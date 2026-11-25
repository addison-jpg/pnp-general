#![no_std]
#![no_main]
// The ast prompter at its smallest: no libc, no standard library, Linux x86-64 system calls only
// (read, write, openat, getdents64, close, exit). It prints the 4ST> prompt and answers each line:
//   :memory     count the centre store's records (center/shards/*.jsonl) by (kind, word)
//   :find WORD  count the records whose line contains WORD; show the first 3 ids and programs
//   :quit       stop
// Any other `:` line is an unknown command; any other line is echoed. The store is read under the
// current directory, or under the folder given as the first argument. Fixed buffers, no allocator.
use core::arch::{asm, global_asm};
use core::panic::PanicInfo;

const LINE: usize = 16384; // longest record read, in bytes without its newline; a longer one is counted as skipped
const FILES: usize = 256; // most shard files
const PAIRS: usize = 1024; // most distinct (kind, word) pairs
const TEXT: usize = 65536; // bytes of (kind, word) text the pair table holds
const DIR: usize = 0o200000; // O_DIRECTORY

unsafe fn sys(n: usize, a: usize, b: usize, c: usize) -> isize {
    // openat's fourth argument (mode) is left unset: the kernel ignores it unless a file is created.
    let r: isize;
    asm!("syscall", inlateout("rax") n as isize => r, in("rdi") a, in("rsi") b, in("rdx") c,
         lateout("rcx") _, lateout("r11") _, options(nostack));
    r
}
fn write(s: &[u8]) { unsafe { sys(1, 1, s.as_ptr() as usize, s.len()); } }
fn read(fd: isize, buf: &mut [u8]) -> isize { unsafe { sys(0, fd as usize, buf.as_mut_ptr() as usize, buf.len()) } }
fn openat(dir: isize, path: *const u8, flags: usize) -> isize { unsafe { sys(257, dir as usize, path as usize, flags) } }
fn close(fd: isize) { unsafe { sys(3, fd as usize, 0, 0); } }
fn exit(code: usize) -> ! { unsafe { sys(60, code, 0, 0); } loop {} }

#[derive(Clone, Copy)]
struct Pair { off: usize, len: usize, n: usize }
struct Tally {
    files: usize, total: usize, skipped: usize, found: usize, np: usize, nt: usize, full: bool,
    pairs: [Pair; PAIRS], // kept in key order, which is (kind, word) order because the zero byte sorts first
    text: [u8; TEXT], // the pairs' keys: kind, a zero byte, word (json.dumps never writes a raw zero byte)
    key: [u8; LINE + 2],
}
struct St {
    t: Tally,
    io: [u8; 65536], // directory entries, then file contents
    line: [u8; LINE],
    names: [[u8; 256]; FILES], // zero-terminated; a Linux file name is at most 255 bytes
    order: [u8; FILES], // name indices in byte order of name, as Python's sorted(glob(...))
}
// All zero, so it lives in .bss: the kernel provides it, the file does not carry it.
static mut ST: St = unsafe { core::mem::zeroed() };

// The kernel starts a process with argc, then the argv pointers, at the stack pointer.
global_asm!(".globl _start", "_start:", "mov rdi, rsp", "call start");

#[no_mangle]
unsafe extern "C" fn start(sp: *const usize) -> ! {
    let r = if *sp > 1 { *sp.add(2) as *const u8 } else { b".\0".as_ptr() };
    let mut n = 0; // the length of the C string, counted with volatile reads so it is not turned into strlen
    while core::ptr::read_volatile(r.add(n)) != 0 { n += 1; }
    let root = core::slice::from_raw_parts(r, n + 1); // the folder name with its zero byte
    let st = &mut *core::ptr::addr_of_mut!(ST);
    let mut buf = [0u8; 256];
    let mut len = 0usize;
    write(b"4ST> ");
    loop {
        // Answer every complete line already in the buffer, then read more.
        while let Some(i) = pos(&buf[..len], b'\n') {
            if answer(st, root, &buf[..i]) { exit(0); }
            buf.copy_within(i + 1..len, 0);
            len -= i + 1;
            write(b"4ST> ");
        }
        if len == buf.len() { write(b"line too long\n"); exit(2); }
        let n = read(0, &mut buf[len..]);
        if n <= 0 {
            // End of input: a last line without a newline is still answered.
            if len > 0 { answer(st, root, &buf[..len]); }
            write(b"\n"); exit(0);
        }
        len += n as usize;
    }
}

// True for `:quit`.
fn answer(st: &mut St, root: &[u8], t: &[u8]) -> bool {
    if t == b":quit" { return true; }
    if t == b":memory" {
        if scan(st, root, b"") { memory(&st.t, root); }
    } else if t.len() > 6 && starts(t, b":find ") {
        if scan(st, root, &t[6..]) {
            write(b"records containing \""); write(&t[6..]); write(b"\": "); num(st.t.found, 0); write(b"\n");
            summary(&st.t, root);
        }
    } else if starts(t, b":") {
        write(b"unknown command\ncommands: :memory  :find WORD  :quit\n");
    } else {
        write(b"you said: "); write(t); write(b"\n");
    }
    false
}

fn memory(t: &Tally, root: &[u8]) {
    if t.full { write(b"refused: more than 1024 distinct (kind, word) pairs, or 65536 bytes of their text\n"); return; }
    summary(t, root);
    for i in 0..t.np {
        let k = key(t, i);
        let z = pos(k, 0).unwrap_or(0);
        num(t.pairs[i].n, 6); write(b" "); write(&k[..z]); write(b" "); write(&k[z + 1..]); write(b"\n");
    }
    write(b"recorded words, not verification: these count what the store says; nothing was re-checked\n");
}
fn key(t: &Tally, i: usize) -> &[u8] { let p = t.pairs[i]; &t.text[p.off..p.off + p.len] }

fn summary(t: &Tally, root: &[u8]) {
    write(cstr(root)); write(b"/center/shards: "); num(t.files, 0); write(b" shard files, "); num(t.total, 0);
    write(b" records, "); num(t.skipped, 0); write(b" skipped (too long)\n");
}

// Reads ROOT/center/shards/*.jsonl in byte order of name and hands each line to `record`.
// False, after saying why, if the folder cannot be read or holds more than FILES shard files.
fn scan(st: &mut St, root: &[u8], needle: &[u8]) -> bool {
    let t = &mut st.t;
    t.files = 0; t.total = 0; t.skipped = 0; t.found = 0; t.np = 0; t.nt = 0; t.full = false;
    let r = openat(-100, root.as_ptr(), DIR); // -100: AT_FDCWD
    let d = if r < 0 { r } else { let d = openat(r, b"center/shards\0".as_ptr(), DIR); close(r); d };
    // List the names that glob's *.jsonl matches (it skips names that start with a dot).
    let mut n = 0;
    loop {
        let got = if d < 0 { d } else { unsafe { sys(217, d as usize, st.io.as_mut_ptr() as usize, st.io.len()) } }; // getdents64
        if got < 0 { close(d); write(b"cannot read "); write(cstr(root)); write(b"/center/shards\n"); return false; }
        if got == 0 { break; }
        let mut o = 0;
        while o < got as usize {
            // struct linux_dirent64: inode (8 bytes), offset (8), record length (2), type (1), name
            let e = &st.io[o..];
            let name = cstr(&e[19..]);
            let l = name.len();
            if l > 6 && name[0] != b'.' && starts(&name[l - 6..], b".jsonl") {
                if n == FILES { close(d); write(b"refused: more than 256 shard files\n"); return false; }
                st.names[n][..=l].copy_from_slice(&e[19..20 + l]); // with its zero byte
                let mut j = n; // insert, keeping `order` sorted
                while j > 0 && lt(&st.names[n], &st.names[st.order[j - 1] as usize]) { st.order[j] = st.order[j - 1]; j -= 1; }
                st.order[j] = n as u8;
                n += 1;
            }
            o += e[16] as usize | (e[17] as usize) << 8;
        }
    }
    for k in 0..n {
        let name = &st.names[st.order[k] as usize];
        let f = openat(d, name.as_ptr(), 0);
        if f >= 0 && lines(&mut st.t, &mut st.io, &mut st.line, f, needle) { st.t.files += 1; }
        else { write(b"cannot read "); write(cstr(name)); write(b"\n"); }
        close(f);
    }
    close(d);
    true
}

// One record per line. A line longer than LINE bytes is counted as skipped, never parsed in part.
fn lines(t: &mut Tally, io: &mut [u8], line: &mut [u8; LINE], f: isize, needle: &[u8]) -> bool {
    let (mut len, mut long) = (0, false);
    loop {
        let r = read(f, io);
        if r < 0 { return false; }
        for &c in &io[..r as usize] {
            if c == b'\n' { record(t, &line[..len], long, needle); len = 0; long = false; }
            else if len < LINE { line[len] = c; len += 1; }
            else { long = true; }
        }
        if r == 0 { record(t, &line[..len], long, needle); return true; } // a last line with no newline
    }
}

fn record(t: &mut Tally, l: &[u8], long: bool, needle: &[u8]) {
    if long { t.skipped += 1; return; }
    if l.is_empty() { return; }
    t.total += 1;
    if needle.is_empty() {
        let mut kl = 0;
        for part in [field(l, b"\"kind\": \""), b"\0", field(l, b"\"word\": \"")] {
            for &c in part { t.key[kl] = c; kl += 1; }
        }
        let new = &t.key[..kl];
        let mut i = 0; // the pair's place in key order
        while i < t.np && lt(key(t, i), new) { i += 1; }
        if i < t.np && eq(key(t, i), new) { t.pairs[i].n += 1; return; }
        if t.np == PAIRS || t.nt + kl > TEXT { t.full = true; return; }
        t.text[t.nt..t.nt + kl].copy_from_slice(new);
        t.pairs.copy_within(i..t.np, i + 1);
        t.pairs[i] = Pair { off: t.nt, len: kl, n: 1 };
        t.np += 1;
        t.nt += kl;
    } else if at(l, needle).is_some() {
        t.found += 1;
        if t.found <= 3 {
            write(b"  id "); write(field(l, b"\"id\": \"")); write(b"  program "); write(field(l, b"\"program\": \"")); write(b"\n");
        }
    }
}

// The value after the first `"NAME": "` in a line, up to the next quote; `-` if there is none.
fn field<'a>(l: &'a [u8], pat: &[u8]) -> &'a [u8] {
    if let Some(i) = at(l, pat) {
        let v = &l[i + pat.len()..];
        if let Some(j) = pos(v, b'"') { return &v[..j]; }
    }
    b"-"
}

fn pos(s: &[u8], c: u8) -> Option<usize> { s.iter().position(|&x| x == c) }
fn cstr(s: &[u8]) -> &[u8] { &s[..pos(s, 0).unwrap_or(s.len())] }
fn starts(h: &[u8], p: &[u8]) -> bool { h.len() >= p.len() && p.iter().zip(h).all(|(a, b)| a == b) }
fn eq(a: &[u8], b: &[u8]) -> bool { a.len() == b.len() && starts(a, b) }
fn at(h: &[u8], p: &[u8]) -> Option<usize> { (0..h.len()).find(|&i| starts(&h[i..], p)) }
fn lt(a: &[u8], b: &[u8]) -> bool {
    match a.iter().zip(b).find(|(x, y)| x != y) { Some((x, y)) => x < y, None => a.len() < b.len() }
}
fn num(mut n: usize, width: usize) {
    let mut b = [b' '; 24];
    let mut i = 24;
    loop { i -= 1; b[i] = b'0' + (n % 10) as u8; n /= 10; if n == 0 { break; } }
    write(&b[i.min(24 - width)..]);
}

#[panic_handler]
fn panic(_: &PanicInfo) -> ! { exit(101) }

// No libc: the two memory routines the compiler calls for slice copies. Volatile byte loops,
// so the optimiser cannot turn them back into calls to themselves.
#[no_mangle]
pub unsafe extern "C" fn memcpy(d: *mut u8, s: *const u8, n: usize) -> *mut u8 {
    let mut i = 0;
    while i < n { core::ptr::write_volatile(d.add(i), core::ptr::read_volatile(s.add(i))); i += 1; }
    d
}
#[no_mangle]
pub unsafe extern "C" fn memmove(d: *mut u8, s: *const u8, n: usize) -> *mut u8 {
    if (d as usize) <= (s as usize) {
        let mut i = 0;
        while i < n { core::ptr::write_volatile(d.add(i), core::ptr::read_volatile(s.add(i))); i += 1; }
    } else {
        let mut i = n;
        while i > 0 { i -= 1; core::ptr::write_volatile(d.add(i), core::ptr::read_volatile(s.add(i))); }
    }
    d
}
