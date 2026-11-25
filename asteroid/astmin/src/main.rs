#![no_std]
#![no_main]
// The ast prompter at its smallest: no libc, no standard library, Linux system calls only.
// It prints the 4ST> prompt, reads a line, and answers `:quit` or echoes the line.
use core::arch::asm;
use core::panic::PanicInfo;

unsafe fn sys3(n: usize, a: usize, b: usize, c: usize) -> isize {
    let r: isize;
    asm!("syscall", inlateout("rax") n as isize => r, in("rdi") a, in("rsi") b, in("rdx") c,
         lateout("rcx") _, lateout("r11") _, options(nostack));
    r
}
fn write(s: &[u8]) { unsafe { sys3(1, 1, s.as_ptr() as usize, s.len()); } }
fn read(buf: &mut [u8]) -> isize { unsafe { sys3(0, 0, buf.as_mut_ptr() as usize, buf.len()) } }
fn exit(code: usize) -> ! { unsafe { sys3(60, code, 0, 0); } loop {} }

#[no_mangle]
pub extern "C" fn _start() -> ! {
    let mut buf = [0u8; 256];
    let mut len = 0usize;
    write(b"4ST> ");
    loop {
        // Answer every complete line already in the buffer, then read more.
        while let Some(i) = buf[..len].iter().position(|&c| c == b'\n') {
            let mut line = [0u8; 256];
            line[..i].copy_from_slice(&buf[..i]);
            buf.copy_within(i + 1..len, 0);
            len -= i + 1;
            let t = &line[..i];
            if t == b":quit" { exit(0); }
            write(b"you said: "); write(t); write(b"\n");
            write(b"4ST> ");
        }
        if len == buf.len() { write(b"line too long\n"); exit(2); }
        let n = read(&mut buf[len..]);
        if n <= 0 {
            // End of input: a last line without a newline is still answered.
            if len > 0 && &buf[..len] != b":quit" { write(b"you said: "); write(&buf[..len]); write(b"\n"); }
            write(b"\n"); exit(0);
        }
        len += n as usize;
    }
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
