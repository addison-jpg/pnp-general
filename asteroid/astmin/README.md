# astmin: the ast prompter at its smallest

A proof of size for `asteroid/AST_CORE.md` ("Rust only for the exe prompter"). No standard library, no libc: Linux system calls only (read, write, openat, getdents64, close, exit), x86-64. It prints the `4ST>` prompt, answers each line, and stops on `:quit`. It does not evaluate `.ath` yet.

Since 2026-11-25 it reads the centre store itself (Addison: "the memory link is kind of a memory hole"): `center/shards/*.jsonl`, written by `center.py`, one JSON record per line.

## Commands

    astmin [ROOT]        # the store is ROOT/center/shards; ROOT defaults to the current directory

| line | answer |
|---|---|
| `:memory` | reads every `ROOT/center/shards/*.jsonl` and prints: the shard-file count, the record count and the "skipped (too long)" count; then, for each (kind, word) pair, the number of records, in byte order of (kind, word), with `-` for a record that has no word; then one line saying these are recorded words, not verification |
| `:find WORD` | the first 3 records whose line contains WORD (the rest of the line after `:find `, compared as plain bytes, case-sensitive), shown by their `id` and `program`; then how many records contain it, and the same counts line |
| `:quit` | stops |
| any other `:` line | `unknown command` and the list of commands |
| any other line | echoed, as before |

Files are read in byte order of name (Python's `sorted(glob(...))`; like glob, names that start with a dot are skipped), lines in file order, so "first 3" is well defined. ROOT comes from argv, read off the initial stack: `_start` is two lines of assembly that hand the stack pointer to Rust. Measured 2026-11-25 on the repository's store:

    4ST> :memory
    ./center/shards: 31 shard files, 562 records, 0 skipped (too long)
       109 cell -
       100 finding checked
        56 finding checked-finite
        21 finding open
         5 finding paper
        13 finding refuted
        51 finding tested
        49 fingerprint -
        90 frame checked-finite
        57 frame open
         3 frame tested
         7 level open
         1 level tested
    recorded words, not verification: these count what the store says; nothing was re-checked
    4ST> :find "word": "refuted"
      id 0bdbbe36  program circuits
      id 4a5ffb32  program circuits
      id 50aa0de4  program circuits
    records containing ""word": "refuted"": 13
    ./center/shards: 31 shard files, 562 records, 0 skipped (too long)

WORD may hold quotes and spaces: the 13 lines holding `"word": "refuted"` are the 13 `finding refuted` records above. The words are what the store records. `:memory` checks none of them; a `checked` here is only a count of records that say `checked`.

## Limits (fixed buffers, no allocator)

| limit | value | past it |
|---|---|---|
| record length | 16,384 bytes, newline excluded (the longest record today is 1,616) | the record is counted in "skipped (too long)", never parsed in part and never dropped silently |
| shard files | 256 | `:memory` and `:find` refuse and print nothing else |
| distinct (kind, word) pairs | 1,024, holding at most 65,536 bytes of kind and word text | `:memory` refuses and prints nothing else |
| prompt line | 256 bytes | `line too long`, exit 2 (as before) |

A shard file that cannot be opened or read is named in a `cannot read` line and left out of the file count (records read before a read error stay counted); a store folder that cannot be read gets `cannot read ROOT/center/shards` and nothing else. All the buffers are zeroed statics in `.bss`: 254,264 bytes of memory at run time, none of them in the file.

## How `kind` and `word` are read

No JSON library. In each line, `kind` is the bytes after the first `"kind": "` up to the next `"`, and `word` likewise after `"word": "`; either one missing reads as `-`. `:find` reads `id` and `program` the same way.

Why this is exact for `center.py`'s output: it writes each record as `json.dumps(r, ensure_ascii=False, sort_keys=True)` on one line.

1. **Fixed separators.** Without `indent`, json.dumps puts `": "` between a key and its value, so a key `kind` with a string value is always the bytes `"kind": "`.
2. **No false match inside text.** Inside a string, json.dumps writes every `"` as `\"`. So in the pattern, the quote after `kind` (preceded by `d`, not by a backslash) is a real closing quote, and `: ` after it makes the string a key. A text field that quotes `"kind": "x"` is stored as `\"kind\": \"x\"` and does not match.
3. **The value ends at the first quote** when it holds nothing json.dumps escapes (`"`, `\`, control characters). With `ensure_ascii=False`, non-ASCII is stored as raw UTF-8, the same bytes Python's `.encode()` gives, and UTF-8 byte order is code-point order, so the sort agrees with Python's.
4. **The first match is the record's own key.** That holds if no nested object holding a `kind` or `word` key comes first. Because keys are sorted, one could come first only under a top-level key that sorts earlier (`by`, `claim`, `evidence`, `id`, ... for `kind`; almost every key for `word`). Today the only nested objects are the `retests` entries (`ok`, `seconds`, `speedup`, `states`, `time`), in 2 of the 562 records.

When it would not be exact: records written with other separators or with `indent` (no match, so every record reads as `-`); a kind or word that json.dumps escapes (a quote, a backslash, a control character; and every non-ASCII character if `ensure_ascii` were left at True); a nested object with a `kind` or `word` key placed before the record's own, or anywhere in a record that has no word of its own; a kind or word that is not a string (`null` or a number reads as `-`). Each of these is a change to `center.py`'s output, and the differential test below would show it.

## Differential test

`memory_diff.py` (standard library only) reads every shard with `json`, computes the same counts, `:find` matches and ids, and builds the whole transcript the binary must print. It then pipes `:memory` and four or five `:find` lines into the binary and compares the output byte for byte. It exits 1 on any difference. It runs three stores:

- the repository's, with ROOT as an argument;
- the same, from the current directory with no argument;
- a made-up store written with `center.py`'s own `json.dumps` call, holding the edge cases: a record of exactly 16,384 bytes and one of 16,385, an empty line, a last line with no newline, a hidden `.jsonl`, a `.txt`, a non-ASCII word and a record with no word.

```
$ python3 -I asteroid/astmin/memory_diff.py
store, root as argument: 31 shard files, 562 records, 0 skipped (too long), 13 (kind, word) pairs, 5 :find words: equal (1491 bytes, exit 0)
store, current directory: 31 shard files, 562 records, 0 skipped (too long), 13 (kind, word) pairs, 5 :find words: equal (1365 bytes, exit 0)
made-up store (edge cases): 2 shard files, 4 records, 1 skipped (too long), 3 (kind, word) pairs, 4 :find words: equal (797 bytes, exit 0)
ok: astmin's output equals the json reference, byte for byte
```

The test can fail. Checked once by hand (2026-11-25, scratch script, not kept): eight one-line breakages of `main.rs` each made it exit 1. They were the line limit one byte short, hidden files read, files read in directory order, pairs not kept in order, a missing field shown as `?`, a last line with no newline dropped, a long line also counted as a record, and four matches shown instead of three. Four of the eight were caught only by the made-up store. The old 2,672-byte binary fails it too. Also by hand: 257 shard files and 1,025 pairs are refused, while 256 and 1,024 are read; a directory named `x.jsonl` is reported as `cannot read x.jsonl`; strace shows only read, write, openat, getdents64 and close (and exit). The old hand tests still hold: lines piped together are answered one at a time; `:quit` stops before later lines; a last line without a newline is answered; a prompt line over 256 bytes is refused.

## Size

Measured 2026-11-25 with the build line below, stripped, statically linked, no dynamic dependencies:

| | bytes |
|---|---|
| before (prompt and echo only) | 2,672 |
| after (with `:memory` and `:find`) | **7,704** |

Of the 7,704 bytes, 3,993 are code and 1,616 are unwind tables (`.eh_frame` and its header), which fat LTO keeps even with `panic = "abort"` and `-C force-unwind-tables=no`. A two-line linker script that discards them (with `-Wl,--no-eh-frame-hdr`) gives 5,888 bytes (1,992 for the old program). It is not adopted, so that the build line stays the same and the two sizes compare. `:memory` on the 386 KB store takes about 2 ms, process start included.

## Build

From this folder:

    RUSTFLAGS="-C link-arg=-nostartfiles -C link-arg=-static -C relocation-model=static" cargo build --release

It writes its own `memcpy` and `memmove`, because without libc nothing else provides them. Rust links with `-nodefaultlibs`, so any other libc routine the compiler reached for (it tried `strlen` once) fails the link instead of slipping in.
