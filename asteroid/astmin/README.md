# astmin: the ast prompter at its smallest

A proof of size for `asteroid/AST_CORE.md` ("Rust only for the exe prompter"). No standard library, no libc: Linux system calls only (read, write, exit), x86-64. It prints the `4ST>` prompt, answers each line, and stops on `:quit`. It does not evaluate `.ath` yet.

Measured 2026-11-25: a **2,672-byte** statically linked ELF, no dynamic dependencies. Tested by hand: lines piped together are answered one at a time; `:quit` stops before later lines; a last line without a newline is answered; a line over 256 bytes is refused.

Build (from this folder):

    RUSTFLAGS="-C link-arg=-nostartfiles -C link-arg=-static -C relocation-model=static" cargo build --release

It writes its own `memcpy` and `memmove`, because without libc nothing else provides them.
