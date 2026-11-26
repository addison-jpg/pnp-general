# Note: a novel .ath partition, and the base executable

Status: a requirement and a gap. Nothing here is built.

## Requirement (stated by the user)

1. A new partition (a separate place to pull to) that holds `.ath` only.
2. No other coding language in that partition: no Python, no Lean, no shell as program code.
3. The base executable (`ast`) is the piece that must run it. It is important, so it must not depend on Python to run.

## Current state (checked)

- `ast` (native, Lean-built) exists at `dist/linux/ast` and `dist/windows/ast.exe`. It skips asteroid's newer statements, such as `converse` and `same`, reporting them as "not in the Lean version yet" (`workshop/bigpicture/PARTS.md`, item 5).
- `asteroid` (Python) runs every `.ath` file in the repo, with the converse and sort primitives. It is the reference.
- The repo still contains Python (`asteroid/`, the `.py` checks in the claims), Lean (`lean/`, `one-not/`), and shell scripts. So this partition does not yet exist as "only .ath".
- The Python checks cannot be removed until `ast` runs their statements. Removing them first would drop checks.

## Gap

To meet requirement 2, `ast` must run every statement the Python checker runs, with the same verdicts. That is parity work (item 5), not a file move.

## Not claimed

- That `ast` already runs the full `.ath` language.
- That a partition with only `.ath` is possible today.
