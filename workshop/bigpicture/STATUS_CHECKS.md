# Status checks, 2026-11-25

Read-only check of six source files. Figures are quoted as each file gives them. Asteroid and Lean were not run.

## 1. Sources

| Source file | Claimed status | Exact figure quoted | Label as the file gives it |
|---|---|---|---|
| /home/user/pnp-general/BOARD.md (STATUS 2026-11-25 evening) | Checked and committed | "Glottolog forest, 13,122 nodes and 428 roots" | "Checked and committed (exact)" |
| /home/user/pnp-general/BOARD.md (STATUS 2026-11-25 evening) | Negative result | "the discrete evaporation rule gives exponent 0, not 3" | "Negative results, kept as found" |
| /home/user/pnp-general/BOARD.md (TOP NOW, line 7) | Done | "4.4 MB Linux binary"; "4.2 MB native asteroid.exe" | "Done" |
| /home/user/pnp-general/BOARD.md (CURRENT STATE, asteroid) | Built binaries | "dist/linux/ast 4.3 MB"; "dist/windows/ast.exe 4.2 MB"; "dist/linux/asteroid 45 MB" | none given |
| /home/user/pnp-general/BOARD.md (CURRENT STATE, one-NOT) | Open | "0 failures at about 1.27 million DD states" | "Open: BottomPay"; "no_minCE is NOT proved" |
| /home/user/pnp-general/RESULTS.md (totals, line 28) | Verified findings | "all: 91 checked, 32 checked-finite, 12 tested, 6 refuted" | "checked", "checked-finite", "tested", "refuted" |
| /home/user/pnp-general/README.md (What is proved) | Proved | no figure | "Checked-finite results exist for many small exact facts" |
| /home/user/pnp-general/README.md (What is open) | Open | "The Windows binary. base is Linux only."; "47 MB" bundle | "open" (list items) |
| /home/user/pnp-general/workshop/mobius/PROOF_STATUS.md (Runs) | Proved | "checks/twist.ath 10 true, 0 false"; "pipeline.ath 5 true, 5 false"; "pipeline_val.ath 6 true, 0 false" | "Proved (checked-finite)"; "Open" (C1) |
| /home/user/pnp-general/workshop/bus/README.md (Laws; Status) | Laws checked in code; status says nothing checked | "L1 to L4" | "checked in code"; "nothing here is checked" |
| /home/user/pnp-general/workshop/gnn_plan/PLAN.md (Status; section 2; steps) | Plan | "Status: a plan"; step 4.1 "not started"; step 4.2 "partial" | "Bus: ... L1, L3, L4 checked on one slice" |

Row sums in RESULTS.md match its totals: checked 48+13+13+9+7+1 = 91; checked-finite 32; tested 12; refuted 6. The asteroid detail table was read only to line 40, so its rows were not checked in full.

## 2. Disagreements

1. **Bus laws L3 and L4.** bus/README.md says L1 to L4 are "checked in code" but its status says "nothing here is checked". gnn_plan/PLAN.md says "L1, L3, L4 checked on one slice". mobius/PROOF_STATUS.md says L3 and L4 "remain open in workshop/bus/laws.ath". README.md says they "are not checkable in asteroid yet".
2. **Windows binary.** BOARD.md (TOP NOW) says native asteroid.exe is "Done" at 4.2 MB. README.md says "The Windows binary" is open and "base is Linux only".
3. **Full asteroid bundle size.** README.md says "47 MB". BOARD.md (CURRENT STATE) says "dist/linux/asteroid 45 MB".
4. **Linux native binary size.** BOARD.md (TOP NOW) says "4.4 MB". BOARD.md (CURRENT STATE) says "dist/linux/ast 4.3 MB".
5. **Windows binary name.** BOARD.md (TOP NOW) says "asteroid.exe" at 4.2 MB. BOARD.md (CURRENT STATE) says "dist/windows/ast.exe" at 4.2 MB. The board's task table says it was renamed from asteroid.exe to ast.exe.

Disagreements found: 5.

## 3. Not checked

- Asteroid and Lean were not run. No `.ath` file, Lean build, or `results.py` was run.
- Evidence paths named in RESULTS.md were not opened to confirm they exist.
- mobius/PROOF_STATUS.md has no row in RESULTS.md, so its checked-finite claims are not in the verified totals.
- Only the requested sections were read. Figures outside them were not compared.
