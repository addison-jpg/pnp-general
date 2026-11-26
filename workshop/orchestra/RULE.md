# Rule: one lead, four helpers

Status: a working rule, written down. Checked in `rule.ath` only where a count is exact.

## Terms
- **lead**: one Opus agent. It holds the task, reads the result, and reports to the user.
- **helper**: one Haiku agent. It does one bounded sub-task with one output file or one report.
- **round**: one user prompt, handled by one lead and at most four helpers.

## Rule
1. Each round has exactly one lead.
2. Each round has at most four helpers. The default is four, run in parallel, each with one bounded task.
3. A helper does not spawn helpers. Only the lead spawns.
4. Each helper gets one input (a path or a question) and returns one output (a path or a short report).
5. The lead merges the four outputs and checks them before reporting. A check that fails is reported as false, not patched.

## Why four helpers and not one
- A helper's task is small enough to finish in one pass, so a Haiku is enough.
- Four parallel inputs cover the four parts a round usually has: read, build, check, report.
- Fewer helpers leave a part without an owner. More helpers cost more tokens than the work needs.

## Not claimed
- That four is optimal. It is a default, chosen for cost and coverage.
- That the rule speeds up every round. A round with one small fact needs no helper.

## When a helper's result counts
A helper's result counts only when both hold:
1. The result is written as an `.ath` file.
2. `bin/asteroid --no-lean` passes on that file.

A helper's own report does not count, even when it says the check passed. The lead runs `bin/asteroid --no-lean` on the file itself and reads its output.

Worked example: a helper writes `workshop/cluster/hairyball/euler_tetra.ath`, which holds the tetrahedron check (V=4, E=6, F=4, so chi = 4 - 6 + 4 = 2). The lead runs `bin/asteroid --no-lean workshop/cluster/hairyball/euler_tetra.ath`. The output is `claims: 1 true, 0 false` with exit 0, so the result counts. If the check does not pass, the result does not count, and per rule 5 the lead reports it as false.
