# Proposal: put the general NP problem at the front

Status: a plan only. Nothing moves until the owner approves.

## (a) Current layout

- `README.md` opens with asteroid, the language. It says: "The P versus NP question is open. Nothing here settles it."
- The P vs NP work lives in two places.
- `one-not/`: rung 1 of the NOT gate ladder. One NOT gate saves nothing on (1,1)-disjoint Boolean sums. Its own Lake project is `one-not/lean/`.
- `lean/PEqualNP/`: the main Lean project. Folders include `CircuitLowerBounds`, `General`, `Gct`, `MetaComplexity`, `ProofComplexity`, `Worlds`, `Verify`.
- `one-not/DEAD_ENDS.md` lists seven families of dead routes (A to G).

## (b) One front folder: `np/`

- `np/README.md` states the general question in one paragraph.
- It links to `one-not/` and to `lean/PEqualNP/`. It moves neither.
- It says which rung of the ladder each part is.
- It links `DEAD_ENDS.md`, `RESULTS.md` and `NAMES.md`.
- The top `README.md` gets one line pointing to `np/`.

## (c) Checks before any move

- Rerun the asteroid files that back the one-not claims (`theorem.ath`, `ladder.ath`). Record claims true and false.
- Run `cd one-not/lean && lake build`. It must end with exactly one placeholder: `no_minCE` in `W951/MinCE.lean`.
- Run `lake build PEqualNP.Verify.All` (BOARD.md asks for it).
- Build `lean/`. Record the status.
- Lean was not built in this session. `lake` is not installed here.

## (d) Still open

asteroid, asked "what is open about circuit", printed:

    [open] about circuit: 0 open frames, 39 unverified findings, 6 open center nodes, 0 open modules, 0 tag rows labelled open

Asked "what is verified about circuit", it printed:

    [open] 29 verified findings and 28 RESULTS.md rows mention circuit (frames and tags are not counted as verified)
    claims: 0 true, 0 false

The ask lines are questions, not claims. So no claim was checked.

Open, from `one-not/README.md`:

- `no_minCE`: there is no minimal counterexample. It is not proved.
- Circuits that lose the certificate game (hard core `cxT2`).
- The point step for real-witness gates among circuits with no gate-saving rewiring (R6).
- Rungs with more NOT gates. Only small cases are tested.
- P versus NP. Nothing here settles it.

## (e) Three smallest safe steps

1. Add `np/README.md` with links only. Move nothing.
2. Add one line to the top `README.md` that points to `np/`.
3. Run the checks in (c). Write the results into `np/README.md`, with their labels.
