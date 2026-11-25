import Mathlib

/-!
# Methods 1: forced pairs. A cell, its four states, its prover and its refuter

LABEL. Definitions and theorems about the METHOD the project runs on (task
`boards/tasks/methods-formal.md`). Nothing here is about circuits, and nothing bears on P versus NP.

The method. Every open statement (a cell) is given two seats at once: a prover and a refuter. The
cell's state is one of `stillOpen`, `tested`, `refuted`, `checked` (`open` is a Lean keyword, so the
first state is spelled `stillOpen`).

What is a DEFINITION CHOICE here (see `methods/README.md`):
* the five legal moves of `Step` (no move leaves `checked` or `refuted`; `tested` never falls back
  to `stillOpen`);
* `Evidence`: `checked` carries a proof of the statement, `refuted` a proof of its negation,
  `tested` and `stillOpen` carry nothing. This is the board's rule "only Lean gives checked" read
  as logic. It is the reading under which a `checked` cell is true; the board itself only finds a
  theorem name in a file (`Board.lean`).
* the board's words `paper` and `premise` have no state here.

What is CHECKED: `checked` and `refuted` are absorbing; `tested` moves to either; a history has at
most two moves; two cells with equivalent statements are never one `checked` and one `refuted`,
on any two branches; for two different statements both can happen (this is what `Lifting.lean`
uses); a move to `checked` is the prover's and a move to `refuted` is the refuter's.
-/

namespace PEqualNP.Methods.Cells

/-- The state of a cell. -/
inductive Status
  | stillOpen | tested | refuted | checked
  deriving DecidableEq, Repr

/-- Who moves. -/
inductive Role
  | prover | refuter
  deriving DecidableEq, Repr

/-- The legal moves, each with the seat that makes it. A test may be run by either seat. -/
inductive Move : Status → Role → Status → Prop
  | test (r : Role) : Move .stillOpen r .tested
  | proveOpen : Move .stillOpen .prover .checked
  | refuteOpen : Move .stillOpen .refuter .refuted
  | proveTested : Move .tested .prover .checked
  | refuteTested : Move .tested .refuter .refuted

/-- One legal transition. -/
def Step (a b : Status) : Prop := ∃ r, Move a r b

/-- Reachable by legal transitions. -/
def Reach : Status → Status → Prop := Relation.ReflTransGen Step

theorem step_iff {a b : Status} :
    Step a b ↔ (a = .stillOpen ∧ b ≠ .stillOpen) ∨ (a = .tested ∧ (b = .checked ∨ b = .refuted)) := by
  constructor
  · rintro ⟨r, h⟩
    cases h <;> simp
  · rintro (⟨rfl, hb⟩ | ⟨rfl, rfl | rfl⟩)
    · cases b
      · exact absurd rfl hb
      · exact ⟨.prover, .test _⟩
      · exact ⟨_, .refuteOpen⟩
      · exact ⟨_, .proveOpen⟩
    · exact ⟨_, .proveTested⟩
    · exact ⟨_, .refuteTested⟩

instance : DecidableRel Step := fun _ _ => decidable_of_iff _ step_iff.symm

/-- `checked` is absorbing: no move leaves it. -/
theorem checked_absorbing {s : Status} : ¬ Step .checked s := by
  rintro ⟨r, h⟩; cases h

/-- `refuted` is absorbing: no move leaves it. -/
theorem refuted_absorbing {s : Status} : ¬ Step .refuted s := by
  rintro ⟨r, h⟩; cases h

theorem reach_checked {s : Status} : Reach .checked s ↔ s = .checked := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, _⟩
    · exact h.symm
    · exact absurd hc checked_absorbing
  · rintro rfl; exact .refl

theorem reach_refuted {s : Status} : Reach .refuted s ↔ s = .refuted := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, _⟩
    · exact h.symm
    · exact absurd hc refuted_absorbing
  · rintro rfl; exact .refl

/-- Along one history a cell is never first `checked` and later `refuted`, nor the reverse. -/
theorem not_reach_checked_refuted : ¬ Reach .checked .refuted ∧ ¬ Reach .refuted .checked :=
  ⟨fun h => by simpa using reach_checked.1 h, fun h => by simpa using reach_refuted.1 h⟩

/-- `tested` can move to `checked` and to `refuted`. -/
theorem tested_moves : Step .tested .checked ∧ Step .tested .refuted :=
  ⟨⟨_, .proveTested⟩, ⟨_, .refuteTested⟩⟩

/-- `tested` moves nowhere else. -/
theorem tested_step_iff {s : Status} : Step .tested s ↔ s = .checked ∨ s = .refuted := by
  simp [step_iff]

/-- Every state is reachable from `stillOpen`. -/
theorem reach_of_stillOpen (s : Status) : Reach .stillOpen s := by
  cases s
  · exact .refl
  · exact .single ⟨.prover, .test _⟩
  · exact .single ⟨_, .refuteOpen⟩
  · exact .single ⟨_, .proveOpen⟩

/-- The whole reachability relation. -/
theorem reach_iff {a b : Status} :
    Reach a b ↔ a = b ∨ a = .stillOpen ∨ (a = .tested ∧ (b = .checked ∨ b = .refuted)) := by
  constructor
  · intro h
    induction h with
    | refl => exact .inl rfl
    | tail _ hbc ih =>
      rcases step_iff.1 hbc with ⟨rfl, _⟩ | ⟨rfl, hc⟩
      · rcases ih with rfl | rfl | ⟨rfl, h | h⟩
        · exact .inr (.inl rfl)
        · exact .inr (.inl rfl)
        · cases h
        · cases h
      · rcases ih with rfl | rfl | ⟨rfl, h | h⟩
        · exact .inr (.inr ⟨rfl, hc⟩)
        · exact .inr (.inl rfl)
        · cases h
        · cases h
  · rintro (rfl | rfl | ⟨rfl, rfl | rfl⟩)
    · exact .refl
    · exact reach_of_stillOpen _
    · exact .single tested_moves.1
    · exact .single tested_moves.2

instance : DecidableRel Reach := fun _ _ => decidable_of_iff _ reach_iff.symm

/-- A measure that every move raises. -/
def Status.rank : Status → ℕ
  | .stillOpen => 0 | .tested => 1 | .refuted => 2 | .checked => 2

theorem rank_lt_of_step {a b : Status} (h : Step a b) : a.rank < b.rank := by
  obtain ⟨r, h⟩ := h
  cases h <;> decide

/-- A history has at most two moves. -/
theorem no_three_steps {a b c d : Status} : Step a b → Step b c → Step c d → False := by
  intro h1 h2 h3
  have := rank_lt_of_step h1; have := rank_lt_of_step h2; have := rank_lt_of_step h3
  have : d.rank ≤ 2 := by cases d <;> decide
  omega

/-- A move to `checked` is the prover's; a move to `refuted` is the refuter's. -/
theorem move_role {a b : Status} {r : Role} (h : Move a r b) :
    (b = .checked → r = .prover) ∧ (b = .refuted → r = .refuter) := by
  cases h <;> simp

/-! ### Evidence: what a state says about the statement -/

/-- What a state asserts about the statement `P`. DEFINITION CHOICE: `checked` holds a proof,
`refuted` holds a refutation, the other two hold nothing. -/
inductive Evidence (P : Prop) : Status → Prop
  | stillOpen : Evidence P .stillOpen
  | tested : Evidence P .tested
  | checked : P → Evidence P .checked
  | refuted : ¬ P → Evidence P .refuted

theorem evidence_checked {P : Prop} : Evidence P .checked ↔ P :=
  ⟨fun h => by cases h; assumption, .checked⟩

theorem evidence_refuted {P : Prop} : Evidence P .refuted ↔ ¬ P :=
  ⟨fun h => by cases h; assumption, .refuted⟩

/-- A cell: a statement, its forced pair of seats, its state, and the evidence for the state. -/
structure Cell (Seat : Type*) where
  /-- The exact statement. -/
  stmt : Prop
  prover : Seat
  refuter : Seat
  /-- The pair is two seats. -/
  distinct : prover ≠ refuter
  status : Status
  sound : Evidence stmt status

variable {Seat : Type*}

/-- **No cell is both checked and refuted for the same exact statement.** `c₁` and `c₂` are any
two cells (two branches of the work, two seats, two days) whose statements are equivalent. -/
theorem not_checked_and_refuted (c₁ c₂ : Cell Seat) (h : c₁.stmt ↔ c₂.stmt) :
    ¬ (c₁.status = .checked ∧ c₂.status = .refuted) := by
  rintro ⟨h1, h2⟩
  have e1 := c₁.sound; have e2 := c₂.sound
  rw [h1] at e1; rw [h2] at e2
  exact evidence_refuted.1 e2 (h.1 (evidence_checked.1 e1))

/-- The condition "same exact statement" cannot be dropped: two cells with different statements
can be one `checked` and one `refuted`. -/
theorem checked_and_refuted_of_different :
    ∃ c₁ c₂ : Cell Bool, c₁.status = .checked ∧ c₂.status = .refuted :=
  ⟨⟨True, true, false, by decide, .checked, .checked trivial⟩,
    ⟨False, true, false, by decide, .refuted, .refuted id⟩, rfl, rfl⟩

/-- A transition of cells: the statement and the pair stay, the state makes a legal move. -/
structure CellStep (c c' : Cell Seat) : Prop where
  stmt : c.stmt = c'.stmt
  prover : c.prover = c'.prover
  refuter : c.refuter = c'.refuter
  step : Step c.status c'.status

/-- Reachable by transitions of cells. -/
def CellReach : Cell Seat → Cell Seat → Prop := Relation.ReflTransGen CellStep

theorem CellReach.stmt {c c' : Cell Seat} (h : CellReach c c') : c.stmt = c'.stmt := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans h.stmt

theorem CellReach.reach {c c' : Cell Seat} (h : CellReach c c') : Reach c.status c'.status := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail h.step

/-- **Branches agree.** From one cell, no two histories end one in `checked` and one in
`refuted`. The state machine alone allows both branches; the evidence forbids one of them. -/
theorem branches_agree {c c₁ c₂ : Cell Seat} (h₁ : CellReach c c₁) (h₂ : CellReach c c₂) :
    ¬ (c₁.status = .checked ∧ c₂.status = .refuted) :=
  not_checked_and_refuted c₁ c₂ (by rw [← h₁.stmt, ← h₂.stmt])

/-- A `checked` cell stays `checked`, and a `refuted` cell stays `refuted`. -/
theorem CellReach.absorbing {c c' : Cell Seat} (h : CellReach c c') :
    (c.status = .checked → c'.status = .checked) ∧ (c.status = .refuted → c'.status = .refuted) :=
  ⟨fun hc => reach_checked.1 (hc ▸ h.reach), fun hc => reach_refuted.1 (hc ▸ h.reach)⟩

/-- **The pair covers the cell** (classical logic): every cell that is not closed has a legal
transition to a closed cell, made by the prover if the statement is true and by the refuter if it
is false. Nothing is said about finding the proof. -/
theorem pair_covers (c : Cell Seat) (h : c.status = .stillOpen ∨ c.status = .tested) :
    ∃ c' : Cell Seat, CellStep c c' ∧
      ((c.stmt ∧ c'.status = .checked ∧ Move c.status .prover .checked) ∨
        (¬ c.stmt ∧ c'.status = .refuted ∧ Move c.status .refuter .refuted)) := by
  by_cases hP : c.stmt
  · refine ⟨⟨c.stmt, c.prover, c.refuter, c.distinct, .checked, .checked hP⟩, ⟨rfl, rfl, rfl, ?_⟩,
      .inl ⟨hP, rfl, ?_⟩⟩
    · rcases h with h | h <;> rw [h] <;> exact ⟨_, by constructor⟩
    · rcases h with h | h <;> rw [h] <;> constructor
  · refine ⟨⟨c.stmt, c.prover, c.refuter, c.distinct, .refuted, .refuted hP⟩, ⟨rfl, rfl, rfl, ?_⟩,
      .inr ⟨hP, rfl, ?_⟩⟩
    · rcases h with h | h <;> rw [h] <;> exact ⟨_, by constructor⟩
    · rcases h with h | h <;> rw [h] <;> constructor

end PEqualNP.Methods.Cells
