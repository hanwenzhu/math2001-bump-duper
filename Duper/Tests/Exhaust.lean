import Duper.Tactic
import Std.Data.Rat.Lemmas

open Lean Elab Tactic in
/-- The `exhaust` tactic proves (true) quantifier-free statements in the language of pure equality.
For example,
```
example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ P) : Q := by exhaust
example {x : Nat} (h1 : x = 0 ∨ x = 1) (h2 : x = 0 ∨ x = 2) : x = 0 := by exhaust
``` -/
elab "exhaust" : tactic => withMainContext do
  evalTactic (← `(tactic| apply Classical.byContradiction _; intro))
  withMainContext do
    let state ← runDuper {} true #[] 0
    match state.result with
    | Duper.ProverM.Result.contradiction => applyProof state
    | Duper.ProverM.Result.saturated =>
      trace[Prover.saturate] "Final Active Set: {state.activeSet.toArray}"
      throwError "Failed, can't rule out other cases"
    | Duper.ProverM.Result.unknown => throwError "Failed, case checking timed out"

-- set_option trace.Preprocessing.debug true
-- set_option trace.Meta.debug true
-- set_option trace.Prover.saturate true
-- set_option trace.Rule.falseElim true
-- set_option inhabitationReasoning false
set_option linter.unusedVariables false

example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ P) : Q := by exhaust

example {X : Type} {x y : X} (h1 : x ≠ y) (h2 : x = y) : False := by exhaust
example {X : Type 1} {x y : X} (h1 : x ≠ y) (h2 : x = y) : False := by exhaust

example (x : Nat) : (x = 5 ∨ x = 2) ∧ (x = 3 ∨ x = 2) ↔ (x = 2) := by exhaust
example {x y : Nat} (h1 : x = 0 ∧ y = 1) : x = 0 ∨ y = 2 := by exhaust
example {x : Int} (hx : x = 1 ∨ (1:Int) = 3) : x = 1 := by exhaust
example (h : (1:Int) = 3) : False := by exhaust
example {x : Nat} (hx1' : x = 1) (hx3' : x = 3) : False := by exhaust
example {x : Nat} (h1 : x = 0 ∨ x = 1) (h2 : x = 0 ∨ x = 2) : x = 0 := by exhaust
example (h : (1:Rat) = 2) : False := by exhaust

example {X : Type} {x1 x2 y1 y2 : X} (hx1 : x1 ≠ x2) (hy1 : y1 ≠ y2) (H : x1 = x2) : False := by
  exhaust

example (x : Nat) :
    (x = 5 ∨ x = 2 ∨ x = 4 ∨ x = 4) ∨ (x = 3 ∨ x = 7 ∨ x = 2)
    ↔ x = 5 ∨ x = 2 ∨ x = 4 ∨ x = 3 ∨ x = 7 := by
  exhaust

example (x : Nat) :
    (¬ (x = 5 ∨ x = 2 ∨ x = 4 ∨ x = 4) ∧ (x = 3 ∨ x = 7 ∨ x = 2)) ↔ (x = 3 ∨ x = 7) := by
  exhaust

example (h : 1 = 3) : False := by
  have : 4 = 4 := rfl
  exhaust

-- ideally this would fail, but the `1 + 1` gets cleaned up to `2` in the `whnf` preprocessing,
-- and that preprocessing seems to be necessary
example (h : 1 = 1 + 1) : False := by exhaust

-- over `Rat` it does fail, so there is an inconsistency in the tactic
example (h : (1:Rat) = 1 + 1) : False := by exhaust

-- want this to succeed, treating the quantified parts as tokens
example {X : Type} (h1 : ∃ x y : X, x ≠ y) (h2 : ¬ ∃ x y : X, x ≠ y) : False := by exhaust

-- want this to fail because of the quantifiers, it succeeds if you run `intros` first
example : ∀ x : Nat, (x = 1 ∧ x = 2) ↔ False := by exhaust

-- want this to fail because of the quantifiers, although it is in scope for vanilla duper
example {X : Type} {s t : X → Prop}
    (hst : ∀ (x1 x2 : X), x1 = x2 ∨ (¬s x1 ∨ ¬t x1) ∨ ¬s x2 ∨ ¬t x2) {x1 x2 y1 y2 : X}
    (hx1 : x1 ≠ x2) (hx2 : s x1) (hx : s x2) (hy1 : y1 ≠ y2) (hy2 : t y1) (hy : t y2) :
    ∃ x1 x2 x3, x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 ∧ (s x1 ∨ t x1) ∧ (s x2 ∨ t x2) ∧
      (s x3 ∨ t x3) := by
  exhaust

-- demonstrate basic failure behaviour (this goal is false!)
example (x : Int) (h : (x = -1 ∨ x = 2 ∨ x = 4 ∨ x = 4) ∨ (x = 3 ∨ x = -2 ∨ x = 2)) :
    x = -1 ∨ x = 2 ∨ x = 4 ∨ x = 3 := by
  exhaust
