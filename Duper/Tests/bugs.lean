import Duper.TPTP
import Duper.Tactic

-- Bug 1
namespace Color2

inductive Color :=
| red : Color
| green : Color

example : @Color.rec (fun _ => Nat) a b .red = a := by duper [Color.rec]

def test : Color → Color
| .red => .green
| .green => .red

set_option pp.match false
#print test
#print test.match_1
#print Color.casesOn

set_option inhabitationReasoning false in
set_option trace.Saturate.debug true in
set_option trace.Timeout.debug true in
example : ∃ c : Color, test c = .green := by
  duper [test, test.match_1, Color.rec, Color.casesOn]

-- This bug demonstrates the difficulty Duper has dealing with inductive arguments and facts such as Color.rec

end Color2

-- Bug 5
set_option inhabitationReasoning true in
set_option trace.typeInhabitationReasoning.debug true in
tptp ITP023_3 "../TPTP-v8.0.0/Problems/ITP/ITP023_3.p"
  by duper [*] -- Fails due to error: unknown free variable '_uniq.6173142'

set_option inhabitationReasoning false in
tptp ITP023_3' "../TPTP-v8.0.0/Problems/ITP/ITP023_3.p"
  by duper [*] -- Det timeout

-- Diagnosis of the above test
/-
The error appears to occur during removeVanishedVarsHelper (which is only called when inhabitationReasoning is enabled).
Specifically, when the clause `∀ (a : Type) (a_1 a_2 : a), _uniq.6179254 → p c_2Ebool_2ET_2E0 = True ∨ a_1 = a_2` is
processed, an mvar `?m.6184382` is given the type `_uniq.6179254`. When `Meta.findInstance` is called on `?m.6184382`'s
type (`_uniq.6179254`), the error "unknown free variable '_uniq.6173142'" is produced.

To further diagnose this bug, the thing to do would be to attempt to trace how the above clause was produced (and therefore,
where the `_uniq.6179254` constraint was imposed).

I'm relegating this to low priority both because it's really hard to debug (ITP023_3 is really long) and because auto's preprocessing
appears to sidestep the issue.

Update: After inhabitation reasoning was improved, duper was able to infer the Nonempty status of enough types that this bug is now also
visible in the following example (originally from test_inhabitationReasoning.lean):

example : ((∃ (A B : Type) (f : B → A) (x : B), f x = f x) = True) :=
  by duper

This might be a more viable example to investigate because of how much shorter it is
-/

-- Bug 7
example (a : α) (as : List α) : [] ≠ a :: as :=
  by duper [List.rec] -- Error: AppBuilder for 'mkAppOptM', result contains metavariables @List.nil

-- Diagnosis of the above example
/-
This error arises during `addRecAsFact` in Tactic.lean on the line that calls `let ctor ← mkAppOptM ctorName #[]`.
Fundamentally, the issue is that `List` is polymorphic and the current `addRecAsFact` doesn't support that.
-/

-- Bug 8: Application type mismatch pertaining to the universe levels of skolems
axiom f.{u} : Type u → Prop

axiom ftrue.{u} : f.{u} (Sort u)

axiom exftrue.{u} : ∃ (x : Type u), f x

def test : ∃ x : Type u, ∃ y : Type v, f x = f y := by
  duper [exftrue]
/-
application type mismatch
  skol.0 [anonymous]
argument has type
  Type u_1
but function has type
  Type u_2 → Type u_2
-/

-- Bug 8
set_option trace.Saturate.debug true in
example (h1 : ∀ x : Nat, x > 0 → ∃ y : Fin x, y.1 = 0) (h2 : 3 > 0) : ∃ z : Fin 3, z.1 = 0 := by
  duper [h1, h2]

/-
The final active set contains both of the following clauses:
- ∀ (a : Fin 3), a.1 ≠ 0
- ∀ (a : Fin 3), (skS.0 Type 0 ((x_0 : Nat) → Fin x_0 → Fin x_0) 3 a).1 = 0

If it were possible to unify `a` from the first clause with `(skS.0 Type 0 ((x_0 : Nat) → Fin x_0 → Fin x_0) 3 a)` from
the second clause, then duper would be able to derive a contradiction. However, the current manner in which skolem symbols
are constructed prevents this.
-/
