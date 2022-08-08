import Duper.ProverM
import Duper.RuleM
import Duper.MClause
import Duper.Util.Iterate

namespace Duper
open RuleM
open ProverM

inductive SimpResult (α : Type)
| Applied (c : α) : SimpResult α
| Unapplicable : SimpResult α
| Removed : SimpResult α

namespace SimpResult

def mapM [Monad m] (f : α → m β) : SimpResult α → m (SimpResult β)
| Applied c    => return Applied (← f c)
| Unapplicable => return Unapplicable
| Removed      => return Removed

def forM {m : Type u → Type v} [Monad m] {α : Type} (r : SimpResult α) (f : α → m PUnit) : m PUnit :=
match r with
| Applied c    => f c
| Unapplicable => return PUnit.unit
| Removed      => return PUnit.unit

end SimpResult

inductive BackwardSimpResult
| Removed (removedClauses : List MClause) : BackwardSimpResult
| Applied (transformedClauses : List (MClause × (MClause × Option ProofReconstructor))) : BackwardSimpResult
| Unapplicable : BackwardSimpResult

open SimpResult

abbrev MSimpRule := MClause → RuleM (SimpResult (List (MClause × Option ProofReconstructor)))
abbrev SimpRule := Clause → ProverM (SimpResult Clause)

abbrev BackwardMSimpRule := MClause → RuleM BackwardSimpResult
abbrev BackwardSimpRule := Clause → ProverM Bool -- Returns true iff any backward simplification was done (meaning backwardSimpLoop needs to loop)

def MSimpRule.toSimpRule (rule : MSimpRule) (ruleName : String) : SimpRule := fun givenClause => do
  -- Run the rule
  let (res, cs) ← runSimpRule do
    withoutModifyingMCtx do
      let mclause ← loadClause givenClause
      let cs? ← rule mclause
      cs?.forM fun cs => do
        for (c, mkProof) in cs do yieldClause c ruleName mkProof
      return cs?
  match res with
  | SimpResult.Removed => return Removed
  | Unapplicable => return Unapplicable
  | SimpResult.Applied [] => return Removed
  | SimpResult.Applied _ => do
    -- Return first clause, add others to passive set
    for i in [:cs.size] do
      let (c, proof) := cs[i]
      if i == 0 then
        let _ ← addNewClause c proof
      else
        addNewToPassive c proof
    return Applied cs[0].1

def BackwardMSimpRule.toBackwardSimpRule (rule : BackwardMSimpRule) (ruleName : String) : BackwardSimpRule :=
  fun givenClause => do
  let (res, cs) ← runSimpRule do
    withoutModifyingMCtx do
      let mclause ← loadClause givenClause
      match ← rule mclause with
      | BackwardSimpResult.Removed removedClauses =>
        let mut clausesToRemove : List Clause := []
        for c in removedClauses do
          clausesToRemove := (← neutralizeMClause c) :: clausesToRemove
        return clausesToRemove
      | BackwardSimpResult.Applied transformedClauses =>
        let mut clausesToRemove : List Clause := []
        for (oldClause, c, mkProof) in transformedClauses do
          yieldClause c ruleName mkProof
          clausesToRemove := (← neutralizeMClause oldClause) :: clausesToRemove
        return clausesToRemove
      | BackwardSimpResult.Unapplicable => return []
  for c in res do removeClause c -- Remove every clause in BackwardSimpResult.Removed and every old clause in BackwardSimpResult.Applied
  for (c, proof) in cs do addNewToPassive c proof -- Add each yielded clause to the passive set
  return not res.isEmpty -- If res is nonempty, then some simplification was performed, so return true. Otherwise, return false

end Duper
