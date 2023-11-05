import Duper.Simp
import Duper.Util.ProofReconstruction
import Lean.Meta.Basic

namespace Duper
open RuleM
open SimpResult
open Lean
open Meta

initialize registerTraceClass `Rule.falseElim

/-- Determines whether a literal is of the form `a = b`, for decidably non-equal expressions `a`
and `b`. -/
def isDecidablyFalseLiteral (lit : Lit) : MetaM Bool := do
  try
    let d ← mkDecide lit.toExpr
    let d ← instantiateMVars d
    let r ← withDefault <| whnf d
    return r.isConstOf ``false
  catch _ => return false

theorem false_ne_true (h : False = True) : False := by rw [h]; exact ⟨⟩
theorem true_ne_false (h : True = False) : False := by rw [← h]; exact ⟨⟩

def mkFalseElimProof (i : Nat) (premises : List Expr) (parents : List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let mut caseProofs := Array.mkEmpty parentLits.size
    for j in [:parentLits.size] do
      let lit := parentLits[j]!
      if i == j then
        -- this is adapted from the internals of `decide`
        let expectedType := lit.toExpr
        trace[Rule.falseElim] "Trying to decide {expectedType}"
        let d ← mkDecide expectedType
        let d ← instantiateMVars d
        let r ← withDefault <| whnf d
        unless r.isConstOf ``false do
          throwError "failed to reduce to 'false'{indentExpr r}"
        trace[Rule.falseElim] "{d} is false"
        let s := d.appArg! -- get instance from `d`
        let rflPrf ← mkEqRefl (toExpr false)
        let proofCase := mkApp3 (Lean.mkConst ``of_decide_eq_false) expectedType s rflPrf
        trace[Rule.falseElim] "built {proofCase} proving {d} is false"
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let proofCase := mkApp proofCase h
          let proofCase := mkApp2 (mkConst ``False.elim [levelZero]) body proofCase
          Meta.mkLambdaFVars #[h] proofCase
        caseProofs := caseProofs.push pr
      else
        -- need proof of `L_j → L_1 ∨ ... ∨ L_n`
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let idx := if j ≥ i then j - 1 else j
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx h
        caseProofs := caseProofs.push pr

    let r ← orCases (parentLits.map Lit.toExpr) caseProofs
    Meta.mkLambdaFVars xs $ mkApp r appliedPremise

def falseElimAtLit (given : Clause) (c : MClause) (i : Nat) : RuleM (Array ClauseStream) :=
  withoutModifyingMCtx $ do
    let lit := c.lits[i]!
    let eligibility ← eligibilityPreUnificationCheck c (alreadyReduced := true) i
    if eligibility == Eligibility.notEligible then return #[]
    let loaded ← getLoadedClauses
    let ug ← DUnif.UnifierGenerator.fromMetaMProcedure (isDecidablyFalseLiteral lit)
    let yC := do
      setLoadedClauses loaded
      if (not $ ← eligibilityPostUnificationCheck c (alreadyReduced := false) i eligibility (strict := true)) then return none
      let c := c.eraseLit i
      trace[Rule.falseElim] "Successfully yielded {c.lits} by removing literal {i}"
      yieldClause c "falseElim" $ some (mkFalseElimProof i)
    return #[ClauseStream.mk ug given yC "falseElim"]

/-- If there is a substitution σ and literal l in c such that σ(l) equates `True` and `False`, then
    falseElim yields the clause obtained by removing l from c and applying sigma to the rest of c -/
def falseElim (given : Clause) (c : MClause) (cNum : Nat) : RuleM (Array ClauseStream) := do
  trace[Rule.falseElim] "Running FalseElim on {c.lits}"
  let mut streams := #[]
  for i in [:c.lits.size] do
    if c.lits[i]!.sign then
      let str ← falseElimAtLit given c i
      streams := streams.append str
  return streams

end Duper