import Duper.Simp
import Duper.Selection
import Duper.Util.ProofReconstruction

namespace Duper

open Lean
open Lean.Meta
open RuleM
open SimpResult
open Comparison
initialize Lean.registerTraceClass `Rule.demodulation

def mkDemodulationProof (sidePremiseLhs : LitSide) (mainPremisePos : ClausePos) (isForward : Bool)
  (premises : List Expr) (parents : List ProofParent) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises) ← instantiatePremises parents premises xs

    let mainParentLits := if isForward then parentsLits[1]! else parentsLits[0]!
    let sideParentLits := if isForward then parentsLits[0]! else parentsLits[1]!
    let appliedMainPremise := if isForward then appliedPremises[1]! else appliedPremises[0]!
    let appliedSidePremise := if isForward then appliedPremises[0]! else appliedPremises[1]!

    let eqLit := sideParentLits[0]!

    let proof ← Meta.withLocalDeclD `heq eqLit.toExpr fun heq => do
      let mut caseProofs : Array Expr := Array.mkEmpty mainParentLits.size
      let eq :=
        if sidePremiseLhs == LitSide.rhs then ← Meta.mkAppM ``Eq.symm #[heq]
        else heq
      for i in [:mainParentLits.size] do
        let lit := mainParentLits[i]!
        let pr : Expr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          if(i == mainPremisePos.lit) then
            let litPos : LitPos := {side := mainPremisePos.side, pos := mainPremisePos.pos}
            let abstrLit ← (lit.abstractAtPos! litPos)
            let abstrExp := abstrLit.toExpr
            let abstrLam := mkLambda `x BinderInfo.default (← Meta.inferType eqLit.lhs) abstrExp
            let rwproof ← Meta.mkAppM ``Eq.mp #[← Meta.mkAppM ``congrArg #[abstrLam, eq], h]
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) i $ rwproof
          else
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) i h
        caseProofs := caseProofs.push $ pr
      let r ← orCases (mainParentLits.map Lit.toExpr) caseProofs
      Meta.mkLambdaFVars #[heq] $ mkApp r appliedMainPremise
    let proof ← Meta.mkLambdaFVars xs $ mkApp proof appliedSidePremise
    return proof

/- Note: I am implementing Schulz's side conditions for RP and RN, except for the condition that RP is allowed if p ≠ λ or σ 
   is a variable renaming. The reason for this is that I suspect I will just have to change the side conditions later to match
   "Superposition for Full Higher-Order Logic", so there's little point in being super precise about implementing Schulz's more
   annoying side conditions.

   So the side conditions I'm implementing are:
   - If mainPremise.lits[mainPremisePos.lit].sign is true (i.e. we are in the RP case), then all of the following must hold:
      1. sidePremise.sidePremiseLhs must match mainPremiseSubterm
      2. sidePremise.sidePremiseLhs must be greater than sidePremise.getOtherSide sidePremiseLhs after matching is performed
      3. mainPremise.lits[mainPremisePos.lit] must not be eligible for paramodulation (in Schulz's paper, we could instead have
         p ≠ λ or σ not be a variable renaming, but these are the conditions I'm not implementing right now)
   - If mainPremise.lits[mainPremisePos.lit].sign is false (i.e. we are in the RN case), then all of the following must hold:
      1. sidePremise.sidePremiseLhs must match mainPremiseSubterm
      2. sidePremise.sidePremiseLhs must be greater than sidePremise.getOtherSide sidePremiseLhs after matching is performed
-/
def forwardDemodulationWithPartner (mainPremise : MClause) (mainPremiseSubterm : Expr) (mainPremisePos : ClausePos)
  (sidePremise : MClause) (sidePremiseLhs : LitSide) : RuleM (SimpResult (List (MClause × Option ProofReconstructor))) := do
  Core.checkMaxHeartbeats "forward demodulation"
  let sidePremiseLit := sidePremise.lits[0]!.makeLhs sidePremiseLhs
  if (mainPremise.lits[mainPremisePos.lit]!.sign && (← eligibleForParamodulation mainPremise mainPremisePos.lit)) then
    return Unapplicable -- Cannot perform demodulation because Schulz's side conditions are not met
  if not (← RuleM.performMatch #[(mainPremiseSubterm, sidePremiseLit.lhs)]) then
    return Unapplicable -- Cannot perform demodulation because we could not match sidePremiseLit.lhs to mainPremiseSubterm
  if (← compare sidePremiseLit.lhs sidePremiseLit.rhs) != Comparison.GreaterThan then
    return Unapplicable -- Cannot perform demodulation because side condition 2 listed above is not met
  let mainPremiseReplaced ← mainPremise.replaceAtPos! mainPremisePos $ ← RuleM.instantiateMVars sidePremiseLit.rhs
  return Applied [(mainPremiseReplaced, (some $ mkDemodulationProof sidePremiseLhs mainPremisePos true))]

def forwardDemodulationAtExpr (e : Expr) (pos : ClausePos) (activeSet : ProverM.ClauseSet) (givenMainClause : MClause) :
  RuleM (SimpResult (List (MClause × Option ProofReconstructor))) := do
  for sideClause in activeSet.toList do
    -- Since I'm not using indices, I need to check eligibility here
    if (sideClause.lits.size != 1 || not sideClause.lits[0]!.sign) then continue
    let (mclause, cToLoad) ← prepLoadClause sideClause
    -- Using foldM rather than foldGreenM because the only valid position for demodulation's side premise is the whole lhs or the whole rhs
    let sideClauseDemodulationRes ← mclause.foldM fun acc sideE sidePos =>
      do
        match acc with
        | Unapplicable => forwardDemodulationWithPartner givenMainClause e pos mclause sidePos.side
        | Applied transformedClauses => return Applied transformedClauses
        | Removed => throwError "Invalid demodulation result"
      Unapplicable
    match sideClauseDemodulationRes with
    | Unapplicable => continue
    | Applied res =>
      -- forwardDemodulationWithPartner succeeded so we need to add cToLoad to loadedClauses in the state
      setLoadedClauses (cToLoad :: (← getLoadedClauses))
      trace[Rule.demodulation] "Main clause: {givenMainClause.lits} at lit: {pos.lit} at expression: {e}"
      trace[Rule.demodulation] "Side clause: {sideClause}"
      trace[Rule.demodulation] "Result: {(List.get! res 0).1.lits}"
      return Applied res
    | Removed => throwError "Invalid demodulation result"
  return Unapplicable

/-- Performs rewriting of positive and negative literals (demodulation) with the given clause c as the main clause. We only attempt
    to use c as the main clause (rather than attempt to use it as a side clause as well) because if we used c as a side clause, we
    would remove the wrong clause from the active set (we would remove c rather than the main clause that c is paired with). c will 
    considered as a side clause in the backward simplificaiton loop (i.e. in backwardDemodulation) -/
def forwardDemodulation (activeSet : ProverM.ClauseSet) : MSimpRule := fun c => do
  let c ← loadClause c
  let fold_fn := fun acc e pos => do
    match acc with
    | Unapplicable => forwardDemodulationAtExpr e pos activeSet c
    | Applied res => return Applied res -- If forwardDemodulationAtExpr ever succeeds, just return the first success
    | Removed => throwError "Invalid demodulation result"
  -- TODO: Determine if foldGreenM is an appropriate function here or if I need one that considers all subexpressions,
  -- rather than just green ones
  c.foldGreenM fold_fn Unapplicable

open BackwardSimpResult

/- Note: I am implementing Schulz's side conditions for RP and RN, except for the condition that RP is allowed if p ≠ λ or σ
   is a variable renaming. The reason for this is that I suspect I will just have to change the side conditions later to match
   "Superposition for Full Higher-Order Logic", so there's little point in being super precise about implementing Schulz's more
   annoying side conditions.

   So the side conditions I'm implementing are:
   - If mainPremise.lits[mainPremisePos.lit].sign is true (i.e. we are in the RP case), then all of the following must hold:
      1. sidePremise.sidePremiseLhs must match mainPremiseSubterm
      2. sidePremise.sidePremiseLhs must be greater than sidePremise.getOtherSide sidePremiseLhs after matching is performed
      3. mainPremise.lits[mainPremisePos.lit] must not be eligible for paramodulation (in Schulz's paper, we could instead have
         p ≠ λ or σ not be a variable renaming, but these are the conditions I'm not implementing right now)
   - If mainPremise.lits[mainPremisePos.lit].sign is false (i.e. we are in the RN case), then all of the following must hold:
      1. sidePremise.sidePremiseLhs must match mainPremiseSubterm
      2. sidePremise.sidePremiseLhs must be greater than sidePremise.getOtherSide sidePremiseLhs after matching is performed
-/
def backwardDemodulationWithPartner (mainPremise : MClause) (mainPremiseSubterm : Expr) (mainPremisePos : ClausePos)
  (sidePremise : MClause) (sidePremiseLhs : LitSide) : RuleM BackwardSimpResult := do
  Core.checkMaxHeartbeats "backward demodulation"
  let sidePremiseLit := sidePremise.lits[0]!.makeLhs sidePremiseLhs
  if (mainPremise.lits[mainPremisePos.lit]!.sign && (← eligibleForParamodulation mainPremise mainPremisePos.lit)) then
    return Unapplicable -- Cannot perform demodulation because Schulz's side conditions are not met
  if not (← performMatch #[(mainPremiseSubterm, sidePremiseLit.lhs)]) then
    return Unapplicable -- Cannot perform demodulation because we could not match sidePremiseLit.lhs to mainPremiseSubterm
  if (← compare sidePremiseLit.lhs sidePremiseLit.rhs) != Comparison.GreaterThan then
    return Unapplicable -- Cannot perform demodulation because side condition 2 listed above is not met
  let mainPremiseReplaced ← mainPremise.replaceAtPos! mainPremisePos $ ← RuleM.instantiateMVars sidePremiseLit.rhs
  return Applied [(mainPremise, (mainPremiseReplaced, (some $ mkDemodulationProof sidePremiseLhs mainPremisePos false)))]

/-- Performs rewriting of positive and negative literals (demodulation) with the given clause as the side clause. -/
def backwardDemodulation (activeSet : ProverM.ClauseSet) : BackwardMSimpRule := fun givenSideClause => do
  let givenSideClause ← loadClause givenSideClause
  if givenSideClause.lits.size != 1 || not givenSideClause.lits[0]!.sign then return Unapplicable
  let l := givenSideClause.lits[0]!
  let c ← compare l.lhs l.rhs
  if (c == Incomparable || c == Equal) then return Unapplicable

  let givenSideClauseLhs := -- givenSideClause.getSide givenSideClauseLhs is will function as the lhs of the side clause
    if c == GreaterThan then LitSide.lhs
    else LitSide.rhs

  for mainClause in activeSet.toList do
    let (mclause, cToLoad) ← prepLoadClause mainClause
    -- TODO: Determine if foldGreenM is an appropriate function here or if I need one that considers all subexpressions,
    -- rather than just green ones
    let mainClauseDemodulationRes ← mclause.foldGreenM fun acc mainE mainPos =>
      do
        match acc with
        | BackwardSimpResult.Unapplicable => backwardDemodulationWithPartner mclause mainE mainPos givenSideClause givenSideClauseLhs
        | BackwardSimpResult.Applied transformedClauses => return BackwardSimpResult.Applied transformedClauses
        | BackwardSimpResult.Removed removedClauses => throwError "Invalid demodulation result"
      BackwardSimpResult.Unapplicable
    match mainClauseDemodulationRes with
    | BackwardSimpResult.Unapplicable => continue
    | BackwardSimpResult.Applied transformedClauses =>
      -- backwardDemodulationWithPartner succeeded so we need to add cToLoad to loadedClauses in the state
      setLoadedClauses (cToLoad :: (← getLoadedClauses))
      trace[Rule.demodulation] "Applying backward demodulation with givenSideClause: {givenSideClause.lits} and main mclause: {mclause.lits}"
      trace[Rule.demodulation] "transformedClauses.1: {(transformedClauses.get! 0).1.lits}"
      trace[Rule.demodulation] "transformedClauses.2: {(transformedClauses.get! 0).2.1.lits}"
      return BackwardSimpResult.Applied transformedClauses
    | BackwardSimpResult.Removed removedClauses => throwError "Invalid demodulation result"
  return Unapplicable