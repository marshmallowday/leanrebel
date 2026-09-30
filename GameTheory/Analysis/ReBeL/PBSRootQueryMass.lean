/-
# Query-weighted rooted comparisons with explicit actual/model discrepancy

This is a diagnostic on eligible public queries, not a replacement of the native
runner. Nonqueries contribute zero only to this restricted diagnostic. Their
native costs are not declared zero. Actual and model history weights stay distinct.
-/

import GameTheory.Analysis.ReBeL.PBSRootStoredState
import GameTheory.Math.Probability.FinDistConditionalMass

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u v
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)

/-- The stopped fraction at a possible query is the conditional event share.
The total conditional's absent-label fallback is not used by this equality. -/
theorem pbsRootStoppedFraction_eq_share
    (roots : FinDist E.History)
    (trunk : Profile (pbsRootFullInformation M roots).behavioralSignature)
    (cut remaining : Nat)
    (observations : List M.PublicSignal) (past : List (Option (List M.PublicSignal)))
    (possible : CFRDFactualChildPossible
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots)
      trunk cut remaining (some observations :: past)) :
    pbsRootStoppedFraction M roots trunk cut remaining observations past =
      FinDist.conditionalEventShare ((pbsRootFullInformation M roots).runBehavioral trunk cut)
        (fun h => publicTrace (pbsRootFullInformation M roots).toInfoSignals h.trace)
        {h | cfrDCutLive remaining h ≠ true} (some observations :: past) := by
  exact (FinDist.conditionalEventShare_eq_ratio _ _ _ _
    (cfrDFactualChildPossible_public
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots)
      trunk cut remaining (some observations :: past) possible)).symm

variable {outerObs : List M.PublicSignal}
variable (outer : PublicBelief (fullInformation.{0, u, u, u, u, u} M).toInfoSignals outerObs)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- The same finite rooted history carrier used by the actual child solver. -/
local instance rootQueryHistory : Fintype (pbsRootProtocol outer.law).History :=
  pbsRootHistoryFintype outer.law

/-- Scalar gap and signed private-security deficit at each eligible query.
The internal request is the actual child-table mass floor times parent loss.
Zero elsewhere excludes that label from this diagnostic, not from native costs. -/
def pbsRootQueryComparison
    (trunk : Profile (pbsRootFullInformation M outer.law).behavioralSignature)
    (cut remaining : Nat) (internalNoise freshNoise : PBSRecursiveDepthNoise.{u})
    (internalCuts freshCuts : List Nat)
    (internalFallback freshFallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (bound loss freshError : ℝ)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (tag : List (Option (List M.PublicSignal))) : ℝ × ℝ := by
  classical
  exact match tag with
  | some observations :: past =>
      if possible : CFRDFactualChildPossible
          (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law)
          trunk cut remaining (some observations :: past) then
        let child := cfrDFactualChildBelief
          (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law)
          trunk cut remaining (some observations :: past) possible
        let posterior := pbsRootPublicPosterior M outer.law trunk cut remaining
          observations past possible
        let decodedChild := pbsRootChildBelief M outer.law child
        let decodedPublic := pbsRootChildBelief M outer.law posterior
        let internal := pbsRootChildRecursiveProfile M outer internalNoise internalCuts
          internalFallback payoff bound child (child.law.positiveMassFloor * loss)
        let fresh := pbsRecursiveDepth freshNoise freshCuts E M freshFallback payoff bound
          decodedPublic freshError
        let internalValue := (decodedChild.law.bind
          ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom internal remaining)).expect
            (payoff who)
        let freshValue := (decodedPublic.law.bind
          ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom fresh remaining)).expect
            (payoff who)
        let privateValue := (pbsRecursiveDepthDraw freshNoise freshCuts M freshFallback
          payoff bound decodedPublic freshError).expect (fun chosen =>
            (decodedPublic.law.bind
              ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom
                (Profile.update unknown who (chosen who)) remaining)).expect (payoff who))
        (|internalValue - freshValue|, internalValue - privateValue)
      else (0, 0)
  | _ => (0, 0)

/-- Actual recursive Nash and private-draw theorems discharge both comparisons.
Only the internal mass-scaled request is enlarged to its parent loss. -/
theorem pbsRootQueryComparison_le
    (trunk : Profile (pbsRootFullInformation M outer.law).behavioralSignature)
    (cut remaining : Nat) (internalNoise freshNoise : PBSRecursiveDepthNoise.{u})
    (internalCuts freshCuts : List Nat)
    (internalFallback freshFallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (bound loss freshError : ℝ)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (internalNoiseBound : PBSRecursiveDepthNoiseBound internalNoise)
    (freshNoiseBound : PBSRecursiveDepthNoiseBound freshNoise)
    (internalHorizon : internalCuts.sum = remaining) (freshHorizon : freshCuts.sum = remaining)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    (lossPositive : 0 < loss) (freshPositive : 0 < freshError)
    (tag : List (Option (List M.PublicSignal))) :
    (pbsRootQueryComparison M outer trunk cut remaining internalNoise freshNoise
      internalCuts freshCuts internalFallback freshFallback payoff bound loss freshError
      unknown who tag).1 ≤ loss + freshError +
        2 * bound * FinDist.conditionalEventShare
          ((pbsRootFullInformation M outer.law).runBehavioral trunk cut)
          (fun h => publicTrace (pbsRootFullInformation M outer.law).toInfoSignals h.trace)
          {h | cfrDCutLive remaining h ≠ true} tag ∧
    (pbsRootQueryComparison M outer trunk cut remaining internalNoise freshNoise
      internalCuts freshCuts internalFallback freshFallback payoff bound loss freshError
      unknown who tag).2 ≤ loss + 2 * freshError +
        2 * bound * FinDist.conditionalEventShare
          ((pbsRootFullInformation M outer.law).runBehavioral trunk cut)
          (fun h => publicTrace (pbsRootFullInformation M outer.law).toInfoSignals h.trace)
          {h | cfrDCutLive remaining h ≠ true} tag := by
  classical
  have zeroBounds (label : List (Option (List M.PublicSignal))) :
      0 ≤ loss + freshError + 2 * bound * FinDist.conditionalEventShare
        ((pbsRootFullInformation M outer.law).runBehavioral trunk cut)
        (fun h => publicTrace (pbsRootFullInformation M outer.law).toInfoSignals h.trace)
        {h | cfrDCutLive remaining h ≠ true} label ∧
      0 ≤ loss + 2 * freshError + 2 * bound * FinDist.conditionalEventShare
        ((pbsRootFullInformation M outer.law).runBehavioral trunk cut)
        (fun h => publicTrace (pbsRootFullInformation M outer.law).toInfoSignals h.trace)
        {h | cfrDCutLive remaining h ≠ true} label := by
    have share := (FinDist.conditionalEventShare_bounds
      ((pbsRootFullInformation M outer.law).runBehavioral trunk cut)
      (fun h => publicTrace (pbsRootFullInformation M outer.law).toInfoSignals h.trace)
      {h | cfrDCutLive remaining h ≠ true} label).1
    constructor <;> positivity
  cases tag with
  | nil => exact zeroBounds []
  | cons head past =>
      cases head with
      | none => exact zeroBounds (none :: past)
      | some observations =>
          by_cases possible : CFRDFactualChildPossible
            (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law)
            trunk cut remaining (some observations :: past)
          · let child := cfrDFactualChildBelief
              (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law)
              trunk cut remaining (some observations :: past) possible
            have requestPositive : 0 < child.law.positiveMassFloor * loss :=
              mul_pos (FinDist.positiveMassFloor_pos child.law) lossPositive
            have floorBound : child.law.positiveMassFloor ≤ 1 := by
              obtain ⟨h, reached⟩ := child.law.support_nonempty
              exact (FinDist.positiveMassFloor_le child.law h reached).trans
                (FinDist.prob_le_one child.law h)
            have requestBound : child.law.positiveMassFloor * loss ≤ loss := by
              simpa only [one_mul] using
                mul_le_mul_of_nonneg_right floorBound lossPositive.le
            have scalar := pbsRootStored_fresh_value M outer trunk cut remaining
              observations past possible internalNoise freshNoise internalNoiseBound freshNoiseBound
              internalCuts freshCuts internalHorizon freshHorizon internalFallback freshFallback
              payoff zeroSum bound nonneg bounded (child.law.positiveMassFloor * loss) freshError
              requestPositive freshPositive who
            have security := pbsRootStored_fresh_security M outer trunk cut remaining
              observations past possible internalNoise freshNoise internalNoiseBound freshNoiseBound
              internalCuts freshCuts internalHorizon freshHorizon internalFallback freshFallback
              payoff zeroSum bound nonneg bounded (child.law.positiveMassFloor * loss) freshError
              requestPositive freshPositive unknown who
            dsimp only [child] at scalar security requestBound
            rw [pbsRootStoppedFraction_eq_share M outer.law trunk cut remaining
              observations past possible] at scalar security
            simp only [pbsRootQueryComparison, dif_pos possible]
            constructor
            · linarith only [scalar, requestBound]
            · linarith only [security, requestBound]
          · simpa only [pbsRootQueryComparison, dif_neg possible] using
              zeroBounds (some observations :: past)

/-- Aggregate using the incoming history law's own query weights. Model
stopped mass replaces inverse reach; actual/model variation remains explicit.
This controls MODEL comparisons, not factual execution security. -/
theorem pbsRootQueryComparison_mean
    (trunk : Profile (pbsRootFullInformation M outer.law).behavioralSignature)
    (cut remaining : Nat) (internalNoise freshNoise : PBSRecursiveDepthNoise.{u})
    (internalCuts freshCuts : List Nat)
    (internalFallback freshFallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (bound loss freshError : ℝ)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (internalNoiseBound : PBSRecursiveDepthNoiseBound internalNoise)
    (freshNoiseBound : PBSRecursiveDepthNoiseBound freshNoise)
    (internalHorizon : internalCuts.sum = remaining) (freshHorizon : freshCuts.sum = remaining)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    (lossPositive : 0 < loss) (freshPositive : 0 < freshError)
    (actual : FinDist (pbsRootProtocol outer.law).History) :
    (actual.map
      (fun h => publicTrace (pbsRootFullInformation M outer.law).toInfoSignals h.trace)).expect
      (fun tag => (pbsRootQueryComparison M outer trunk cut remaining internalNoise freshNoise
        internalCuts freshCuts internalFallback freshFallback payoff bound loss freshError
        unknown who tag).1) ≤
      loss + freshError + 2 * bound *
        (((pbsRootFullInformation M outer.law).runBehavioral trunk cut).probOf
          {h | cfrDCutLive remaining h ≠ true} + FinDist.atomVariation actual
            ((pbsRootFullInformation M outer.law).runBehavioral trunk cut)) ∧
    (actual.map
      (fun h => publicTrace (pbsRootFullInformation M outer.law).toInfoSignals h.trace)).expect
      (fun tag => (pbsRootQueryComparison M outer trunk cut remaining internalNoise freshNoise
        internalCuts freshCuts internalFallback freshFallback payoff bound loss freshError
        unknown who tag).2) ≤
      loss + 2 * freshError + 2 * bound *
        (((pbsRootFullInformation M outer.law).runBehavioral trunk cut).probOf
          {h | cfrDCutLive remaining h ≠ true} + FinDist.atomVariation actual
            ((pbsRootFullInformation M outer.law).runBehavioral trunk cut)) := by
  have pointwise := pbsRootQueryComparison_le M outer trunk cut remaining
    internalNoise freshNoise internalCuts freshCuts internalFallback freshFallback
    payoff bound loss freshError unknown who internalNoiseBound freshNoiseBound
    internalHorizon freshHorizon zeroSum nonneg bounded lossPositive freshPositive
  constructor
  · exact FinDist.expect_le_conditionalEventShare_budget actual
      ((pbsRootFullInformation M outer.law).runBehavioral trunk cut)
      (fun h => publicTrace (pbsRootFullInformation M outer.law).toInfoSignals h.trace)
      {h | cfrDCutLive remaining h ≠ true}
      _ (loss + freshError) (2 * bound) (by positivity) (fun tag _ => (pointwise tag).1)
  · exact FinDist.expect_le_conditionalEventShare_budget actual
      ((pbsRootFullInformation M outer.law).runBehavioral trunk cut)
      (fun h => publicTrace (pbsRootFullInformation M outer.law).toInfoSignals h.trace)
      {h | cfrDCutLive remaining h ≠ true}
      _ (loss + 2 * freshError) (2 * bound) (by positivity) (fun tag _ => (pointwise tag).2)

/-- Native checkpoints supply actual weights through their history marginal.
The joint state law stays intact; no independent memory product or model PBS
replaces its actual history distribution. No factual security is asserted. -/
theorem pbsRootQueryComparison_native_mean {K : Type v}
    (trunk : Profile (pbsRootFullInformation M outer.law).behavioralSignature)
    (cut remaining : Nat) (internalNoise freshNoise : PBSRecursiveDepthNoise.{u})
    (internalCuts freshCuts : List Nat)
    (internalFallback freshFallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (bound loss freshError : ℝ)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (internalNoiseBound : PBSRecursiveDepthNoiseBound internalNoise)
    (freshNoiseBound : PBSRecursiveDepthNoiseBound freshNoise)
    (internalHorizon : internalCuts.sum = remaining) (freshHorizon : freshCuts.sum = remaining)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    (lossPositive : 0 < loss) (freshPositive : 0 < freshError)
    (states : FinDist (PrivateIterationState (pbsRootFullInformation M outer.law) K)) :
    states.expect (fun state =>
      (pbsRootQueryComparison M outer trunk cut remaining internalNoise freshNoise
        internalCuts freshCuts internalFallback freshFallback payoff bound loss freshError
        unknown who
        (publicTrace (pbsRootFullInformation M outer.law).toInfoSignals state.history.trace)).2) ≤
      loss + 2 * freshError + 2 * bound *
        (((pbsRootFullInformation M outer.law).runBehavioral trunk cut).probOf
          {h | cfrDCutLive remaining h ≠ true} +
          FinDist.atomVariation (states.map (fun state => state.history))
            ((pbsRootFullInformation M outer.law).runBehavioral trunk cut)) := by
  have estimate := (pbsRootQueryComparison_mean M outer trunk cut remaining
    internalNoise freshNoise internalCuts freshCuts internalFallback freshFallback
    payoff bound loss freshError unknown who internalNoiseBound freshNoiseBound
    internalHorizon freshHorizon zeroSum nonneg bounded lossPositive freshPositive
    (states.map (fun state => state.history))).2
  rw [FinDist.expect_map, FinDist.expect_map] at estimate
  exact estimate

end GameTheory.ReBeL
