/-
# Coherent draw controls: sampled plans, off-model roots and finite children

A fair behavioral profile is never one of its deterministic sampled profiles,
yet their unilateral history laws agree. The actual noisy finite-child trace
instantiates the envelope and security without a supplied continuation bound.
-/

import GameTheory.Analysis.ReBeL.CFRDFiniteCoherent
import GameTheory.Analysis.ReBeL.Examples.CFRDEnvelope
import GameTheory.Analysis.ReBeL.Examples.CFRDLiveControl

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- The existing finite canonical history enumeration. -/
local instance coherentHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Legal finite menus, including counterfactual and inactive information states. -/
local instance coherentChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Information equality used by the actual outer recurrence. -/
local instance coherentInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- Every sampled profile is different from this genuinely randomized source.
Thus the resolver is not a pure wrapper around the unchanged profile. -/
theorem coherent_fair_draw_not_source (next : Profile (model fullPrior).behavioralSignature)
    (sampled : next ∈ (cfrDPolicyDraw (model fullPrior) cfrFallback liveFairContinuation).support) :
    next ≠ liveFairContinuation := by
  intro same
  subst next
  obtain ⟨action, pure⟩ := cfrDPolicyDraw_supported_pure (model fullPrior) cfrFallback
    liveFairContinuation liveFairContinuation sampled 0
    ((model fullPrior).infoOf 0 (decode (.second false false false false)).trace)
  have fair := liveFairSecondLaw false false false false 0
  unfold liveSecondLaw at fair
  rw [pure, FinDist.map_pure] at fair
  have half (bit : Bool) : carriedBitLaw.prob bit = 1 / 2 := by
    cases bit <;> norm_num [carriedBitLaw, FinDist.prob_mix, FinDist.prob_pure_eq_ite]
  have mass := congrArg (fun law : FinDist Bool =>
    law.prob ((liveSecondEquiv false false false false 0).symm action)) fair
  rw [FinDist.prob_pure_self, half] at mass
  norm_num at mass

/-- The changed private draw nevertheless preserves all outcomes at a live
root excluded by the factual parent. No model posterior is postulated. -/
theorem coherent_fair_off_model_law
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    (cfrDPolicyDraw (model fullPrior) cfrFallback liveFairContinuation).bind (fun next =>
      (model fullPrior).runBehavioralFrom (Profile.update unknown who (next who))
        1 zeroControlHistory) =
      (model fullPrior).runBehavioralFrom
        (Profile.update unknown who (liveFairContinuation who)) 1 zeroControlHistory :=
  cfrDPolicyDraw_run (model fullPrior) (perfectRecall fullPrior) cfrFallback
    liveFairContinuation unknown who 1 zeroControlHistory

/-- Exhausted execution fuel bypasses sampling even at an arbitrary carried state. -/
theorem coherent_zero_fuel (t : Nat) (unknown : Profile (model fullPrior).behavioralSignature)
    (who : Player) (state : PrivateIterationState (model fullPrior) (Fin t)) :
    carriedResolvedTail (model fullPrior)
        (cfrDCoherentResolver (model fullPrior) cfrFallback (envelopeControlPlays t))
        unknown who 0 state = FinDist.pure state.history := by
  simp only [carriedResolvedTail, cfrDCutLive_zero, Bool.false_eq_true, if_false]

/-- The real finite child's noisy parent trace supplies the opponent envelope
for an actual private-plan draw; neither child Nash nor a local ceiling is input. -/
theorem coherent_finite_envelope (t : Nat)
    (unknown : Profile (model fullPrior).behavioralSignature) (who opponent : Player)
    (different : opponent ≠ who) :
    CFRDResolverEnvelope (model fullPrior) (envelopeControlPlays t)
      (cfrDFiniteCoherentResolver (reducedModel fullPrior) cfrFallback cfrPayoff 2 1
        2 (1 / 4) (fun _ _ _ _ => 1 / 8) t) cfrFallback unknown
      who opponent 2 1 (cfrPayoff opponent) (1 / 4) :=
  cfrDFiniteCoherentResolver_envelope (reducedModel fullPrior) cfrFallback cfrPayoff
    (cumulative_zeroSum fullPrior) 2 1 2 (1 / 4) (by norm_num) (by norm_num)
    cfrPayoff_abs_le_two (fun _ _ _ _ => 1 / 8) unknown who opponent different t

/-- The sampled finite-solver execution preserves the complete actual law,
not only the value at its assumed opponent model. -/
theorem coherent_finite_law (t : Nat) [NeZero t]
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    privateCarriedResolve (model fullPrior) (cfrIterationLaw t) (envelopeControlPlays t)
        (cfrDFiniteCoherentResolver (reducedModel fullPrior) cfrFallback cfrPayoff 2 1
          2 (1 / 4) (fun _ _ _ _ => 1 / 8) t) unknown who 2 1 =
      privateCarriedContinue (model fullPrior) (cfrIterationLaw t) (envelopeControlPlays t)
        unknown who 2 1 :=
  cfrDFiniteCoherentResolver_law (reducedModel fullPrior) cfrFallback cfrPayoff 2 1
    2 (1 / 4) (fun _ _ _ _ => 1 / 8) unknown who t

/-- A live actual finite-solver instance has no switching penalty; its two
nonzero error sources and the finite outer-iteration term are still explicit. -/
theorem coherent_finite_security (t : Nat) [NeZero t]
    (reference : Profile (model fullPrior).behavioralSignature)
    (equilibrium : IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreference (fun h who => cfrPayoff who h)) reference)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    ((model fullPrior).runBehavioral reference 3).expect (cfrPayoff who) -
      ((cfrDDepthErrorConstant (model fullPrior) decisionClock cfrFallback 2 1 0 +
          cfrDDepthErrorConstant (model fullPrior) decisionClock cfrFallback 2 1 1) * (1 / 8) +
        (cfrDDepthFiniteConstant (model fullPrior) decisionClock cfrFallback 2 1 2 0 +
          cfrDDepthFiniteConstant (model fullPrior) decisionClock cfrFallback 2 1 2 1) /
          Real.sqrt t + 2 * (1 / 4)) ≤
      (privateCarriedResolve (model fullPrior) (cfrIterationLaw t) (envelopeControlPlays t)
        (cfrDFiniteCoherentResolver (reducedModel fullPrior) cfrFallback cfrPayoff 2 1
          2 (1 / 4) (fun _ _ _ _ => 1 / 8) t) unknown who 2 1).expect (cfrPayoff who) := by
  exact cfrDFiniteCoherentResolver_security (reducedModel fullPrior) cfrFallback cfrPayoff
    (cumulative_zeroSum fullPrior) 2 1 2 (1 / 8) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) cfrPayoff_abs_le_two
    (fun _ _ _ _ => 1 / 8) (by intros; norm_num) reference equilibrium unknown who t

end GameTheory.ReBeL.Examples.HiddenTypes
