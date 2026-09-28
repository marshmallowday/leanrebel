/-
# Nash-derived replacement bounds with explicit model discrepancy

The recursive solver supplies its Nash error. The remaining transport cost
compares actual roots and opponents with the solver's modeled game; it never
compares the old and new own policies to infer policy closeness from Nash.
-/

import GameTheory.Analysis.ReBeL.PBSRecursiveRecomputedValue

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable [Fintype E.History]

/-- Two root-law errors and two opposing-policy errors for a Nash deviation.
Both execution charges follow their actual unknown-opponent prefixes. -/
def nashReplacementTransport
    (old fresh unknown : Profile M.behavioralSignature) (who : Fin 2)
    (fuel : Nat) (actual model : FinDist E.History) : ℝ :=
  2 * FinDist.atomVariation actual model +
    executionKernelCharge M (Profile.update unknown who (old who))
      (Profile.update fresh who (old who)) fuel actual +
    executionKernelCharge M (Profile.update unknown who (fresh who)) fresh fuel actual

/-- Changing neither roots nor opposing policies costs nothing, even when the
old and fresh own policies are far apart. No equilibrium uniqueness is used. -/
theorem nashReplacementTransport_same
    (old fresh : Profile M.behavioralSignature) (who : Fin 2)
    (fuel : Nat) (model : FinDist E.History) :
    nashReplacementTransport M old fresh fresh who fuel model model = 0 := by
  simp only [nashReplacementTransport, FinDist.atomVariation_self, mul_zero,
    Profile.update_eq_self, executionKernelCharge_self, add_zero]

/-- Independent primitive opponent-model rates yield an explicit finite-fuel
allowance. A root-law discrepancy is charged twice, not removed by support. -/
theorem nashReplacementTransport_le_rates
    (old fresh unknown : Profile M.behavioralSignature) (who : Fin 2)
    (fuel : Nat) (actual model : FinDist E.History) (incoming oldRate freshRate : ℝ)
    (root : FinDist.atomVariation actual model ≤ incoming)
    (oldSteps : ∀ history, FinDist.atomVariation
      (M.runBehavioralFrom (Profile.update unknown who (old who)) 1 history)
      (M.runBehavioralFrom (Profile.update fresh who (old who)) 1 history) ≤ oldRate)
    (freshSteps : ∀ history, FinDist.atomVariation
      (M.runBehavioralFrom (Profile.update unknown who (fresh who)) 1 history)
      (M.runBehavioralFrom fresh 1 history) ≤ freshRate) :
    nashReplacementTransport M old fresh unknown who fuel actual model ≤
      2 * incoming + (fuel : ℝ) * oldRate + (fuel : ℝ) * freshRate :=
  add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left root (by norm_num))
      (executionKernelCharge_le_mul M _ _ oldRate oldSteps fuel actual))
    (executionKernelCharge_le_mul M _ _ freshRate freshSteps fuel actual)

/-- Canonical approximate Nash controls a replacement against the actual
opponent after paying only the explicit root/opponent transport terms. -/
theorem behavioralNash_replacement_le
    {observations : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals observations)
    (old fresh unknown : Profile M.behavioralSignature) (who : Fin 2) (fuel : Nat)
    (actual : FinDist E.History) (payoff : Fin 2 → E.History → ℝ) (error bound : ℝ)
    (nonneg : 0 ≤ bound) (bounded : ∀ h, |payoff who h| ≤ bound)
    (equilibrium : IsNash (behavioralBeliefForm M belief fuel)
      (euPreferenceWithin error (fun h player => payoff player h)) fresh) :
    (actual.bind (M.runBehavioralFrom (Profile.update unknown who (old who)) fuel)).expect
        (payoff who) -
      (actual.bind (M.runBehavioralFrom (Profile.update unknown who (fresh who)) fuel)).expect
        (payoff who) ≤
      error + bound * nashReplacementTransport M old fresh unknown who fuel actual belief.law := by
  have deviation := (isNash_iff (F := behavioralBeliefForm M belief fuel)
    (weaklyPrefers := euPreferenceWithin error (fun h player => payoff player h))
    fresh).mp equilibrium who (old who)
  rw [euPreferenceWithin_apply] at deviation
  simp only [expectedUtility, behavioralBeliefForm, PublicBelief.continuationLaw] at deviation
  have leftError := (FinDist.abs_expect_sub_le_atomVariation
    (actual.bind (M.runBehavioralFrom (Profile.update unknown who (old who)) fuel))
    (belief.law.bind (M.runBehavioralFrom (Profile.update fresh who (old who)) fuel))
    (payoff who) bound bounded).trans
      (mul_le_mul_of_nonneg_left
        (runBehavioralFrom_atomVariation_le M _ _ fuel actual belief.law) nonneg)
  have rightError := (FinDist.abs_expect_sub_le_atomVariation
    (actual.bind (M.runBehavioralFrom (Profile.update unknown who (fresh who)) fuel))
    (belief.law.bind (M.runBehavioralFrom fresh fuel))
    (payoff who) bound bounded).trans
      (mul_le_mul_of_nonneg_left
        (runBehavioralFrom_atomVariation_le M _ _ fuel actual belief.law) nonneg)
  have leftUpper := (abs_le.mp leftError).2
  have rightLower := (abs_le.mp rightError).1
  unfold nashReplacementTransport
  nlinarith only [deviation, leftUpper, rightLower]

variable [∀ who, Fintype (E.Action who)]

/-- The actual recursive solver discharges the Nash premise, keeping its
finite allocated rounds, numerical contract and positive requested tolerance. -/
theorem pbsRecursiveDepth_replacement_le
    (noise : PBSRecursiveDepthNoise.{u}) (noiseBound : PBSRecursiveDepthNoiseBound noise)
    (cuts : List Nat) (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation.{0, u, u, u, u, u} M).toInfoSignals observations)
    (tolerance : ℝ) (positive : 0 < tolerance)
    (old unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (who : Fin 2) (actual : FinDist E.History) :
    let fresh := pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance
    recursivePolicyValueChange M old fresh unknown who cuts.sum actual (payoff who) ≤
      tolerance + bound * nashReplacementTransport.{u} (E := E)
        (fullInformation.{0, u, u, u, u, u} M)
        old fresh unknown who cuts.sum actual belief.law := by
  intro fresh
  have equilibrium := @pbsRecursiveDepth_isNash.{u} noise noiseBound cuts E M
    inferInstance inferInstance fallback payoff zeroSum bound nonneg bounded
    observations belief tolerance positive
  have estimate := @behavioralNash_replacement_le.{u} E
    (fullInformation.{0, u, u, u, u, u} M) inferInstance observations belief
    old fresh unknown who cuts.sum actual payoff tolerance bound nonneg (bounded who) equilibrium
  unfold recursivePolicyValueChange
  rw [FinDist.expect_sub]
  simpa only [FinDist.expect_bind] using estimate

/-- On the modeled root law against the computed opposing policy, only the
actual solver tolerance remains. The old own policy is entirely arbitrary. -/
theorem pbsRecursiveDepth_model_replacement_le
    (noise : PBSRecursiveDepthNoise.{u}) (noiseBound : PBSRecursiveDepthNoiseBound noise)
    (cuts : List Nat) (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation.{0, u, u, u, u, u} M).toInfoSignals observations)
    (tolerance : ℝ) (positive : 0 < tolerance)
    (old : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2) :
    let fresh := pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance
    recursivePolicyValueChange M old fresh fresh who cuts.sum belief.law (payoff who) ≤
      tolerance := by
  intro fresh
  have estimate := pbsRecursiveDepth_replacement_le.{u} (E := E) M noise noiseBound cuts
    fallback payoff zeroSum bound nonneg bounded belief tolerance positive old fresh who belief.law
  simpa only [nashReplacementTransport_same.{u}, mul_zero, add_zero] using estimate

end GameTheory.ReBeL
