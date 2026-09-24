/-
# Structurally recursive, finite-budget PBS CFR-D

A finite list counts original transitions between public cuts. At each level
we construct a new chance-rooted protocol and call the same algorithm on the
strictly shorter tail. The empty list performs no original transition and uses
a legal fallback; no deepest full-root solver or supplied child equilibrium is
hidden in the base case. Accuracy is proved separately by list induction.

Uniform carrier universes keep the changing rooted model inside one family.
This is a classical real-valued specification, not a numerical refinement claim.
-/

import GameTheory.Analysis.ReBeL.PBSComposedDepth

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u

/-- A prediction family reads only the modeled query and its allocated error.
The same family can be applied to each newly constructed rooted protocol. -/
abbrev PBSRecursiveDepthNoise :=
  {E : ExecutionProtocol.{0, u, u} (Fin 2)} →
  (M : InformationModel.{0, u, u, u, u, u} E) →
  (roots : FinDist E.History) → ℝ → PBSRootDepthNoise M roots

/-- A numerical approximation contract, separate from the algorithm and its
Nash theorem. It is not a claim that an arbitrary learned network satisfies it. -/
def PBSRecursiveDepthNoiseBound (noise : PBSRecursiveDepthNoise.{u}) : Prop :=
  ∀ {E : ExecutionProtocol.{0, u, u} (Fin 2)}
    (M : InformationModel.{0, u, u, u, u, u} E) (roots : FinDist E.History)
    error, 0 ≤ error → ∀ n trunk who info, |noise M roots error n trunk who info| ≤ error

/-- Computational data only: neither a Nash witness nor a correctness proof
is an argument of a recursive solver. -/
abbrev PBSRecursiveDepthFamily :=
  {E : ExecutionProtocol.{0, u, u} (Fin 2)} →
  (M : InformationModel.{0, u, u, u, u, u} E) →
  [Fintype E.History] → [∀ who, Fintype (E.Action who)] →
  Profile M.strategicSignature → (Fin 2 → E.History → ℝ) → ℝ → PBSChildSolve M

/-- Recurse on a finite cut schedule, not on a claimed convergence witness.
Every parent computes its finite round count and its actual factual child PBSs. -/
def pbsRecursiveDepth (noise : PBSRecursiveDepthNoise.{u}) :
    List Nat → PBSRecursiveDepthFamily.{u}
  | [] => by
      intro E M _ _ fallback _payoff _bound obs _belief _tolerance
      exact fun who => (cfrDInformationFallback M fallback who).toBehavioral
  | cut :: tail => by
      intro E M _ _ fallback payoff bound obs belief tolerance
      letI : Fintype (pbsRootProtocol belief.law).History := pbsRootHistoryFintype belief.law
      let error := pbsDepthAllocationError
        (pbsRootDepthErrorFactor M belief.law fallback cut tail.sum) tolerance
      exact pbsComposedDepthProfile M belief fallback payoff cut tail.sum bound error
        (tolerance / 8) tolerance
        (pbsRecursiveDepth noise tail (pbsRootInformation (fullInformation M) belief.law)
          (pbsRootDepthFallback M belief.law fallback) (pbsRootPayoff belief.law payoff) bound)
        (noise M belief.law error)

/-- The empty schedule is exactly the legal fallback, including off-path menus. -/
theorem pbsRecursiveDepth_nil (noise : PBSRecursiveDepthNoise.{u})
    {E : ExecutionProtocol.{0, u, u} (Fin 2)}
    (M : InformationModel.{0, u, u, u, u, u} E)
    [Fintype E.History] [∀ who, Fintype (E.Action who)]
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (bound : ℝ) {obs : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals obs) (tolerance : ℝ) :
    pbsRecursiveDepth noise [] M fallback payoff bound belief tolerance =
      (fun who => (cfrDInformationFallback M fallback who).toBehavioral) := rfl

/-- List induction discharges every smaller-solver accuracy premise. The final
statement contains no child equilibrium, local regret certificate, or supplied
recursive accuracy assumption. All original behavioral deviations are covered. -/
theorem pbsRecursiveDepth_isNash (noise : PBSRecursiveDepthNoise.{u})
    (noiseBound : PBSRecursiveDepthNoiseBound noise) (cuts : List Nat) :
    ∀ {E : ExecutionProtocol.{0, u, u} (Fin 2)}
      (M : InformationModel.{0, u, u, u, u, u} E)
      [Fintype E.History] [∀ who, Fintype (E.Action who)]
      (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ),
      IsZeroSum (fun h who => payoff who h) →
      ∀ bound, 0 ≤ bound → (∀ who h, |payoff who h| ≤ bound) →
      ∀ {obs} (belief : PublicBelief (fullInformation M).toInfoSignals obs) tolerance,
        0 < tolerance →
        IsNash (behavioralBeliefForm (fullInformation M) belief cuts.sum)
          (euPreferenceWithin tolerance (fun h who => payoff who h))
          (pbsRecursiveDepth noise cuts M fallback payoff bound belief tolerance) := by
  induction cuts with
  | nil =>
      intro E M _ _ fallback payoff _zeroSum bound _hb _bounded obs belief tolerance positive
      rw [isNash_iff]
      intro who replacement
      simp only [List.sum_nil, euPreferenceWithin_apply, behavioralBeliefForm,
        PublicBelief.continuationLaw_zero]
      exact le_add_of_nonneg_right positive.le
  | cons cut tail ih =>
      intro E M _ _ fallback payoff zeroSum bound hb bounded obs belief tolerance positive
      letI : Fintype (pbsRootProtocol belief.law).History := pbsRootHistoryFintype belief.law
      simp only [List.sum_cons, pbsRecursiveDepth]
      apply pbsComposedDepthProfile_isNash M belief fallback payoff zeroSum cut tail.sum
        bound _ _ tolerance hb
      · exact (pbsDepthAllocationError_pos _ tolerance positive).le
      · exact div_pos positive (by norm_num)
      · exact bounded
      · exact pbsDepthAllocation_feasible _ tolerance positive
      · intro childObs child target childPositive
        exact ih (pbsRootInformation (fullInformation M) belief.law)
          (pbsRootDepthFallback M belief.law fallback) (pbsRootPayoff belief.law payoff)
          (pbsRootPayoff_zeroSum belief.law payoff zeroSum) bound hb
          (fun who => pbsRootPayoff_abs_le belief.law payoff who bound hb (bounded who))
          child target childPositive
      · exact noiseBound M belief.law _ (pbsDepthAllocationError_pos _ tolerance positive).le

/-- A concrete, nonzero numerical perturbation uses the full allocated allowance.
It is a reference control, not an assertion about a trained predictor. -/
def pbsRecursiveAllocatedNoise : PBSRecursiveDepthNoise.{u} := by
  intro E M roots error n trunk who info
  exact error

/-- The positive-error control meets the numerical contract at every rooted level. -/
theorem pbsRecursiveAllocatedNoise_bounded :
    PBSRecursiveDepthNoiseBound (pbsRecursiveAllocatedNoise : PBSRecursiveDepthNoise.{u}) := by
  intro E M roots error nonneg n trunk who info
  exact (abs_of_nonneg nonneg).le

/-- Whenever a parent target is positive, its concrete perturbation is strictly
positive too; the accuracy proof does not replace numerical errors by zero. -/
theorem pbsRecursiveAllocatedNoise_positive
    {E : ExecutionProtocol.{0, u, u} (Fin 2)}
    (M : InformationModel.{0, u, u, u, u, u} E) (roots : FinDist E.History)
    (error : ℝ) (positive : 0 < error) (n : Nat) (trunk) (who : Fin 2) (info) :
    0 < pbsRecursiveAllocatedNoise M roots error n trunk who info := positive

end GameTheory.ReBeL
