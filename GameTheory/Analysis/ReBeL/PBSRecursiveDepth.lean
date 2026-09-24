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
import GameTheory.Analysis.ReBeL.CFRDRecursivePlay

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u

/-- A prediction family reads only the modeled query and its allocated error.
The protocol is explicit so the same family can be used at every rooted level. -/
abbrev PBSRecursiveDepthNoise :=
  (E : ExecutionProtocol.{0, u, u} (Fin 2)) →
  (M : InformationModel.{0, u, u, u, u, u} E) →
  (roots : FinDist E.History) → ℝ → PBSRootDepthNoise M roots

/-- A numerical approximation contract, separate from the algorithm and its
Nash theorem. It is not a claim that an arbitrary learned network satisfies it. -/
def PBSRecursiveDepthNoiseBound (noise : PBSRecursiveDepthNoise.{u}) : Prop :=
  ∀ {E : ExecutionProtocol.{0, u, u} (Fin 2)}
    (M : InformationModel.{0, u, u, u, u, u} E) (roots : FinDist E.History)
    error, 0 ≤ error → ∀ n trunk who info, |noise E M roots error n trunk who info| ≤ error

/-- Computational data only: neither a Nash witness nor a correctness proof
is an argument of a recursive solver. The changing protocol is explicit. -/
abbrev PBSRecursiveDepthFamily :=
  (E : ExecutionProtocol.{0, u, u} (Fin 2)) →
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
        (pbsRecursiveDepth noise tail (pbsRootProtocol belief.law)
          (pbsRootInformation (fullInformation M) belief.law)
          (pbsRootDepthFallback M belief.law fallback) (pbsRootPayoff belief.law payoff) bound)
        (noise E M belief.law error)

/-- The empty schedule is exactly the legal fallback, including off-path menus. -/
theorem pbsRecursiveDepth_nil (noise : PBSRecursiveDepthNoise.{u})
    {E : ExecutionProtocol.{0, u, u} (Fin 2)}
    (M : InformationModel.{0, u, u, u, u, u} E)
    [Fintype E.History] [∀ who, Fintype (E.Action who)]
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (bound : ℝ) {obs : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals obs) (tolerance : ℝ) :
    pbsRecursiveDepth noise [] E M fallback payoff bound belief tolerance =
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
          (pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance) := by
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
      let _ : Fintype (pbsRootProtocol belief.law).History := pbsRootHistoryFintype belief.law
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
    0 < pbsRecursiveAllocatedNoise E M roots error n trunk who info := positive

section Sampling

variable (noise : PBSRecursiveDepthNoise.{u}) (cuts : List Nat)
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
variable (bound : ℝ) {obs : List M.PublicSignal}

/-- Draw an actual finite parent iterate whose children are the recursive tail.
The empty schedule is a pure fallback, not a uniform draw from an empty range. -/
def pbsRecursiveDepthDraw
    (belief : PublicBelief (fullInformation M).toInfoSignals obs) (tolerance : ℝ) :
    FinDist (Profile (fullInformation M).behavioralSignature) := by
  cases cuts with
  | nil => exact FinDist.pure (pbsRecursiveDepth noise [] E M fallback payoff bound belief tolerance)
  | cons cut tail =>
      letI : Fintype (pbsRootProtocol belief.law).History := pbsRootHistoryFintype belief.law
      let error := pbsDepthAllocationError
        (pbsRootDepthErrorFactor M belief.law fallback cut tail.sum) tolerance
      exact pbsComposedDepthDraw M belief fallback payoff cut tail.sum bound error
        (tolerance / 8) tolerance
        (pbsRecursiveDepth noise tail (pbsRootProtocol belief.law)
          (pbsRootInformation (fullInformation M) belief.law)
          (pbsRootDepthFallback M belief.law fallback) (pbsRootPayoff belief.law payoff) bound)
        (noise E M belief.law error)

/-- All original history observables agree with the recursively computed
average against every fixed unknown opponent. No per-draw Nash premise is used. -/
theorem pbsRecursiveDepthDraw_law
    (belief : PublicBelief (fullInformation M).toInfoSignals obs) (tolerance : ℝ)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat) :
    (pbsRecursiveDepthDraw noise cuts M fallback payoff bound belief tolerance).bind
      (fun chosen => belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (chosen who)) steps)) =
      belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance who)) steps) := by
  cases cuts with
  | nil => simp only [pbsRecursiveDepthDraw, FinDist.pure_bind]
  | cons cut tail =>
      let _ : Fintype (pbsRootProtocol belief.law).History := pbsRootHistoryFintype belief.law
      exact pbsComposedDepthDraw_law M belief fallback payoff cut tail.sum bound _ _ tolerance
        _ _ unknown who steps

/-- The exact same private parent family supplies value expectations. -/
theorem pbsRecursiveDepthDraw_value
    (belief : PublicBelief (fullInformation M).toInfoSignals obs) (tolerance : ℝ)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (value : E.History → ℝ) :
    (pbsRecursiveDepthDraw noise cuts M fallback payoff bound belief tolerance).expect
      (fun chosen => (belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (chosen who)) steps)).expect value) =
      (belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance who)) steps)).expect
        value := by
  have equal := congrArg (fun law : FinDist E.History => law.expect value)
    (pbsRecursiveDepthDraw_law noise cuts M fallback payoff bound belief tolerance unknown who steps)
  simpa only [FinDist.expect_bind] using equal

variable {K : Type*}

/-- A canonical resolver reads the incoming model PBS, never the actual hidden
history or unknown-opponent policy. It retains the old strategy when no PBS exists. -/
def pbsRecursiveDepthResolver (tolerance : ℝ)
    (plays : K → Profile (fullInformation M).behavioralSignature) :
    CarriedPublicResolver (fullInformation M) K := fun memory _ belief =>
  match belief with
  | none => FinDist.pure (plays memory)
  | some prior => pbsRecursiveDepthDraw noise cuts M fallback payoff bound prior tolerance

/-- Missing beliefs do not fabricate a new solver root. -/
theorem pbsRecursiveDepthResolver_none (tolerance : ℝ)
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (memory : K) (observations : List M.PublicSignal) :
    pbsRecursiveDepthResolver noise cuts M fallback payoff bound tolerance plays memory
      observations none = FinDist.pure (plays memory) := rfl

/-- The selected profile remains paired with the posterior it actually produces.
This identity is valid even at actual histories outside the modeled support. -/
theorem pbsRecursiveDepthResolver_step_some (tolerance : ℝ)
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (state : PrivateIterationState (fullInformation M) K)
    (belief : PublicBelief (fullInformation M).toInfoSignals
      (publicTrace (fullInformation M).toInfoSignals state.history.trace))
    (stored : state.belief = some belief) (live : cfrDCutLive steps state.history = true) :
    carriedResolvedStep (fullInformation M) plays
      (pbsRecursiveDepthResolver noise cuts M fallback payoff bound tolerance plays)
      unknown who steps state =
      (pbsRecursiveDepthDraw noise cuts M fallback payoff bound belief tolerance).bind
        (fun chosen => ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who (chosen who)) steps state.history).map
            (resolvedNextState (fullInformation M) state chosen steps)) := by
  simp only [carriedResolvedStep, if_pos live, stored, pbsRecursiveDepthResolver]

/-- Install the actual recursive solver in the existing finite memory runner;
execution fuel is separate from the training cut schedule. -/
def pbsRecursiveDepthStage (tolerance : ℝ) (steps : Nat)
    (initial : K → Profile (fullInformation M).behavioralSignature) :
    CarriedResolveStage (fullInformation M) K where
  fuel := steps
  resolver := pbsRecursiveDepthResolver noise cuts M fallback payoff bound tolerance
    (carriedMemoryProfile (fullInformation M) initial)

/-- No fresh solve or draw is performed at zero execution fuel. -/
theorem pbsRecursiveDepthStage_zero_history (tolerance : ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) :
    (carriedMemoryStep (fullInformation M) initial unknown who
      (pbsRecursiveDepthStage noise cuts M fallback payoff bound tolerance 0 initial) state).map
        (fun next => next.history) = FinDist.pure state.history := by
  rw [carriedMemoryStep_history]
  simp only [pbsRecursiveDepthStage, carriedResolvedTail, cfrDCutLive_zero,
    Bool.false_eq_true, if_false]

end Sampling

end GameTheory.ReBeL
