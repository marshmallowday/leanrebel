/-
# First unsupported-history hit in noisy carried-depth execution

Every step is the constructed depth-limited solver at its incoming model PBS.
The analysis charges only the first live unsupported history. It keeps the
native private profile/PBS coupling and uses no model/actual posterior equality.
A smaller sampling allowance alone is not a recursive security theorem.
The refined exit law retains the native private state and its unexecuted suffix.
-/

import GameTheory.Analysis.ReBeL.PBSCarriedDepthSampling
import GameTheory.Math.Probability.FinDistFirstHit

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*}
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- Probability that the actual native schedule ever presents a live history
outside an existing carried model's support. Missing beliefs and stopped stages
are not exceptions. All native choices before the first hit are preserved. -/
def pbsCarriedDepthFirstHitProbability (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (schedule : List (PBSCarriedDepthParameters M))
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))) : ℝ :=
  FinDist.sequenceFirstHitProbability (fun parameters =>
    carriedMemoryStep (fullInformation M) initial unknown who
      (pbsCarriedDepthConfiguredStage M fallback payoff initial parameters))
    (fun parameters => {state | pbsCarriedCFRException M parameters.fuel state}) schedule states

/-- The defect is a derived probability in the unit interval, not an arbitrary allowance. -/
theorem pbsCarriedDepthFirstHitProbability_bounds
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (schedule : List (PBSCarriedDepthParameters M))
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))) :
    0 ≤ pbsCarriedDepthFirstHitProbability M fallback payoff initial unknown who schedule states ∧
      pbsCarriedDepthFirstHitProbability M fallback payoff initial unknown who
        schedule states ≤ 1 :=
  ⟨FinDist.sequenceFirstHitProbability_nonneg _ _ _ _,
    FinDist.sequenceFirstHitProbability_le_one _ _ _ _⟩

/-- This probability never exceeds the existing sum of native exceptional visits. -/
theorem pbsCarriedDepthFirstHitProbability_le_visits
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (schedule : List (PBSCarriedDepthParameters M))
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))) :
    pbsCarriedDepthFirstHitProbability M fallback payoff initial unknown who schedule states ≤
      min 1 (pbsCarriedDepthSequenceExceptionMass M fallback payoff initial unknown who
        schedule states) :=
  FinDist.sequenceFirstHitProbability_le_min _ _ _ _

/-- Arbitrary future kernels may read the complete native private state. Error
is charged once at the first unsupported history, rather than at every later visit. -/
theorem pbsCarriedDepthFirstHit_future_error {Outcome : Type*}
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (schedule : List (PBSCarriedDepthParameters M))
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)))
    (future : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K) → FinDist Outcome)
    (value : Outcome → ℝ) (observableBound : ℝ)
    (bounded : ∀ outcome, |value outcome| ≤ observableBound) :
    |((pbsCarriedDepthNativeStates M fallback payoff initial unknown who schedule states).bind
        future).expect value -
      ((pbsCarriedDepthHistoryFirstStates M fallback payoff initial unknown who
        schedule states).bind future).expect value| ≤
      2 * observableBound * pbsCarriedDepthFirstHitProbability M fallback payoff initial
        unknown who schedule states := by
  apply FinDist.abs_expect_bindSequence_sub_le_firstHit
  · intro parameters state outside
    exact pbsCarriedDepthConfiguredStep_eq_historyFirst M fallback payoff initial unknown who
      parameters state outside
  · exact bounded

/-- The same first-hit charge applies to the existing finite recursive runner
and its final retained-policy continuation. No alternative execution is substituted. -/
theorem pbsCarriedDepthFirstHit_execute_error
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (schedule : List (PBSCarriedDepthParameters M))
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)))
    (value : E.History → ℝ) (observableBound : ℝ)
    (bounded : ∀ history, |value history| ≤ observableBound) :
    |(states.bind (executeCarriedResolves (fullInformation M) initial unknown who finalFuel
        (schedule.map (pbsCarriedDepthConfiguredStage M fallback payoff initial)))).expect value -
      ((pbsCarriedDepthHistoryFirstStates M fallback payoff initial unknown who
        schedule states).bind
        (carriedSelectedTail (fullInformation M) initial unknown who finalFuel)).expect value| ≤
      2 * observableBound * pbsCarriedDepthFirstHitProbability M fallback payoff initial
        unknown who schedule states := by
  have same :
      states.bind (executeCarriedResolves (fullInformation M) initial unknown who finalFuel
          (schedule.map (pbsCarriedDepthConfiguredStage M fallback payoff initial))) =
        (pbsCarriedDepthNativeStates M fallback payoff initial unknown who schedule states).bind
          (carriedSelectedTail (fullInformation M) initial unknown who finalFuel) := by
    simp only [pbsCarriedDepthNativeStates, FinDist.bind_bind]
    apply FinDist.bind_congr
    intro state _
    exact pbsCarriedDepthSequence_execute M fallback payoff initial unknown who
      finalFuel schedule state
  rw [same]
  exact pbsCarriedDepthFirstHit_future_error M fallback payoff initial unknown who
    schedule states (carriedSelectedTail (fullInformation M) initial unknown who finalFuel)
    value observableBound bounded

/-- An optional first-exit witness retains the entire private memory and model
PBS, together with the suffix starting at the still-unexecuted exceptional stage. -/
abbrev PBSCarriedDepthExit (Memory : Type*) :=
  Option (List (PBSCarriedDepthParameters M) ×
    PrivateIterationState (fullInformation M) (CarriedResolveMemory (fullInformation M) Memory))

/-- Native first-exit witnesses; no independent resampling or posterior reset occurs. -/
def pbsCarriedDepthFirstExit (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (schedule : List (PBSCarriedDepthParameters M))
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))) : FinDist (PBSCarriedDepthExit M K) :=
  states.bind (FinDist.sequenceFirstExit (fun parameters =>
    carriedMemoryStep (fullInformation M) initial unknown who
      (pbsCarriedDepthConfiguredStage M fallback payoff initial parameters))
    (fun parameters => {state | pbsCarriedCFRException M parameters.fuel state}) schedule)

/-- Signed continuation discrepancy at a native witness, computed from the
actual remaining kernels. It is not assumed small or equal to a child Nash error. -/
def pbsCarriedDepthFirstExitValue {Outcome : Type*}
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (future : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K) → FinDist Outcome)
    (value : Outcome → ℝ) : PBSCarriedDepthExit M K → ℝ :=
  FinDist.sequenceFirstExitValue (fun parameters =>
    carriedMemoryStep (fullInformation M) initial unknown who
      (pbsCarriedDepthConfiguredStage M fallback payoff initial parameters))
    (pbsCarriedDepthHistoryFirstMemoryStep M fallback payoff initial unknown who) future value

/-- The refined witness has exactly the previously proved first-hit probability. -/
theorem pbsCarriedDepthFirstExit_hitProbability
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (schedule : List (PBSCarriedDepthParameters M))
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))) :
    ((pbsCarriedDepthFirstExit M fallback payoff initial unknown who schedule states).map
        Option.isSome).prob true =
      pbsCarriedDepthFirstHitProbability M fallback payoff initial unknown who schedule states :=
  FinDist.sequenceFirstExit_hitProbability _ _ _ _

/-- Complete native/history-first payoff discrepancy is the signed expectation
of the computed suffix discrepancy at actual first-exit witnesses. -/
theorem pbsCarriedDepthFirstExit_future_identity {Outcome : Type*}
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (schedule : List (PBSCarriedDepthParameters M))
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)))
    (future : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K) → FinDist Outcome)
    (value : Outcome → ℝ) :
    ((pbsCarriedDepthNativeStates M fallback payoff initial unknown who schedule states).bind
        future).expect value -
      ((pbsCarriedDepthHistoryFirstStates M fallback payoff initial unknown who
        schedule states).bind future).expect value =
      (pbsCarriedDepthFirstExit M fallback payoff initial unknown who schedule states).expect
        (pbsCarriedDepthFirstExitValue M fallback payoff initial unknown who future value) := by
  apply FinDist.expect_bindSequence_sub_eq_firstExit
  intro parameters state outside
  exact pbsCarriedDepthConfiguredStep_eq_historyFirst M fallback payoff initial unknown who
    parameters state outside

/-- State-dependent sampling charge derived from the solver's actual suffixes.
It retains possible support defects and is not a recursive-security certificate. -/
def pbsCarriedDepthFirstExitCharge {Outcome : Type*}
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (schedule : List (PBSCarriedDepthParameters M))
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)))
    (future : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K) → FinDist Outcome)
    (value : Outcome → ℝ) : ℝ :=
  (pbsCarriedDepthFirstExit M fallback payoff initial unknown who schedule states).expect
    (fun witness =>
      |pbsCarriedDepthFirstExitValue M fallback payoff initial unknown who future value witness|)

/-- A derived, state-dependent error bound for any future reading the full private state. -/
theorem pbsCarriedDepthFirstExit_future_error {Outcome : Type*}
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (schedule : List (PBSCarriedDepthParameters M))
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)))
    (future : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K) → FinDist Outcome)
    (value : Outcome → ℝ) :
    |((pbsCarriedDepthNativeStates M fallback payoff initial unknown who schedule states).bind
        future).expect value -
      ((pbsCarriedDepthHistoryFirstStates M fallback payoff initial unknown who
        schedule states).bind future).expect value| ≤
      pbsCarriedDepthFirstExitCharge M fallback payoff initial unknown who schedule states
        future value := by
  apply FinDist.abs_expect_bindSequence_sub_le_firstExit
  intro parameters state outside
  exact pbsCarriedDepthConfiguredStep_eq_historyFirst M fallback payoff initial unknown who
    parameters state outside

/-- The computed charge cannot exceed the old uniform first-hit allowance. -/
theorem pbsCarriedDepthFirstExitCharge_le_firstHit {Outcome : Type*}
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (schedule : List (PBSCarriedDepthParameters M))
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)))
    (future : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K) → FinDist Outcome)
    (value : Outcome → ℝ) (observableBound : ℝ)
    (bounded : ∀ outcome, |value outcome| ≤ observableBound) :
    pbsCarriedDepthFirstExitCharge M fallback payoff initial unknown who schedule states
        future value ≤
      2 * observableBound * pbsCarriedDepthFirstHitProbability M fallback payoff initial
        unknown who schedule states :=
  FinDist.firstExitValue_expect_abs_le_firstHit _ _ _ _ _ _ bounded _ _

end GameTheory.ReBeL
