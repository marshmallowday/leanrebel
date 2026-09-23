/-
# Native carried-PBS sampling through a complete finite schedule

This connects the full-state history-first comparison to the existing
executeCarriedResolves runner. Every exceptional mass is measured under
native forward state laws. The comparator retains the native conditional
profile/posterior pairing and is analysis-only, not a public strategy.
-/

import GameTheory.Analysis.ReBeL.PBSCarriedSampling
import GameTheory.Math.Probability.FinDistSequentialError

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

/-- Distinct training horizon, execution horizon and positive iteration count
for a single native carried-PBS solve. Finiteness of the schedule is separate. -/
structure PBSCarriedCFRParameters where
  /-- Original transitions in the child's training game. -/
  trainingFuel : Nat
  /-- Actual transitions before the next solve. Zero retains the stopped rule. -/
  fuel : Nat
  /-- Number of native information-set CFR iterations. -/
  iterations : Nat
  /-- A uniform private iteration draw must have a nonempty carrier. -/
  iterations_ne_zero : iterations ≠ 0

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*}
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- A numerical schedule entry installs the already-defined native resolver;
it does not introduce a second execution or a different posterior update. -/
def pbsCarriedCFRConfiguredStage (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (parameters : PBSCarriedCFRParameters) : CarriedResolveStage (fullInformation M) K :=
  letI : NeZero parameters.iterations := ⟨parameters.iterations_ne_zero⟩
  pbsCarriedCFRStage M fallback payoff parameters.trainingFuel parameters.fuel
    parameters.iterations initial

/-- Store the native conditional profile and its own posterior in the existing
newest-first memory. Only the history marginal comes from the average. -/
def pbsCarriedCFRHistoryFirstMemoryStep (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (parameters : PBSCarriedCFRParameters)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) :
    FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) :=
  letI : NeZero parameters.iterations := ⟨parameters.iterations_ne_zero⟩
  (pbsCarriedCFRHistoryFirstStep M fallback payoff parameters.trainingFuel parameters.iterations
    (carriedMemoryProfile (fullInformation M) initial) unknown who parameters.fuel state).map
      (storeCarriedDraw (fullInformation M))

/-- Equality off the explicit sampling exception is equality of the entire
stored state, including every previous private draw and the current model PBS. -/
theorem pbsCarriedCFRConfiguredStep_eq_historyFirst
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (parameters : PBSCarriedCFRParameters)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))
    (outside : ¬ pbsCarriedCFRException M parameters.fuel state) :
    carriedMemoryStep (fullInformation M) initial unknown who
        (pbsCarriedCFRConfiguredStage M fallback payoff initial parameters) state =
      pbsCarriedCFRHistoryFirstMemoryStep M fallback payoff initial unknown who
        parameters state := by
  letI : NeZero parameters.iterations := ⟨parameters.iterations_ne_zero⟩
  exact congrArg (fun distribution => distribution.map (storeCarriedDraw (fullInformation M)))
    (pbsCarriedCFRResolver_step_eq_historyFirst M fallback payoff parameters.trainingFuel
      parameters.iterations (carriedMemoryProfile (fullInformation M) initial)
      unknown who parameters.fuel state outside)

/-- Full native state law after all scheduled canonical resolver steps. This
is only monadic composition of carriedMemoryStep; its runner identity is below. -/
def pbsCarriedCFRNativeStates (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (schedule : List PBSCarriedCFRParameters)
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))) :
    FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) :=
  states.bind (FinDist.bindSequence (fun parameters =>
    carriedMemoryStep (fullInformation M) initial unknown who
      (pbsCarriedCFRConfiguredStage M fallback payoff initial parameters)) schedule)

/-- Analysis-only comparison at EVERY stage, not just the first stage followed
by an identical native suffix. It keeps the conditional private-state coupling. -/
def pbsCarriedCFRHistoryFirstStates (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (schedule : List PBSCarriedCFRParameters)
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))) :
    FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) :=
  states.bind (FinDist.bindSequence
    (pbsCarriedCFRHistoryFirstMemoryStep M fallback payoff initial unknown who) schedule)

/-- Sum of sampling-exception probabilities under NATIVE successive state laws.
The actual unknown opponent, retained private draws and carried PBS all remain
inside these laws. This definition supplies no vanishing or asymptotic premise. -/
def pbsCarriedCFRSequenceExceptionMass (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (schedule : List PBSCarriedCFRParameters)
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))) : ℝ :=
  FinDist.sequenceEventMass (fun parameters =>
    carriedMemoryStep (fullInformation M) initial unknown who
      (pbsCarriedCFRConfiguredStage M fallback payoff initial parameters))
    (fun parameters => {state | pbsCarriedCFRException M parameters.fuel state}) schedule states

/-- Any bounded observation after any further finite kernel obeys the sum of
actual forward sampling charges. No CarriedResolveStepBounds is an assumption. -/
theorem pbsCarriedCFRSequence_future_error {Outcome : Type*}
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (schedule : List PBSCarriedCFRParameters)
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)))
    (future : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K) → FinDist Outcome)
    (value : Outcome → ℝ) (bound : ℝ) (bounded : ∀ outcome, |value outcome| ≤ bound) :
    |((pbsCarriedCFRNativeStates M fallback payoff initial unknown who schedule states).bind
        future).expect value -
      ((pbsCarriedCFRHistoryFirstStates M fallback payoff initial unknown who schedule states).bind
        future).expect value| ≤
      2 * bound * pbsCarriedCFRSequenceExceptionMass M fallback payoff initial unknown who
        schedule states := by
  apply FinDist.abs_expect_bindSequence_sub_le_of_eq_off_event
  · intro parameters state outside
    exact pbsCarriedCFRConfiguredStep_eq_historyFirst M fallback payoff initial unknown who
      parameters state outside
  · exact bounded

/-- The native state composition is exactly the existing recursive runner
before its final selected continuation, not a substitute averaged-policy run. -/
theorem pbsCarriedCFRSequence_execute
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (schedule : List PBSCarriedCFRParameters)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) :
    executeCarriedResolves (fullInformation M) initial unknown who finalFuel
        (schedule.map (pbsCarriedCFRConfiguredStage M fallback payoff initial)) state =
      (FinDist.bindSequence (fun parameters =>
        carriedMemoryStep (fullInformation M) initial unknown who
          (pbsCarriedCFRConfiguredStage M fallback payoff initial parameters)) schedule state).bind
        (carriedSelectedTail (fullInformation M) initial unknown who finalFuel) := by
  induction schedule generalizing state with
  | nil =>
      simp only [List.map_nil, executeCarriedResolves, FinDist.bindSequence, FinDist.pure_bind]
  | cons parameters schedule ih =>
      simp only [List.map_cons, executeCarriedResolves, FinDist.bindSequence, FinDist.bind_bind]
      apply FinDist.bind_congr
      intro next _
      exact ih next

/-- The actual finite recursive execution is compared with history-first
sampling at every solve. The residual event mass is not dropped or assumed small. -/
theorem pbsCarriedCFRSequence_execute_error
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (schedule : List PBSCarriedCFRParameters)
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)))
    (value : E.History → ℝ) (bound : ℝ) (bounded : ∀ history, |value history| ≤ bound) :
    |(states.bind (executeCarriedResolves (fullInformation M) initial unknown who finalFuel
        (schedule.map (pbsCarriedCFRConfiguredStage M fallback payoff initial)))).expect value -
      ((pbsCarriedCFRHistoryFirstStates M fallback payoff initial unknown who schedule states).bind
        (carriedSelectedTail (fullInformation M) initial unknown who finalFuel)).expect value| ≤
      2 * bound * pbsCarriedCFRSequenceExceptionMass M fallback payoff initial unknown who
        schedule states := by
  have same :
      states.bind (executeCarriedResolves (fullInformation M) initial unknown who finalFuel
          (schedule.map (pbsCarriedCFRConfiguredStage M fallback payoff initial))) =
        (pbsCarriedCFRNativeStates M fallback payoff initial unknown who schedule states).bind
          (carriedSelectedTail (fullInformation M) initial unknown who finalFuel) := by
    simp only [pbsCarriedCFRNativeStates, FinDist.bind_bind]
    apply FinDist.bind_congr
    intro state _
    exact pbsCarriedCFRSequence_execute M fallback payoff initial unknown who finalFuel schedule state
  rw [same]
  exact pbsCarriedCFRSequence_future_error M fallback payoff initial unknown who
    schedule states (carriedSelectedTail (fullInformation M) initial unknown who finalFuel)
    value bound bounded

/-- A resumed suffix receives exactly the full native checkpoint distribution,
including the carried PBS and all earlier private choices. -/
theorem pbsCarriedCFRNativeStates_append
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (before after : List PBSCarriedCFRParameters)
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))) :
    pbsCarriedCFRNativeStates M fallback payoff initial unknown who (before ++ after) states =
      pbsCarriedCFRNativeStates M fallback payoff initial unknown who after
        (pbsCarriedCFRNativeStates M fallback payoff initial unknown who before states) := by
  simp only [pbsCarriedCFRNativeStates, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro state _
  exact FinDist.bindSequence_append _ before after state

end GameTheory.ReBeL
