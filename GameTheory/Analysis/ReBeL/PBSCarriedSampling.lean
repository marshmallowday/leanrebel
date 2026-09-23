/-
# Actual child iterations solved from a carried public belief

A live resolver consumes the stored joint PBS as the NEW root game. Its
private draw is from that root's actual information-set CFR iterations, not
from pure plans of an old averaged profile. The selected profile and its
own model posterior remain paired in the canonical next-state law.
-/

import GameTheory.Analysis.ReBeL.PBSSupportedSampling
import GameTheory.Analysis.ReBeL.CFRDRecursivePlay
import GameTheory.Math.Probability.FinDistEventError

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*}

/-- Only live states with an existing model belief but an unsupported actual
history require the sampling defect allowance. Missing beliefs retain the old
policy in BOTH executions and are not silently treated as sampled posteriors. -/
def pbsCarriedCFRException (steps : Nat)
    (state : PrivateIterationState (fullInformation M) K) : Prop :=
  cfrDCutLive steps state.history = true ∧
    match state.belief with
    | none => False
    | some belief => state.history ∉ belief.law.support

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- Solve the actual carried PBS, then draw one of its computed CFR iterates.
The old private memory is consulted only if the model has no posterior. -/
def pbsCarriedCFRResolver (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (trainingFuel t : Nat) [NeZero t]
    (plays : K → Profile (fullInformation M).behavioralSignature) :
    CarriedPublicResolver (fullInformation M) K :=
  fun memory _ belief =>
    match belief with
    | none => FinDist.pure (plays memory)
    | some prior => (cfrIterationLaw t).map fun n =>
        pbsInformationCFRIterate M prior fallback payoff trainingFuel n.val

/-- The comparison solves the SAME carried PBS and takes its own-reach
average. It does not update a posterior using an averaged private draw. -/
def pbsCarriedCFRAverageResolver (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (trainingFuel t : Nat) [NeZero t]
    (plays : K → Profile (fullInformation M).behavioralSignature) :
    CarriedPublicResolver (fullInformation M) K :=
  fun memory _ belief =>
    match belief with
    | none => FinDist.pure (plays memory)
    | some prior => FinDist.pure (pbsInformationCFR M prior fallback payoff trainingFuel t)

/-- No model posterior means no newly fabricated child game. -/
theorem pbsCarriedCFRResolver_none (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (trainingFuel t : Nat) [NeZero t]
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (memory : K) (observations : List M.PublicSignal) :
    pbsCarriedCFRResolver M fallback payoff trainingFuel t plays memory observations none =
      FinDist.pure (plays memory) := rfl

/-- A supplied carried belief is used directly, independently of the prior
family. This equation preserves the actual iteration law and all its indices. -/
theorem pbsCarriedCFRResolver_some (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (trainingFuel t : Nat) [NeZero t]
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (memory : K) {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations) :
    pbsCarriedCFRResolver M fallback payoff trainingFuel t plays memory observations
        (some belief) =
      (cfrIterationLaw t).map (fun n =>
        pbsInformationCFRIterate M belief fallback payoff trainingFuel n.val) := rfl

/-- Against arbitrary fixed opponents the complete law at the model root
is the native child's own-reach averaged law, with finite t unchanged. -/
theorem pbsCarriedCFRResolver_model_law (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (trainingFuel t : Nat) [NeZero t]
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (memory : K) {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat) :
    (pbsCarriedCFRResolver M fallback payoff trainingFuel t plays memory observations
        (some belief)).bind (fun chosen => belief.law.bind
          ((fullInformation M).runBehavioralFrom
            (Profile.update unknown who (chosen who)) steps)) =
      belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (pbsInformationCFR M belief fallback payoff trainingFuel t who)) steps) := by
  rw [pbsCarriedCFRResolver_some, FinDist.bind_map]
  exact pbsInformationCFR_sampling_law M belief fallback payoff trainingFuel t unknown who steps

/-- The FULL next-state law retains the sampled child and updates the stored
PBS with that child, not with the average. This equation applies even when the
actual hidden history lies outside the stored model's support. -/
theorem pbsCarriedCFRResolver_step_some (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (trainingFuel t : Nat) [NeZero t]
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (state : PrivateIterationState (fullInformation M) K)
    (belief : PublicBelief (fullInformation M).toInfoSignals
      (publicTrace (fullInformation M).toInfoSignals state.history.trace))
    (stored : state.belief = some belief) (live : cfrDCutLive steps state.history = true) :
    carriedResolvedStep (fullInformation M) plays
      (pbsCarriedCFRResolver M fallback payoff trainingFuel t plays) unknown who steps state =
    (cfrIterationLaw t).bind (fun n =>
      ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (pbsInformationCFRIterate M belief fallback payoff trainingFuel n.val who))
        steps state.history).map (resolvedNextState (fullInformation M) state
          (pbsInformationCFRIterate M belief fallback payoff trainingFuel n.val) steps)) := by
  simp only [carriedResolvedStep, if_pos live, stored, pbsCarriedCFRResolver,
    FinDist.bind_map]

/-- History-law equality is justified exactly outside the explicit exception.
No equality of the two model posterior laws is asserted by this theorem. -/
theorem pbsCarriedCFRResolver_tail_eq_average (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (trainingFuel t : Nat) [NeZero t]
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (state : PrivateIterationState (fullInformation M) K)
    (outside : ¬ pbsCarriedCFRException M steps state) :
    carriedResolvedTail (fullInformation M)
        (pbsCarriedCFRResolver M fallback payoff trainingFuel t plays) unknown who steps state =
      carriedResolvedTail (fullInformation M)
        (pbsCarriedCFRAverageResolver M fallback payoff trainingFuel t plays)
        unknown who steps state := by
  unfold carriedResolvedTail
  by_cases live : cfrDCutLive steps state.history = true
  · rw [if_pos live, if_pos live]
    cases stored : state.belief with
    | none => simp only [pbsCarriedCFRResolver, pbsCarriedCFRAverageResolver, stored]
    | some belief =>
        have supported : state.history ∈ belief.law.support := by
          by_contra absent
          apply outside
          refine ⟨live, ?_⟩
          simpa only [stored] using absent
        simp only [pbsCarriedCFRResolver, pbsCarriedCFRAverageResolver, stored,
          FinDist.bind_map, FinDist.pure_bind]
        exact pbsInformationCFR_sampling_from_support M belief fallback payoff
          trainingFuel t unknown who steps state.history supported
  · rw [if_neg live, if_neg live]

/-- No support domination is required for the ACTUAL incoming state law.
Every exceptional live state is charged at most twice the observable bound.
This is one-step sampling error, not a recursive safety assumption. -/
theorem pbsCarriedCFRResolver_actual_error (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (trainingFuel t : Nat) [NeZero t]
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (states : FinDist (PrivateIterationState (fullInformation M) K))
    (value : E.History → ℝ) (bound : ℝ) (bounded : ∀ history, |value history| ≤ bound) :
    |(states.bind (carriedResolvedTail (fullInformation M)
        (pbsCarriedCFRResolver M fallback payoff trainingFuel t plays)
        unknown who steps)).expect value -
      (states.bind (carriedResolvedTail (fullInformation M)
        (pbsCarriedCFRAverageResolver M fallback payoff trainingFuel t plays)
        unknown who steps)).expect value| ≤
      2 * bound * states.probOf {state | pbsCarriedCFRException M steps state} := by
  apply FinDist.abs_expect_bind_sub_le_of_eq_off_event
  · exact bounded
  · intro state _ outside
    exact pbsCarriedCFRResolver_tail_eq_average M fallback payoff trainingFuel t plays
      unknown who steps state outside

/-- Install the native carried-belief resolver in the EXISTING finite recursive
runner. Every stage consumes its incoming posterior; none resets the game.
The accumulated private profile list is retained by carriedMemoryStep. -/
def pbsCarriedCFRStage (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (trainingFuel steps t : Nat) [NeZero t]
    (initial : K → Profile (fullInformation M).behavioralSignature) :
    CarriedResolveStage (fullInformation M) K where
  fuel := steps
  resolver := pbsCarriedCFRResolver M fallback payoff trainingFuel t
    (carriedMemoryProfile (fullInformation M) initial)

/-- Zero-fuel stages make no solver query and do not alter history or belief.
The pre-existing stopped-memory convention is kept rather than redefined. -/
theorem pbsCarriedCFRStage_zero_history (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (trainingFuel t : Nat) [NeZero t]
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) :
    (carriedMemoryStep (fullInformation M) initial unknown who
      (pbsCarriedCFRStage M fallback payoff trainingFuel 0 t initial) state).map
        (fun next => next.history) = FinDist.pure state.history := by
  rw [carriedMemoryStep_history]
  simp only [pbsCarriedCFRStage, carriedResolvedTail, cfrDCutLive_zero,
    Bool.false_eq_true, if_false]

end GameTheory.ReBeL
