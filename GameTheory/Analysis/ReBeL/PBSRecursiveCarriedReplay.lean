/-
# Native carried state and late-value replay for recursive children

History marginal averaging does not reset the private profile or its model
posterior. Disintegration below retains their native conditional joint law.
A late-value consumer keeps the same draw through the full remaining horizon.
-/

import GameTheory.Analysis.ReBeL.PBSRecursiveReplay
import GameTheory.Analysis.ReBeL.PBSCarriedValue

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable (noise : PBSRecursiveDepthNoise.{u}) (cuts : List Nat)
variable (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
variable (bound tolerance : ℝ) {K : Type*}

/-- Proof-side average at the same incoming model PBS. This is only a history
comparison; no deployed resolver is changed and no posterior is averaged. -/
def pbsRecursiveAverageResolver
    (plays : K → Profile (fullInformation M).behavioralSignature) :
    CarriedPublicResolver (fullInformation M) K := fun memory _ belief =>
  match belief with
  | none => FinDist.pure (plays memory)
  | some prior =>
      FinDist.pure (pbsRecursiveDepth noise cuts E M fallback payoff bound prior tolerance)

/-- Stopped and missing-belief cases remain exact. Otherwise only supported
histories use the recursive private-draw identity. -/
theorem pbsRecursiveDepthResolver_tail_eq_average
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (state : PrivateIterationState (fullInformation M) K)
    (outside : ¬ pbsCarriedCFRException M steps state) :
    carriedResolvedTail (fullInformation M)
      (pbsRecursiveDepthResolver noise cuts M fallback payoff bound tolerance plays)
      unknown who steps state =
    carriedResolvedTail (fullInformation M)
      (pbsRecursiveAverageResolver M noise cuts fallback payoff bound tolerance plays)
      unknown who steps state := by
  unfold carriedResolvedTail
  by_cases live : cfrDCutLive steps state.history = true
  · rw [if_pos live, if_pos live]
    cases stored : state.belief with
    | none => simp only [pbsRecursiveDepthResolver, pbsRecursiveAverageResolver]
    | some belief =>
        have supported : state.history ∈ belief.law.support := by
          by_contra absent
          apply outside
          refine ⟨live, ?_⟩
          simpa only [stored] using absent
        simp only [pbsRecursiveDepthResolver, pbsRecursiveAverageResolver, FinDist.pure_bind]
        exact pbsRecursiveDepthDraw_from_support M noise cuts fallback payoff bound belief
          tolerance unknown who steps state.history supported
  · rw [if_neg live, if_neg live]

/-- An averaged history followed by the native conditional profile/PBS state.
The conditional depends on the unknown opponent only on the analysis side. -/
def pbsRecursiveHistoryFirstStep
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (state : PrivateIterationState (fullInformation M) K) :
    FinDist (PrivateIterationState (fullInformation M)
      (K × Profile (fullInformation M).behavioralSignature)) :=
  let native := carriedResolvedStep (fullInformation M) plays
    (pbsRecursiveDepthResolver noise cuts M fallback payoff bound tolerance plays)
    unknown who steps state
  (carriedResolvedTail (fullInformation M)
    (pbsRecursiveAverageResolver M noise cuts fallback payoff bound tolerance plays)
    unknown who steps state).bind fun history =>
      native.condOnFibre (fun next => next.history) history

/-- Full next-state equality retains both the selected model posterior and
its private profile, so any subsequent solve can still read the actual memory. -/
theorem pbsRecursiveDepthResolver_step_eq_historyFirst
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (state : PrivateIterationState (fullInformation M) K)
    (outside : ¬ pbsCarriedCFRException M steps state) :
    carriedResolvedStep (fullInformation M) plays
      (pbsRecursiveDepthResolver noise cuts M fallback payoff bound tolerance plays)
      unknown who steps state =
    pbsRecursiveHistoryFirstStep M noise cuts fallback payoff bound tolerance plays
      unknown who steps state := by
  let native := carriedResolvedStep (fullInformation M) plays
    (pbsRecursiveDepthResolver noise cuts M fallback payoff bound tolerance plays)
    unknown who steps state
  have marginal : native.map (fun next => next.history) =
      carriedResolvedTail (fullInformation M)
        (pbsRecursiveAverageResolver M noise cuts fallback payoff bound tolerance plays)
        unknown who steps state :=
    (carriedResolvedStep_history (fullInformation M) plays
      (pbsRecursiveDepthResolver noise cuts M fallback payoff bound tolerance plays)
      unknown who steps state).trans
        (pbsRecursiveDepthResolver_tail_eq_average M noise cuts fallback payoff bound
          tolerance plays unknown who steps state outside)
  have disintegration := FinDist.eq_bind_condOnFibre native (fun next => next.history)
  rw [marginal] at disintegration
  exact disintegration

/-- Arbitrary later kernels may inspect the native model PBS and private draw.
The defect is measured under the actual incoming full-state distribution. -/
theorem pbsRecursiveHistoryFirstStep_future_error {Outcome : Type*}
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (states : FinDist (PrivateIterationState (fullInformation M) K))
    (future : PrivateIterationState (fullInformation M)
      (K × Profile (fullInformation M).behavioralSignature) → FinDist Outcome)
    (value : Outcome → ℝ) (limit : ℝ) (bounded : ∀ outcome, |value outcome| ≤ limit) :
    |((states.bind (carriedResolvedStep (fullInformation M) plays
        (pbsRecursiveDepthResolver noise cuts M fallback payoff bound tolerance plays)
        unknown who steps)).bind future).expect value -
      ((states.bind (pbsRecursiveHistoryFirstStep M noise cuts fallback payoff bound tolerance
        plays unknown who steps)).bind future).expect value| ≤
      2 * limit * states.probOf {state | pbsCarriedCFRException M steps state} := by
  rw [FinDist.bind_bind, FinDist.bind_bind]
  apply FinDist.abs_expect_bind_sub_le_of_eq_off_event
  · exact bounded
  · intro state _ outside
    exact congrArg (fun law => law.bind future)
      (pbsRecursiveDepthResolver_step_eq_historyFirst M noise cuts fallback payoff bound
        tolerance plays unknown who steps state outside)

/-- The same actual draw drives both stage fuel and late continuation.
This identifies the new value with the recomputed average, not with an
arbitrary incumbent whose Nash accuracy alone gives no such equality. -/
theorem pbsRecursiveDepthStage_selected_late_value
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps remaining : Nat)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))
    (belief : PublicBelief (fullInformation M).toInfoSignals
      (publicTrace (fullInformation M).toInfoSignals state.history.trace))
    (stored : state.belief = some belief) (live : cfrDCutLive steps state.history = true)
    (supported : state.history ∈ belief.law.support) (value : E.History → ℝ) :
    (carriedMemoryStep (fullInformation M) initial unknown who
      (pbsRecursiveDepthStage noise cuts M fallback payoff bound tolerance steps initial)
      state).expect (fun next =>
        (carriedSelectedTail (fullInformation M) initial unknown who remaining next).expect
          value) =
    ((fullInformation M).runBehavioralFrom
      (Profile.update unknown who
        (pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance who))
      (steps + remaining) state.history).expect value := by
  rw [carriedMemoryStep_selected_late_expect]
  simp only [pbsRecursiveDepthStage, if_pos live, stored, pbsRecursiveDepthResolver]
  have equal := congrArg (fun law : FinDist E.History => law.expect value)
    (pbsRecursiveDepthDraw_from_support M noise cuts fallback payoff bound belief tolerance
      unknown who (steps + remaining) state.history supported)
  simpa only [FinDist.expect_bind] using equal

/-- A replay of the identical incumbent has zero signed replacement loss.
The equality premise concerns the computed policy, not its Nash error; the
parent-table replay theorem separately identifies a concrete matching child. -/
theorem pbsRecursiveDepthStage_signedLoss_zero
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps remaining : Nat)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))
    (belief : PublicBelief (fullInformation M).toInfoSignals
      (publicTrace (fullInformation M).toInfoSignals state.history.trace))
    (stored : state.belief = some belief) (live : cfrDCutLive steps state.history = true)
    (supported : state.history ∈ belief.law.support)
    (same : carriedMemoryProfile (fullInformation M) initial state.iteration who =
      pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance who)
    (value : E.History → ℝ) :
    carriedReplacementSignedLoss (fullInformation M) initial unknown who
      (pbsRecursiveDepthStage noise cuts M fallback payoff bound tolerance steps initial)
      remaining state value = 0 := by
  unfold carriedReplacementSignedLoss carriedReplacementOutcome
  rw [FinDist.expect_bind, pbsRecursiveDepthStage_selected_late_value M noise cuts
    fallback payoff bound tolerance initial unknown who steps remaining state belief
    stored live supported value]
  simp only [carriedSelectedTail, pbsRecursiveDepthStage, same, sub_self]

end GameTheory.ReBeL
