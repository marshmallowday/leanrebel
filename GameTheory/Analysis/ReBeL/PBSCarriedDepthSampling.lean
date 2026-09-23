/-
# Native noisy depth-limited sampling at actual carried histories

The same finite parent iterates used by the rooted CFR-D value consumer are
compared with their own-reach average at each supported original history.
The full-state comparator retains the native conditional private profile and
its own propagated model PBS. It is analysis-only, not a public resolver that
resets the PBS to an average. Unsupported actual histories are charged explicitly.
-/

import GameTheory.Analysis.ReBeL.PBSCarriedDepth
import GameTheory.Analysis.ReBeL.PBSCarriedSampling

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*}
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {observations : List M.PublicSignal}

/-- The noisy depth-limited parent's actual iteration mixture agrees at each
supported original history, not only after averaging over the modeled roots.
Finite outer counts, positive child tolerance and prediction noise are unchanged. -/
theorem pbsInformationDepthCFR_sampling_from_support
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : PBSRootDepthNoise M belief.law)
    (t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (history : E.History) (supported : history ∈ belief.law.support) :
    (cfrIterationLaw t).bind (fun n => (fullInformation M).runBehavioralFrom
      (Profile.update unknown who (pbsInformationDepthCFRIterate M belief fallback payoff
        cut remaining bound loss noise n.val who)) steps history) =
      (fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationDepthCFR M belief fallback payoff
          cut remaining bound loss noise t who)) steps history := by
  exact pbsPublicBelief_sampling_from_support M belief (cfrIterationLaw t)
    (fun n => Profile.update unknown who (pbsInformationDepthCFRIterate M belief fallback
      payoff cut remaining bound loss noise n.val who))
    (Profile.update unknown who (pbsInformationDepthCFR M belief fallback payoff
      cut remaining bound loss noise t who)) steps
    (pbsInformationDepthCFR_delayed_sampling M belief fallback payoff cut remaining bound loss
      noise t unknown who steps) history supported

/-- Model and actual probabilities may differ arbitrarily within model support.
This does not assume that an unknown opponent generates the modeled posterior. -/
theorem pbsInformationDepthCFR_sampling_reweighted
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : PBSRootDepthNoise M belief.law)
    (t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (actual : FinDist E.History)
    (dominated : ∀ history ∈ actual.support, history ∈ belief.law.support) :
    actual.bind (fun history => (cfrIterationLaw t).bind (fun n =>
      (fullInformation M).runBehavioralFrom (Profile.update unknown who
        (pbsInformationDepthCFRIterate M belief fallback payoff cut remaining bound loss
          noise n.val who)) steps history)) =
      actual.bind ((fullInformation M).runBehavioralFrom (Profile.update unknown who
        (pbsInformationDepthCFR M belief fallback payoff cut remaining bound loss noise t who))
        steps) := by
  apply FinDist.bind_congr
  intro history sampled
  exact pbsInformationDepthCFR_sampling_from_support M belief fallback payoff cut remaining
    bound loss noise t unknown who steps history (dominated history sampled)

/-- Without support domination, charge the actual unsupported-root probability.
This is a derived finite-law defect bound, not a claimed vanishing safety rate. -/
theorem pbsInformationDepthCFR_actual_sampling_error
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : PBSRootDepthNoise M belief.law)
    (t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (actual : FinDist E.History) (value : E.History → ℝ) (observableBound : ℝ)
    (bounded : ∀ history, |value history| ≤ observableBound) :
    |(actual.bind (fun history => (cfrIterationLaw t).bind (fun n =>
        (fullInformation M).runBehavioralFrom (Profile.update unknown who
          (pbsInformationDepthCFRIterate M belief fallback payoff cut remaining bound loss
            noise n.val who)) steps history))).expect value -
      (actual.bind ((fullInformation M).runBehavioralFrom (Profile.update unknown who
        (pbsInformationDepthCFR M belief fallback payoff cut remaining bound loss noise t who))
        steps)).expect value| ≤
      2 * observableBound * actual.probOf {history | history ∉ belief.law.support} := by
  apply FinDist.abs_expect_bind_sub_le_of_eq_off_event
  · exact bounded
  · intro history _ outside
    exact pbsInformationDepthCFR_sampling_from_support M belief fallback payoff cut remaining
      bound loss noise t unknown who steps history (not_not.mp outside)

/-- Analysis-only averaged resolver at the same incoming PBS. This supplies a
history marginal; it is never used to replace the native profile/PBS pairing. -/
def pbsCarriedDepthAverageResolver (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSCarriedDepthNoise M) (t : Nat) [NeZero t]
    (plays : K → Profile (fullInformation M).behavioralSignature) :
    CarriedPublicResolver (fullInformation M) K :=
  fun memory _ belief =>
    match belief with
    | none => FinDist.pure (plays memory)
    | some prior => FinDist.pure (pbsInformationDepthCFR M prior fallback payoff
        cut remaining bound loss (noise prior.law) t)

/-- The support exception is the existing history/PBS event, independent of
which solver computed the profile. Stopped and missing-belief cases are exact. -/
theorem pbsCarriedDepthResolver_tail_eq_average (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSCarriedDepthNoise M) (t : Nat) [NeZero t]
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (state : PrivateIterationState (fullInformation M) K)
    (outside : ¬ pbsCarriedCFRException M steps state) :
    carriedResolvedTail (fullInformation M)
        (pbsCarriedDepthResolver M fallback payoff cut remaining bound loss noise t plays)
        unknown who steps state =
      carriedResolvedTail (fullInformation M)
        (pbsCarriedDepthAverageResolver M fallback payoff cut remaining bound loss noise t plays)
        unknown who steps state := by
  unfold carriedResolvedTail
  by_cases live : cfrDCutLive steps state.history = true
  · rw [if_pos live, if_pos live]
    cases stored : state.belief with
    | none => simp only [pbsCarriedDepthResolver, pbsCarriedDepthAverageResolver]
    | some belief =>
        have supported : state.history ∈ belief.law.support := by
          by_contra absent
          apply outside
          refine ⟨live, ?_⟩
          simpa only [stored] using absent
        simp only [pbsCarriedDepthResolver, pbsCarriedDepthAverageResolver,
          FinDist.bind_map, FinDist.pure_bind]
        exact pbsInformationDepthCFR_sampling_from_support M belief fallback payoff cut
          remaining bound loss (noise belief.law) t unknown who steps state.history supported
  · rw [if_neg live, if_neg live]

/-- Disintegrate the full native step after sampling the averaged history law.
The conditional still contains the native private profile and its model PBS.
The unknown opponent occurs only in this proof-side comparison kernel. -/
def pbsCarriedDepthHistoryFirstStep (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSCarriedDepthNoise M) (t : Nat) [NeZero t]
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (state : PrivateIterationState (fullInformation M) K) :
    FinDist (PrivateIterationState (fullInformation M)
      (K × Profile (fullInformation M).behavioralSignature)) :=
  let native := carriedResolvedStep (fullInformation M) plays
    (pbsCarriedDepthResolver M fallback payoff cut remaining bound loss noise t plays)
    unknown who steps state
  (carriedResolvedTail (fullInformation M)
    (pbsCarriedDepthAverageResolver M fallback payoff cut remaining bound loss noise t plays)
    unknown who steps state).bind fun history =>
      native.condOnFibre (fun next => next.history) history

/-- Equality is of the entire native next state, not merely the played value
or history marginal. It therefore remains usable by a later carried-PBS solve. -/
theorem pbsCarriedDepthResolver_step_eq_historyFirst
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : PBSCarriedDepthNoise M)
    (t : Nat) [NeZero t] (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (state : PrivateIterationState (fullInformation M) K)
    (outside : ¬ pbsCarriedCFRException M steps state) :
    carriedResolvedStep (fullInformation M) plays
        (pbsCarriedDepthResolver M fallback payoff cut remaining bound loss noise t plays)
        unknown who steps state =
      pbsCarriedDepthHistoryFirstStep M fallback payoff cut remaining bound loss noise t plays
        unknown who steps state := by
  let native := carriedResolvedStep (fullInformation M) plays
    (pbsCarriedDepthResolver M fallback payoff cut remaining bound loss noise t plays)
    unknown who steps state
  have marginal : native.map (fun next => next.history) =
      carriedResolvedTail (fullInformation M)
        (pbsCarriedDepthAverageResolver M fallback payoff cut remaining bound loss noise t plays)
        unknown who steps state :=
    (carriedResolvedStep_history (fullInformation M) plays
      (pbsCarriedDepthResolver M fallback payoff cut remaining bound loss noise t plays)
      unknown who steps state).trans
        (pbsCarriedDepthResolver_tail_eq_average M fallback payoff cut remaining bound loss
          noise t plays unknown who steps state outside)
  have disintegration := FinDist.eq_bind_condOnFibre native (fun next => next.history)
  rw [marginal] at disintegration
  exact disintegration

/-- Arbitrary subsequent kernels may inspect the retained private profile and
its own posterior. The actual unsupported-history probability is not discarded. -/
theorem pbsCarriedDepthHistoryFirstStep_future_error {Outcome : Type*}
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : PBSCarriedDepthNoise M)
    (t : Nat) [NeZero t] (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (states : FinDist (PrivateIterationState (fullInformation M) K))
    (future : PrivateIterationState (fullInformation M)
      (K × Profile (fullInformation M).behavioralSignature) → FinDist Outcome)
    (value : Outcome → ℝ) (observableBound : ℝ)
    (bounded : ∀ outcome, |value outcome| ≤ observableBound) :
    |((states.bind (carriedResolvedStep (fullInformation M) plays
        (pbsCarriedDepthResolver M fallback payoff cut remaining bound loss noise t plays)
        unknown who steps)).bind future).expect value -
      ((states.bind (pbsCarriedDepthHistoryFirstStep M fallback payoff cut remaining bound loss
        noise t plays unknown who steps)).bind future).expect value| ≤
      2 * observableBound * states.probOf {state | pbsCarriedCFRException M steps state} := by
  rw [FinDist.bind_bind, FinDist.bind_bind]
  apply FinDist.abs_expect_bind_sub_le_of_eq_off_event
  · exact bounded
  · intro state _ outside
    exact congrArg (fun law => law.bind future)
      (pbsCarriedDepthResolver_step_eq_historyFirst M fallback payoff cut remaining bound loss
        noise t plays unknown who steps state outside)

end GameTheory.ReBeL
