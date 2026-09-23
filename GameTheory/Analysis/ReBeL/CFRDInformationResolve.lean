/-
# Fresh information-set solves from carried public beliefs

The actual resolver runs CFR at its stored joint model PBS and draws a new
private iteration with the posterior-dependent conditional budget. Missing
model support retains the incumbent policy; it never invents a posterior.
The existing referee carries the selected profile and updates the stored PBS.
This construction alone does not prove recursive safety on supported branches.
-/

import GameTheory.Analysis.ReBeL.CFRDInformationSampling
import GameTheory.Analysis.ReBeL.CFRDRecursivePlay

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {K : Type*}

/-- A fresh private draw from the actual information-set recurrence at this PBS.
The count is computed from the joint posterior, not a global fixed child count. -/
def cfrDInformationResolveDraw {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel : Nat) (bound loss : ℝ) :
    FinDist (Profile (fullInformation M).behavioralSignature) :=
  (cfrIterationLaw (pbsInformationConditionalRounds M belief fuel bound loss)).map
    (fun n => pbsInformationCFRIterate M belief fallback payoff fuel n.val)

/-- Drawing a child and retaining it for the whole continuation realizes its
computed average against any fixed opponent on the supplied model root law.
This is not an equality of the model and actual unknown-opponent posteriors. -/
theorem cfrDInformationResolveDraw_law {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel : Nat) (bound loss : ℝ)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) :
    (cfrDInformationResolveDraw M belief fallback payoff fuel bound loss).bind
        (fun chosen => belief.law.bind ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who (chosen who)) steps)) =
      belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (pbsInformationConditionalProfile M belief fallback fuel
            (fun h player => payoff player h) bound loss who)) steps) := by
  rw [cfrDInformationResolveDraw, FinDist.bind_map]
  exact pbsInformationConditionalSample_eq M belief fallback fuel
    (fun h player => payoff player h) bound loss unknown who steps

/-- Public data and retained private memory are the only resolver inputs.
A supported stored PBS is solved afresh; absence retains the current policy.
No hidden history, actual opponent, or safety certificate is an input. -/
def cfrDInformationResolver
    (incumbent : K → Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel : Nat) (bound loss : ℝ) : CarriedPublicResolver (fullInformation M) K :=
  fun memory _ belief => match belief with
    | none => FinDist.pure (incumbent memory)
    | some prior => cfrDInformationResolveDraw M prior fallback payoff fuel bound loss

/-- An unavailable model posterior selects an explicit incumbent fallback. -/
theorem cfrDInformationResolver_none
    (incumbent : K → Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel : Nat) (bound loss : ℝ) (memory : K) (observations : List M.PublicSignal) :
    cfrDInformationResolver M incumbent fallback payoff fuel bound loss memory
      observations none = FinDist.pure (incumbent memory) := rfl

/-- Available beliefs really invoke the information-set child learner, not
another draw of the incumbent's old policy family. -/
theorem cfrDInformationResolver_some
    (incumbent : K → Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel : Nat) (bound loss : ℝ) (memory : K) {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations) :
    cfrDInformationResolver M incumbent fallback payoff fuel bound loss memory
      observations (some belief) =
        cfrDInformationResolveDraw M belief fallback payoff fuel bound loss := rfl

/-- Training covers all remaining play, while this stage executes only its
own interval. The canonical step retains the draw and updates the stored PBS. -/
def cfrDInformationResolveStage
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (trainFuel stepFuel : Nat) (bound loss : ℝ) :
    CarriedResolveStage (fullInformation M) K where
  fuel := stepFuel
  resolver := cfrDInformationResolver M (carriedMemoryProfile (fullInformation M) initial)
    fallback payoff trainFuel bound loss

/-- A finite public re-solving schedule. Every stage learns for its entire
remaining horizon, including the final retained continuation. -/
def cfrDInformationResolveStages
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (bound loss : ℝ) (finalFuel : Nat) : List Nat →
    List (CarriedResolveStage (fullInformation M) K)
  | [] => []
  | fuel :: schedule =>
      cfrDInformationResolveStage M initial fallback payoff
        (fuel + schedule.sum + finalFuel) fuel bound loss ::
      cfrDInformationResolveStages initial fallback payoff bound loss finalFuel schedule

/-- Execution fuel is exactly the finite schedule plus the final continuation;
zero-length intervals contribute no fuel and use the existing no-query rule. -/
theorem cfrDInformationResolveStages_fuel
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (bound loss : ℝ) (finalFuel : Nat) (schedule : List Nat) :
    carriedResolveFuel (fullInformation M) finalFuel
        (cfrDInformationResolveStages M initial fallback payoff bound loss finalFuel schedule) =
      schedule.sum + finalFuel := by
  induction schedule with
  | nil => simp only [cfrDInformationResolveStages, carriedResolveFuel, List.sum_nil, zero_add]
  | cons fuel schedule ih =>
      simp only [cfrDInformationResolveStages, carriedResolveFuel,
        cfrDInformationResolveStage, List.sum_cons, ih, Nat.add_assoc]

/-- Proof normal form of the existing memory bookkeeping after a missing-PBS
step. This does not introduce another runner or alter the canonical state type. -/
def cfrDInformationMissingNext
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) (history : E.History) :
    PrivateIterationState (fullInformation M) (CarriedResolveMemory (fullInformation M) K) where
  iteration := (state.iteration.1,
    carriedMemoryProfile (fullInformation M) initial state.iteration :: state.iteration.2)
  history := history
  belief := none

/-- Even at positive execution fuel and a live off-model history, no posterior
is manufactured and the same incumbent is retained. The equality covers the
whole carried state, not only its payoff or its final history. -/
theorem cfrDInformationResolveStage_none
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (trainFuel stepFuel : Nat) (bound loss : ℝ)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) (missing : state.belief = none) :
    carriedMemoryStep (fullInformation M) initial unknown who
        (cfrDInformationResolveStage M initial fallback payoff trainFuel stepFuel bound loss)
        state =
      ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (carriedMemoryProfile (fullInformation M) initial state.iteration who))
        stepFuel state.history).map (cfrDInformationMissingNext M initial state) := by
  by_cases live : cfrDCutLive stepFuel state.history = true
  · simp only [carriedMemoryStep, cfrDInformationResolveStage, carriedResolvedStep,
      if_pos live, missing, cfrDInformationResolver_none, FinDist.pure_bind,
      FinDist.map_comp, resolvedNextState, storeCarriedDraw, carriedBeliefUpdate_none,
      cfrDInformationMissingNext]
  · rw [cfrD_run_stopped (fullInformation M) _ stepFuel state.history live]
    simp only [carriedMemoryStep, cfrDInformationResolveStage, carriedResolvedStep,
      if_neg live, FinDist.map_pure, storeCarriedDraw, cfrDInformationMissingNext, missing]

end GameTheory.ReBeL
