/-
# Carried-PBS execution of actual depth-limited parent iterates

The incoming joint model belief is the root of the newly computed CFR-D solve.
The resolver receives no actual hidden history or unknown-opponent policy.
Each private draw remains paired with the posterior propagated through that
same draw by the existing canonical resolver step and finite memory runner.
-/

import GameTheory.Analysis.ReBeL.PBSInformationDepthCFR
import GameTheory.Analysis.ReBeL.CFRDRecursivePlay

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*}

/-- A public model-law-indexed perturbation family for freshly rooted queries.
The actual hidden state and unknown opponent are deliberately not arguments. -/
abbrev PBSCarriedDepthNoise := (roots : FinDist E.History) → PBSRootDepthNoise M roots

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- Compute the incoming PBS's noisy depth-limited recurrence and privately
sample one of its actual parent iterates. Missing beliefs retain the old profile. -/
def pbsCarriedDepthResolver (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSCarriedDepthNoise M) (t : Nat) [NeZero t]
    (plays : K → Profile (fullInformation M).behavioralSignature) :
    CarriedPublicResolver (fullInformation M) K :=
  fun memory _ belief =>
    match belief with
    | none => FinDist.pure (plays memory)
    | some prior => (cfrIterationLaw t).map fun n =>
        pbsInformationDepthCFRIterate M prior fallback payoff cut remaining bound loss
          (noise prior.law) n.val

/-- Absence of a model posterior does not fabricate a new child game. -/
theorem pbsCarriedDepthResolver_none (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSCarriedDepthNoise M) (t : Nat) [NeZero t]
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (memory : K) (observations : List M.PublicSignal) :
    pbsCarriedDepthResolver M fallback payoff cut remaining bound loss noise t plays
      memory observations none = FinDist.pure (plays memory) := rfl

/-- The supplied belief, not the old private strategy family, determines the
newly computed depth-limited iterates and their numerical prediction queries. -/
theorem pbsCarriedDepthResolver_some (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSCarriedDepthNoise M) (t : Nat) [NeZero t]
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (memory : K) {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations) :
    pbsCarriedDepthResolver M fallback payoff cut remaining bound loss noise t plays
        memory observations (some belief) =
      (cfrIterationLaw t).map (fun n => pbsInformationDepthCFRIterate M belief fallback payoff
        cut remaining bound loss (noise belief.law) n.val) := rfl

/-- At the modeled root, the actual resolver realizes the constructed noisy
parent's own-reach average against any fixed unknown opponent. This is not an
identification of the incoming actual-state law with the model belief. -/
theorem pbsCarriedDepthResolver_model_law (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSCarriedDepthNoise M) (t : Nat) [NeZero t]
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (memory : K) {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat) :
    (pbsCarriedDepthResolver M fallback payoff cut remaining bound loss noise t plays
        memory observations (some belief)).bind (fun chosen => belief.law.bind
          ((fullInformation M).runBehavioralFrom
            (Profile.update unknown who (chosen who)) steps)) =
      belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationDepthCFR M belief fallback payoff
          cut remaining bound loss (noise belief.law) t who)) steps) := by
  rw [pbsCarriedDepthResolver_some, FinDist.bind_map]
  exact pbsInformationDepthCFR_sampling_law M belief fallback payoff cut remaining bound loss
    (noise belief.law) t unknown who steps

/-- The full canonical next-state law keeps the sampled parent iterate and its
own propagated model PBS together, even at unsupported actual input histories.
No equality with an independently averaged-PBS state law is claimed. -/
theorem pbsCarriedDepthResolver_step_some (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSCarriedDepthNoise M) (t : Nat) [NeZero t]
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (state : PrivateIterationState (fullInformation M) K)
    (belief : PublicBelief (fullInformation M).toInfoSignals
      (publicTrace (fullInformation M).toInfoSignals state.history.trace))
    (stored : state.belief = some belief) (live : cfrDCutLive steps state.history = true) :
    carriedResolvedStep (fullInformation M) plays
        (pbsCarriedDepthResolver M fallback payoff cut remaining bound loss noise t plays)
        unknown who steps state =
      (cfrIterationLaw t).bind (fun n =>
        ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who (pbsInformationDepthCFRIterate M belief fallback payoff
            cut remaining bound loss (noise belief.law) n.val who)) steps state.history).map
          (resolvedNextState (fullInformation M) state
            (pbsInformationDepthCFRIterate M belief fallback payoff cut remaining bound loss
              (noise belief.law) n.val) steps)) := by
  simp only [carriedResolvedStep, if_pos live, stored, pbsCarriedDepthResolver, FinDist.bind_map]

/-- Install the constructed depth-limited solver into the pre-existing finite
recursive runner, with separate training cut, remaining horizon and execution fuel. -/
def pbsCarriedDepthStage (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining steps : Nat) (bound loss : ℝ)
    (noise : PBSCarriedDepthNoise M) (t : Nat) [NeZero t]
    (initial : K → Profile (fullInformation M).behavioralSignature) :
    CarriedResolveStage (fullInformation M) K where
  fuel := steps
  resolver := pbsCarriedDepthResolver M fallback payoff cut remaining bound loss noise t
    (carriedMemoryProfile (fullInformation M) initial)

/-- The canonical zero-fuel branch bypasses all new solver queries. Its history
is unchanged; the existing memory-bookkeeping convention is not redefined. -/
theorem pbsCarriedDepthStage_zero_history (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSCarriedDepthNoise M) (t : Nat) [NeZero t]
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) :
    (carriedMemoryStep (fullInformation M) initial unknown who
      (pbsCarriedDepthStage M fallback payoff cut remaining 0 bound loss noise t initial)
      state).map (fun next => next.history) = FinDist.pure state.history := by
  rw [carriedMemoryStep_history]
  simp only [pbsCarriedDepthStage, carriedResolvedTail, cfrDCutLive_zero,
    Bool.false_eq_true, if_false]

end GameTheory.ReBeL
