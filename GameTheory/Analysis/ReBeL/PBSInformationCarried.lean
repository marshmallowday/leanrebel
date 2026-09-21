/-
# Carried execution of actual information-set CFR iterations

The private child iteration is retained across every segment. The referee's
actual history and optional model PBS are separate: an impossible model
observation remains absent. The model PBS is conditioned from the supplied
joint root law and the selected complete profile, never from the unknown
opponent's actual law. No fresh child solve or independent redraw is hidden
in a segment boundary.
-/

import GameTheory.Analysis.ReBeL.PBSInformationSampling
import GameTheory.Analysis.ReBeL.CFRDCarriedPlay

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {observations : List M.PublicSignal}

/-- Attach the selected child's model belief while retaining its actual history.
Only the public observation is passed to the conditioning operation. -/
def pbsInformationCarriedState
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (fuel t elapsed : Nat) (iteration : Fin t) (history : E.History) :
    PrivateIterationState (fullInformation M) (Fin t) :=
  { iteration := iteration
    history := history
    belief := PublicBelief.condition?
      (belief.law.bind ((fullInformation M).runBehavioralFrom
        (pbsInformationCFRIterate M belief fallback payoff fuel iteration.val) elapsed))
      (publicTrace (fullInformation M).toInfoSignals history.trace) }

/-- Equal public observations yield the same model law, without exposing either
actual hidden history or using an opposing policy in the belief constructor. -/
theorem pbsInformationCarriedState_public
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (fuel t elapsed : Nat) (iteration : Fin t) (first second : E.History)
    (same : publicTrace (fullInformation M).toInfoSignals first.trace =
      publicTrace (fullInformation M).toInfoSignals second.trace) :
    ((pbsInformationCarriedState M belief fallback payoff fuel t elapsed iteration first).belief.map
      fun b => b.law) =
    ((pbsInformationCarriedState M belief fallback payoff fuel t elapsed iteration second).belief.map
      fun b => b.law) := by
  dsimp only [pbsInformationCarriedState]
  exact congrArg (fun obs => (PublicBelief.condition?
    (belief.law.bind ((fullInformation M).runBehavioralFrom
      (pbsInformationCFRIterate M belief fallback payoff fuel iteration.val) elapsed))
    obs).map fun b => b.law) same

/-- Off-model observations do not acquire an invented Bayesian posterior. -/
theorem pbsInformationCarriedState_no_posterior
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (fuel t elapsed : Nat) (iteration : Fin t) (history : E.History) :
    (pbsInformationCarriedState M belief fallback payoff fuel t elapsed iteration history).belief =
      none ↔
      ¬ PublicBelief.Possible (S := (fullInformation M).toInfoSignals)
        (belief.law.bind ((fullInformation M).runBehavioralFrom
          (pbsInformationCFRIterate M belief fallback payoff fuel iteration.val) elapsed))
        (publicTrace (fullInformation M).toInfoSignals history.trace) :=
  PublicBelief.condition?_eq_none _ _

/-- Draw one genuine child iteration and run against a seed-blind opponent. -/
def pbsInformationCarriedPrefix
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (elapsed : Nat) : FinDist (PrivateIterationState (fullInformation M) (Fin t)) :=
  (cfrIterationLaw t).bind fun iteration =>
    (belief.law.bind ((fullInformation M).runBehavioralFrom
      (Profile.update unknown who
        (pbsInformationCFRIterate M belief fallback payoff fuel iteration.val who)) elapsed)).map
      (pbsInformationCarriedState M belief fallback payoff fuel t elapsed iteration)

/-- Advance without resampling the iteration or replacing the actual history
by a draw from the model belief. The posterior is refreshed at the new time. -/
def pbsInformationCarriedAdvance
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (elapsed amount : Nat) (state : PrivateIterationState (fullInformation M) (Fin t)) :
    FinDist (PrivateIterationState (fullInformation M) (Fin t)) :=
  ((fullInformation M).runBehavioralFrom
    (Profile.update unknown who
      (pbsInformationCFRIterate M belief fallback payoff fuel state.iteration.val who))
    amount state.history).map
    (pbsInformationCarriedState M belief fallback payoff fuel t (elapsed + amount) state.iteration)

/-- Forgetting referee data gives the actual computed child's averaged law. -/
theorem pbsInformationCarriedPrefix_history
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (elapsed : Nat) :
    (pbsInformationCarriedPrefix M belief fallback payoff fuel t unknown who elapsed).map
      PrivateIterationState.history =
      belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFR M belief fallback payoff fuel t who))
        elapsed) := by
  simpa only [pbsInformationCarriedPrefix, FinDist.map_eq_bind, FinDist.bind_bind,
    FinDist.pure_bind, pbsInformationCarriedState, FinDist.bind_pure] using
    pbsInformationCFR_sampling_law M belief fallback payoff fuel t unknown who elapsed

/-- Segment composition preserves the entire joint seed/history/model state,
not just its expected payoff. Zero-length and terminal segments are included. -/
theorem pbsInformationCarriedPrefix_advance
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (elapsed amount : Nat) :
    (pbsInformationCarriedPrefix M belief fallback payoff fuel t unknown who elapsed).bind
      (pbsInformationCarriedAdvance M belief fallback payoff fuel t unknown who elapsed amount) =
      pbsInformationCarriedPrefix M belief fallback payoff fuel t unknown who (elapsed + amount) := by
  simp only [pbsInformationCarriedPrefix, pbsInformationCarriedAdvance,
    FinDist.map_eq_bind, FinDist.bind_bind, FinDist.pure_bind, pbsInformationCarriedState]
  apply FinDist.bind_congr
  intro iteration _
  apply FinDist.bind_congr
  intro history _
  rw [(fullInformation M).runBehavioralFrom_add _ elapsed amount history, FinDist.bind_bind]

/-- A finite segmentation runs the same selected child throughout, while
retaining its private index and refreshing the optional model PBS. -/
def pbsInformationCarriedStages
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) :
    Nat → List Nat → PrivateIterationState (fullInformation M) (Fin t) →
      FinDist (PrivateIterationState (fullInformation M) (Fin t))
  | _, [], state => FinDist.pure state
  | elapsed, amount :: rest, state =>
      (pbsInformationCarriedAdvance M belief fallback payoff fuel t unknown who
        elapsed amount state).bind
        (pbsInformationCarriedStages belief fallback payoff fuel t unknown who
          (elapsed + amount) rest)

/-- Any finite segmentation equals a single run, including the carried model
posterior. No independent-solve equivalence is presumed at segment boundaries. -/
theorem pbsInformationCarriedPrefix_stages
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (elapsed : Nat) (segments : List Nat) :
    (pbsInformationCarriedPrefix M belief fallback payoff fuel t unknown who elapsed).bind
      (pbsInformationCarriedStages M belief fallback payoff fuel t unknown who elapsed segments) =
      pbsInformationCarriedPrefix M belief fallback payoff fuel t unknown who
        (elapsed + segments.sum) := by
  induction segments generalizing elapsed with
  | nil =>
      simp only [pbsInformationCarriedStages, FinDist.bind_pure, List.sum_nil, Nat.add_zero]
  | cons amount rest ih =>
      simp only [pbsInformationCarriedStages, ← FinDist.bind_bind]
      rw [pbsInformationCarriedPrefix_advance, ih]
      simp only [List.sum_cons, Nat.add_assoc]

/-- Actual continuation play from the supplied joint PBS with a retained
private child iteration and any finite partition of the continuation fuel. -/
def pbsInformationCarriedRun
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (segments : List Nat) : FinDist E.History :=
  ((pbsInformationCarriedPrefix M belief fallback payoff fuel t unknown who 0).bind
    (pbsInformationCarriedStages M belief fallback payoff fuel t unknown who 0 segments)).map
    PrivateIterationState.history

/-- The actual sampled execution realizes the computed child average against
any fixed information-local opponent, with no extra segmentation penalty. -/
theorem pbsInformationCarriedRun_eq_average
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (segments : List Nat) :
    pbsInformationCarriedRun M belief fallback payoff fuel t unknown who segments =
      belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFR M belief fallback payoff fuel t who))
        segments.sum) := by
  rw [pbsInformationCarriedRun, pbsInformationCarriedPrefix_stages, Nat.zero_add]
  exact pbsInformationCarriedPrefix_history M belief fallback payoff fuel t unknown who _

end GameTheory.ReBeL
