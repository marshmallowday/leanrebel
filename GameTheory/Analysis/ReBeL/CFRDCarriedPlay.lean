/-
# Private iteration execution with carried model beliefs

The referee retains the sampled iteration across the public cut. Its actual
history is not passed to a player's action rule. The model belief depends only
on this private iteration and the observed public trace, not on the unknown
opponent. An impossible model observation has no invented Bayesian posterior.
This module preserves a selected continuation; recursive re-solving is a
separate replacement obligation.
-/

import GameTheory.Analysis.ReBeL.CFRDSafety
import GameTheory.ReBeL.BeliefExecution

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*}

/-- Referee state, not a policy observation. The iteration remains private. -/
structure PrivateIterationState (K : Type*) where
  /-- The one sampled solver iteration, retained across the cut. -/
  iteration : K
  /-- Actual history under the focal policy and the unknown opponent. -/
  history : E.History
  /-- A model posterior, not the actual unknown-opponent posterior. -/
  belief : Option (PublicBelief M.toInfoSignals (publicTrace M.toInfoSignals history.trace))

/-- Attach a model belief without changing the actual hidden history or seed.
Only the public trace is observed by the model-conditioning operation. -/
def privateIterationState (plays : K → Profile M.behavioralSignature) (elapsed : Nat)
    (iteration : K) (history : E.History) : PrivateIterationState M K :=
  { iteration := iteration
    history := history
    belief := PublicBelief.condition? (M.runBehavioral (plays iteration) elapsed)
      (publicTrace M.toInfoSignals history.trace) }

/-- The same model observation produces the same optional joint history law,
even if the actual hidden histories or opposing policies are different. -/
theorem privateIterationState_public (plays : K → Profile M.behavioralSignature)
    (elapsed : Nat) (iteration : K) (first second : E.History)
    (same : publicTrace M.toInfoSignals first.trace =
      publicTrace M.toInfoSignals second.trace) :
    ((privateIterationState M plays elapsed iteration first).belief.map fun b => b.law) =
      ((privateIterationState M plays elapsed iteration second).belief.map fun b => b.law) := by
  dsimp only [privateIterationState]
  exact congrArg (fun observations =>
    (PublicBelief.condition? (M.runBehavioral (plays iteration) elapsed) observations).map
      fun b => b.law) same

/-- Zero-probability model observations are preserved rather than silently
replaced by the factual unknown-opponent law. -/
theorem privateIterationState_no_posterior (plays : K → Profile M.behavioralSignature)
    (elapsed : Nat) (iteration : K) (history : E.History) :
    (privateIterationState M plays elapsed iteration history).belief = none ↔
      ¬ PublicBelief.Possible (S := M.toInfoSignals)
        (M.runBehavioral (plays iteration) elapsed)
        (publicTrace M.toInfoSignals history.trace) :=
  PublicBelief.condition?_eq_none _ _

/-- Sample once and execute the focal player's policy against a seed-blind
opponent, retaining both the seed and its model belief at the cut. -/
def privateCarriedPrefix (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (cut : Nat) :
    FinDist (PrivateIterationState M K) :=
  seed.bind fun iteration =>
    (M.runBehavioral (Profile.update unknown who (plays iteration who)) cut).map
      (privateIterationState M plays cut iteration)

/-- Continuing from a carried state uses the SAME selected policy, not a
new independent iteration. No model posterior is substituted for the actual
history; the model belief is available to a later public re-solving adapter. -/
def privateCarriedContinue (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (cut remaining : Nat) :
    FinDist E.History :=
  (privateCarriedPrefix M seed plays unknown who cut).bind fun state =>
    M.runBehavioralFrom (Profile.update unknown who (plays state.iteration who))
      remaining state.history

/-- Forgetting the retained seed and model data yields the actual prefix law. -/
theorem privateCarriedPrefix_history (seed : FinDist K)
    (plays : K → Profile M.behavioralSignature) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut : Nat) :
    (privateCarriedPrefix M seed plays unknown who cut).map PrivateIterationState.history =
      privateIterationLaw M seed plays unknown who cut := by
  simp only [privateCarriedPrefix, privateIterationLaw, FinDist.map_eq_bind,
    FinDist.bind_bind, FinDist.pure_bind, privateIterationState, FinDist.bind_pure]

/-- The carried-state execution is exactly the canonical complete-policy
mixture against every seed-blind opponent, including off-model observations. -/
theorem privateCarriedContinue_eq (seed : FinDist K)
    (plays : K → Profile M.behavioralSignature) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut remaining : Nat) :
    privateCarriedContinue M seed plays unknown who cut remaining =
      privateIterationLaw M seed plays unknown who (cut + remaining) := by
  simp only [privateCarriedContinue, privateCarriedPrefix, privateIterationLaw,
    FinDist.map_eq_bind, FinDist.bind_bind, FinDist.pure_bind, privateIterationState]
  apply FinDist.bind_congr
  intro iteration _
  exact (M.runBehavioralFrom_add _ cut remaining E.initHistory).symm

variable [Fintype K]

/-- This law is the own-reach average against an arbitrary opponent. The
result is not a claim about arithmetic coordinate averaging or a shared seed. -/
theorem privateCarriedContinue_eq_average (hrecall : M.PerfectRecall)
    (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (fallback : (who : Fin 2) → M.Policy who)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (cut remaining : Nat) :
    privateCarriedContinue M seed plays unknown who cut remaining =
      M.runBehavioral (Profile.update unknown who
        (ownReachAverageProfile M (fun _ => seed) plays fallback who)) (cut + remaining) := by
  rw [privateCarriedContinue_eq, privateIterationLaw_eq_average M hrecall _ _ fallback]

variable [Fintype E.History]
variable [∀ who info, Fintype (M.Choice who info)]
variable [∀ who, DecidableEq (M.InfoState who)]

/-- The proved finite-time security bound applies to actual carried-state
execution. This does not assert safety of an arbitrary replacement policy. -/
theorem cfrDDepth_carried_security (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (cut remaining : Nat) (oracle : CFRDValueOracle M) (bound error loss : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 ≤ loss)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error)
    (optimal : CFRDDepthLeafOptimal M clock fallback payoff cut remaining oracle loss)
    (reference : Profile M.behavioralSignature)
    (equilibrium : IsNash (M.toBehavioralGameForm (cut + remaining))
      (euPreference (fun history who => payoff who history)) reference)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (t : Nat) [NeZero t] :
    (M.runBehavioral reference (cut + remaining)).expect (payoff who) -
      ((cfrDDepthErrorConstant M clock fallback cut remaining 0 +
          cfrDDepthErrorConstant M clock fallback cut remaining 1) * error +
        (cfrDDepthFiniteConstant M clock fallback cut remaining bound 0 +
          cfrDDepthFiniteConstant M clock fallback cut remaining bound 1) / Real.sqrt t +
        2 * loss) ≤
      (privateCarriedContinue M (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val)
        unknown who cut remaining).expect (payoff who) := by
  rw [privateCarriedContinue_eq]
  exact cfrDDepth_private_security M clock hrecall fallback payoff hzero cut remaining oracle
    bound error loss hb he hl bounded accurate optimal reference equilibrium unknown who t

end GameTheory.ReBeL
