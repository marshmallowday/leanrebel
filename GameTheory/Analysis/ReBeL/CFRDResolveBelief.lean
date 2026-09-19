/-
# Carrying the model belief after a public continuation replacement

A new solve changes the future model profile, not the observed past. Bayesian
updating therefore starts from the stored joint PBS and uses canonical
continuation execution, not a fresh run from the game's initial state.
The new private draw is retained; the actual opponent never becomes part of
the model posterior. Forgetting this extra state recovers the resolver law
already used by the security theorem exactly.
-/

import GameTheory.Analysis.ReBeL.CFRDResolve

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*}

/-- A stored joint belief is propagated only through the newly chosen future
model. No unknown-opponent policy or actual hidden history is an input. -/
def carriedBeliefUpdate {past : List M.PublicSignal}
    (belief : Option (PublicBelief M.toInfoSignals past))
    (chosen : Profile M.behavioralSignature) (fuel : Nat)
    (observed : List M.PublicSignal) : Option (PublicBelief M.toInfoSignals observed) :=
  belief.bind fun prior =>
    PublicBelief.condition? (PublicBelief.continuationLaw M chosen fuel prior) observed

/-- Missing model support remains missing; it is not silently replaced by a
posterior inferred from the actual opposing strategy or hidden history. -/
theorem carriedBeliefUpdate_none {past : List M.PublicSignal}
    (chosen : Profile M.behavioralSignature) (fuel : Nat) (observed : List M.PublicSignal) :
    carriedBeliefUpdate M (past := past) none chosen fuel observed = none := rfl

/-- A supported stored belief yields a new posterior exactly when the new
PUBLIC observation has positive mass under its model continuation law. -/
theorem carriedBeliefUpdate_eq_none {past : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals past) (chosen : Profile M.behavioralSignature)
    (fuel : Nat) (observed : List M.PublicSignal) :
    carriedBeliefUpdate M (some belief) chosen fuel observed = none ↔
      ¬ PublicBelief.Possible (S := M.toInfoSignals)
        (PublicBelief.continuationLaw M chosen fuel belief) observed := by
  exact PublicBelief.condition?_eq_none _ _

/-- Updating from a carried PBS cannot erase its public past, independently
of how the replacement profile would have played from the initial state. -/
theorem carriedBeliefUpdate_preserves_past {past : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals past) (chosen : Profile M.behavioralSignature)
    (fuel : Nat) (observed : List M.PublicSignal)
    (supported : PublicBelief.Possible (S := M.toInfoSignals)
      (PublicBelief.continuationLaw M chosen fuel belief) observed) :
    past <:+ observed := by
  obtain ⟨history, same, reached⟩ := supported
  have extends := PublicBelief.continuation_in_publicSubgame M chosen fuel belief history reached
  simpa only [PublicSubgame, Set.mem_setOf_eq, same] using extends

/-- Both the preceding private iteration and the fresh private profile draw
are retained. The posterior starts from the stored belief, not from a reset. -/
def resolvedNextState (state : PrivateIterationState M K)
    (chosen : Profile M.behavioralSignature) (fuel : Nat) (history : E.History) :
    PrivateIterationState M (K × Profile M.behavioralSignature) where
  iteration := (state.iteration, chosen)
  history := history
  belief := carriedBeliefUpdate M state.belief chosen fuel
    (publicTrace M.toInfoSignals history.trace)

/-- A public solve followed by a bounded canonical continuation, retaining
its new model belief and private draw for a later solve. Stopped states keep
their belief unchanged and do not invoke the resolver. -/
def carriedResolvedStep (plays : K → Profile M.behavioralSignature)
    (resolver : CarriedPublicResolver M K) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (fuel : Nat) (state : PrivateIterationState M K) :
    FinDist (PrivateIterationState M (K × Profile M.behavioralSignature)) :=
  if cfrDCutLive fuel state.history = true then
    (resolver state.iteration (publicTrace M.toInfoSignals state.history.trace)
      state.belief).bind fun chosen =>
        (M.runBehavioralFrom (Profile.update unknown who (chosen who)) fuel state.history).map
          (resolvedNextState M state chosen fuel)
  else FinDist.pure {
    iteration := (state.iteration, plays state.iteration)
    history := state.history
    belief := state.belief }

/-- The referee's history law is unchanged by retaining the new private
state. This is a canonical execution equality, not just a payoff equality. -/
theorem carriedResolvedStep_history (plays : K → Profile M.behavioralSignature)
    (resolver : CarriedPublicResolver M K) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (fuel : Nat) (state : PrivateIterationState M K) :
    (carriedResolvedStep M plays resolver unknown who fuel state).map
        (fun next => next.history) =
      carriedResolvedTail M resolver unknown who fuel state := by
  unfold carriedResolvedStep carriedResolvedTail
  split <;> simp only [FinDist.map_eq_bind, FinDist.bind_bind, FinDist.pure_bind,
    resolvedNextState, FinDist.bind_pure]

/-- The full privately selected prefix followed by the belief-carrying step. -/
def privateCarriedResolveStep (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (resolver : CarriedPublicResolver M K) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut remaining : Nat) :
    FinDist (PrivateIterationState M (K × Profile M.behavioralSignature)) :=
  (privateCarriedPrefix M seed plays unknown who cut).bind
    (carriedResolvedStep M plays resolver unknown who remaining)

/-- Adding the new carried PBS and private draw preserves the complete
original-game outcome law of the actual public resolver. -/
theorem privateCarriedResolveStep_history
    (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (resolver : CarriedPublicResolver M K) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut remaining : Nat) :
    (privateCarriedResolveStep M seed plays resolver unknown who cut remaining).map
        (fun state => state.history) =
      privateCarriedResolve M seed plays resolver unknown who cut remaining := by
  unfold privateCarriedResolveStep privateCarriedResolve
  rw [FinDist.map_bind]
  apply FinDist.bind_congr
  intro state _
  exact carriedResolvedStep_history M plays resolver unknown who remaining state

/-- In particular the proved security inequality applies unchanged to this
belief-carrying execution, by rewriting with this exact payoff identity. -/
theorem privateCarriedResolveStep_expect
    (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (resolver : CarriedPublicResolver M K) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut remaining : Nat) (payoff : E.History → ℝ) :
    (privateCarriedResolveStep M seed plays resolver unknown who cut remaining).expect
        (fun state => payoff state.history) =
      (privateCarriedResolve M seed plays resolver unknown who cut remaining).expect payoff := by
  rw [← FinDist.expect_map, privateCarriedResolveStep_history]

end GameTheory.ReBeL
