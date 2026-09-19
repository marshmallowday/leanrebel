/-
# Finite public re-solving with retained private memory

This is an actual finite execution chain, built from the canonical runner and
belief-carrying resolver step. Each new private profile is kept together with
the original private iteration. A stage-local continuation comparison implies
an additive bound for the complete chain. The comparison is explicit and is
not claimed to follow from arbitrary on-path subgame Nash equilibria.
-/

import GameTheory.Analysis.ReBeL.CFRDResolveBelief

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*}

/-- Original private iteration and the newest-first list of private profile draws. -/
abbrev CarriedResolveMemory (K : Type*) := K × List (Profile M.behavioralSignature)

/-- Until the first re-solve, use the original selected profile; afterwards,
use the most recently privately selected complete model profile. -/
def carriedMemoryProfile (initial : K → Profile M.behavioralSignature)
    (memory : CarriedResolveMemory M K) : Profile M.behavioralSignature :=
  memory.2.headD (initial memory.1)

/-- Enter the recursive execution without discarding the initial model PBS. -/
def enterCarriedMemory (state : PrivateIterationState M K) :
    PrivateIterationState M (CarriedResolveMemory M K) where
  iteration := (state.iteration, [])
  history := state.history
  belief := state.belief

/-- Flatten a fresh private draw into retained memory while preserving the
actual history and the model posterior already computed by the canonical step. -/
def storeCarriedDraw
    (state : PrivateIterationState M
      (CarriedResolveMemory M K × Profile M.behavioralSignature)) :
    PrivateIterationState M (CarriedResolveMemory M K) where
  iteration := (state.iteration.1.1, state.iteration.2 :: state.iteration.1.2)
  history := state.history
  belief := state.belief

/-- A stage's execution budget and public-only query procedure. The finite
list of stages, rather than a convergence or fairness assumption, terminates execution. -/
structure CarriedResolveStage (K : Type*) where
  /-- Number of canonical transitions allowed before the next public re-solve. -/
  fuel : Nat
  /-- Public observations, model belief and retained private memory determine the next draw. -/
  resolver : CarriedPublicResolver M (CarriedResolveMemory M K)

/-- One real canonical resolver step with all earlier private draws retained. -/
def carriedMemoryStep (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K)
    (state : PrivateIterationState M (CarriedResolveMemory M K)) :
    FinDist (PrivateIterationState M (CarriedResolveMemory M K)) :=
  (carriedResolvedStep M (carriedMemoryProfile M initial) stage.resolver
    unknown who stage.fuel state).map (storeCarriedDraw M)

/-- Memory bookkeeping preserves the actual public resolver's history law. -/
theorem carriedMemoryStep_history (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K)
    (state : PrivateIterationState M (CarriedResolveMemory M K)) :
    (carriedMemoryStep M initial unknown who stage state).map (fun next => next.history) =
      carriedResolvedTail M stage.resolver unknown who stage.fuel state := by
  unfold carriedMemoryStep
  rw [FinDist.map_comp]
  exact carriedResolvedStep_history M (carriedMemoryProfile M initial)
    stage.resolver unknown who stage.fuel state

/-- The selected complete profile is used for the remaining final continuation.
The actual unknown opponent is unchanged throughout every stage. -/
def carriedSelectedTail (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (fuel : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K)) : FinDist E.History :=
  M.runBehavioralFrom
    (Profile.update unknown who (carriedMemoryProfile M initial state.iteration who))
    fuel state.history

/-- Total remaining canonical fuel of a finite schedule, including its final continuation. -/
def carriedResolveFuel (finalFuel : Nat) : List (CarriedResolveStage M K) → Nat
  | [] => finalFuel
  | stage :: stages => stage.fuel + carriedResolveFuel finalFuel stages

/-- Execute every scheduled public solve, retaining its posterior and private
draws. Zero-fuel and terminal stages use the existing no-query stopping rule. -/
def executeCarriedResolves (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat) :
    List (CarriedResolveStage M K) →
      PrivateIterationState M (CarriedResolveMemory M K) → FinDist E.History
  | [], state => carriedSelectedTail M initial unknown who finalFuel state
  | stage :: stages, state =>
      (carriedMemoryStep M initial unknown who stage state).bind
        (executeCarriedResolves initial unknown who finalFuel stages)

/-- Only stage-local comparisons at actually reached carried states are
required. Each comparison uses the old selected continuation and the new
selected continuation, NOT the output value of the remaining recursive chain.
The latter is bounded by induction. These premises are proof obligations for
the particular resolver; arbitrary subgame Nash is not asserted to imply them. -/
def CarriedResolveStepBounds (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (payoff : E.History → ℝ) (allowance : CarriedResolveStage M K → ℝ) :
    List (CarriedResolveStage M K) →
      FinDist (PrivateIterationState M (CarriedResolveMemory M K)) → Prop
  | [], _ => True
  | stage :: stages, states =>
      (∀ state, state ∈ states.support →
        (carriedSelectedTail M initial unknown who
          (carriedResolveFuel M finalFuel (stage :: stages)) state).expect payoff -
        (carriedMemoryStep M initial unknown who stage state).expect (fun next =>
          (carriedSelectedTail M initial unknown who
            (carriedResolveFuel M finalFuel stages) next).expect payoff) ≤ allowance stage) ∧
      CarriedResolveStepBounds initial unknown who finalFuel payoff allowance stages
        (states.bind (carriedMemoryStep M initial unknown who stage))

/-- The complete finite execution loses at most the SUM of its local
replacement allowances. The proof follows actual forward state laws, so
later comparisons are not imposed only on an unrelated model distribution. -/
theorem executeCarriedResolves_loss_le (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (payoff : E.History → ℝ) (allowance : CarriedResolveStage M K → ℝ)
    (stages : List (CarriedResolveStage M K))
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K)))
    (bounds : CarriedResolveStepBounds M initial unknown who finalFuel payoff
      allowance stages states) :
    states.expect (fun state => (carriedSelectedTail M initial unknown who
        (carriedResolveFuel M finalFuel stages) state).expect payoff) -
      (states.bind (executeCarriedResolves M initial unknown who finalFuel stages)).expect
        payoff ≤ (stages.map allowance).sum := by
  induction stages generalizing states with
  | nil => simp only [executeCarriedResolves, carriedResolveFuel, FinDist.expect_bind,
      List.map_nil, List.sum_nil, sub_self, le_refl]
  | cons stage stages ih =>
      have localBound := FinDist.expect_le_of_forall states
        (fun state =>
          (carriedSelectedTail M initial unknown who
            (carriedResolveFuel M finalFuel (stage :: stages)) state).expect payoff -
          (carriedMemoryStep M initial unknown who stage state).expect (fun next =>
            (carriedSelectedTail M initial unknown who
              (carriedResolveFuel M finalFuel stages) next).expect payoff))
        (allowance stage) bounds.1
      rw [FinDist.expect_sub] at localBound
      have tailBound := ih
        (states.bind (carriedMemoryStep M initial unknown who stage)) bounds.2
      simp only [executeCarriedResolves, FinDist.expect_bind,
        List.map_cons, List.sum_cons] at tailBound ⊢
      linarith

/-- Start with the actual unknown-opponent prefix and its carried MODEL PBS,
then execute the finite public re-solving schedule. -/
def privateRecursiveResolve (seed : FinDist K)
    (plays : K → Profile M.behavioralSignature) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut finalFuel : Nat) (stages : List (CarriedResolveStage M K)) :
    FinDist E.History :=
  ((privateCarriedPrefix M seed plays unknown who cut).map (enterCarriedMemory M)).bind
    (executeCarriedResolves M plays unknown who finalFuel stages)

/-- Without further re-solving, the exact original carried continuation is
recovered; entering memory does not resample the private iteration. -/
theorem privateRecursiveResolve_nil (seed : FinDist K)
    (plays : K → Profile M.behavioralSignature) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut finalFuel : Nat) :
    privateRecursiveResolve M seed plays unknown who cut finalFuel [] =
      privateCarriedContinue M seed plays unknown who cut finalFuel := by
  simp only [privateRecursiveResolve, executeCarriedResolves, privateCarriedContinue,
    FinDist.map_eq_bind, FinDist.bind_bind, FinDist.pure_bind,
    enterCarriedMemory, carriedSelectedTail, carriedMemoryProfile, List.headD_nil]

/-- A finite public re-solving chain inherits any established security lower
bound on the original carried continuation, with explicit accumulated loss.
The finite-iteration term inside that prior bound is not discarded. -/
theorem privateRecursiveResolve_inherits_bound (seed : FinDist K)
    (plays : K → Profile M.behavioralSignature) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut finalFuel : Nat) (stages : List (CarriedResolveStage M K))
    (payoff : E.History → ℝ) (allowance : CarriedResolveStage M K → ℝ) (lower : ℝ)
    (prior : lower ≤ (privateCarriedContinue M seed plays unknown who cut
      (carriedResolveFuel M finalFuel stages)).expect payoff)
    (bounds : CarriedResolveStepBounds M plays unknown who finalFuel payoff allowance stages
      ((privateCarriedPrefix M seed plays unknown who cut).map (enterCarriedMemory M))) :
    lower - (stages.map allowance).sum ≤
      (privateRecursiveResolve M seed plays unknown who cut finalFuel stages).expect payoff := by
  have transferred := executeCarriedResolves_loss_le M plays unknown who finalFuel payoff
    allowance stages
    ((privateCarriedPrefix M seed plays unknown who cut).map (enterCarriedMemory M)) bounds
  have oldValue :
      ((privateCarriedPrefix M seed plays unknown who cut).map (enterCarriedMemory M)).expect
        (fun state => (carriedSelectedTail M plays unknown who
          (carriedResolveFuel M finalFuel stages) state).expect payoff) =
      (privateCarriedContinue M seed plays unknown who cut
        (carriedResolveFuel M finalFuel stages)).expect payoff := by
    simp only [FinDist.expect_map, privateCarriedContinue, FinDist.expect_bind,
      enterCarriedMemory, carriedSelectedTail, carriedMemoryProfile, List.headD_nil]
  rw [oldValue] at transferred
  exact (by linarith : lower - (stages.map allowance).sum ≤ _)

end GameTheory.ReBeL
