/-
# Signed replacement costs for the actual carried resolver

The selected child is retained through the stage AND the late continuation.
Its primitive execution discrepancy gives a signed local comparison, then a
forward expected cost for the complete native recursive execution. These are
computed costs, not claims that finite-iteration Nash makes policy drift small.
-/

import GameTheory.Analysis.ReBeL.PBSOpponentModelTransport
import GameTheory.Analysis.ReBeL.PBSCarriedDepthFirstHit
import GameTheory.Math.Probability.FinDistValueCoupling

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*}

/-- The private draw used for the stage is also the draw used by its late
selected continuation. This equality keeps the actual history and model PBS
paired in memory; it does not replace the state law by a product of marginals. -/
theorem carriedMemoryStep_selected_late_expect
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K))
    (payoff : E.History → ℝ) :
    (carriedMemoryStep M initial unknown who stage state).expect (fun next =>
        (carriedSelectedTail M initial unknown who remaining next).expect payoff) =
      if cfrDCutLive stage.fuel state.history = true then
        (stage.resolver state.iteration (publicTrace M.toInfoSignals state.history.trace)
          state.belief).expect (fun chosen =>
            (M.runBehavioralFrom (Profile.update unknown who (chosen who))
              (stage.fuel + remaining) state.history).expect payoff)
      else (carriedSelectedTail M initial unknown who remaining state).expect payoff := by
  by_cases live : cfrDCutLive stage.fuel state.history = true
  · rw [if_pos live, carriedMemoryStep, FinDist.expect_map, carriedResolvedStep,
      if_pos live, FinDist.expect_bind]
    apply FinDist.expect_congr
    intro chosen _
    rw [FinDist.expect_map]
    dsimp only [carriedSelectedTail, storeCarriedDraw, resolvedNextState,
      carriedMemoryProfile, List.headD_cons]
    rw [← FinDist.expect_bind, ← M.runBehavioralFrom_add]
  · simp only [if_neg live, carriedMemoryStep, FinDist.expect_map, carriedResolvedStep,
      FinDist.expect_pure, storeCarriedDraw, carriedSelectedTail,
      carriedMemoryProfile, List.headD_cons]

variable [Fintype E.History]

/-- Source-kernel cost of replacing the retained policy by the actual private
resolver draw, with the SAME unknown opponent on both sides. The entire late
horizon is charged. Stopped stages do not query or replace and cost zero. -/
def carriedReplacementExecutionCharge
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K)) : ℝ :=
  if cfrDCutLive stage.fuel state.history = true then
    (stage.resolver state.iteration (publicTrace M.toInfoSignals state.history.trace)
      state.belief).expect (fun chosen =>
        executionKernelCharge M
          (Profile.update unknown who (carriedMemoryProfile M initial state.iteration who))
          (Profile.update unknown who (chosen who)) (stage.fuel + remaining)
          (FinDist.pure state.history))
  else 0

/-- The constructed allowance is nonnegative; the signed loss itself need not be. -/
theorem carriedReplacementExecutionCharge_nonneg
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K)) :
    0 ≤ carriedReplacementExecutionCharge M initial unknown who stage remaining state := by
  unfold carriedReplacementExecutionCharge
  split
  · calc
      0 = (stage.resolver state.iteration
          (publicTrace M.toInfoSignals state.history.trace) state.belief).expect
            (fun _ => (0 : ℝ)) := (FinDist.expect_const _ 0).symm
      _ ≤ _ := FinDist.expect_mono fun _ _ => executionKernelCharge_nonneg M _ _ _ _
  · exact le_refl _

/-- A signed stage comparison derived from actual execution. No optimal-value
comparison or CarriedResolveStepBounds certificate is assumed. The child may
be random and may change both model policies, while the actual opponent stays fixed. -/
theorem carriedMemoryStep_selected_loss_le
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K))
    (payoff : E.History → ℝ) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ history, |payoff history| ≤ bound) :
    (carriedSelectedTail M initial unknown who (stage.fuel + remaining) state).expect payoff -
      (carriedMemoryStep M initial unknown who stage state).expect (fun next =>
        (carriedSelectedTail M initial unknown who remaining next).expect payoff) ≤
      bound * carriedReplacementExecutionCharge M initial unknown who stage remaining state := by
  rw [carriedMemoryStep_selected_late_expect]
  by_cases live : cfrDCutLive stage.fuel state.history = true
  · rw [if_pos live, carriedReplacementExecutionCharge, if_pos live]
    rw [← FinDist.expect_smul, ← FinDist.expect_const
      (stage.resolver state.iteration (publicTrace M.toInfoSignals state.history.trace)
        state.belief)
      ((carriedSelectedTail M initial unknown who (stage.fuel + remaining) state).expect payoff),
      ← FinDist.expect_sub]
    apply FinDist.expect_mono
    intro chosen _
    have distance := runBehavioralFrom_atomVariation_le M
      (Profile.update unknown who (carriedMemoryProfile M initial state.iteration who))
      (Profile.update unknown who (chosen who)) (stage.fuel + remaining)
      (FinDist.pure state.history) (FinDist.pure state.history)
    simp only [FinDist.pure_bind, FinDist.atomVariation_self, zero_add] at distance
    exact (le_abs_self _).trans
      ((FinDist.abs_expect_sub_le_atomVariation _ _ payoff bound bounded).trans
        (mul_le_mul_of_nonneg_left distance nonneg))
  · rw [if_neg live, carriedReplacementExecutionCharge, if_neg live, mul_zero]
    have stopped := cfrDCutValue_stopped M
      (Profile.update unknown who (carriedMemoryProfile M initial state.iteration who))
      (fun history => (M.runBehavioralFrom
        (Profile.update unknown who (carriedMemoryProfile M initial state.iteration who))
        remaining history).expect payoff) stage.fuel state.history live
    rw [← FinDist.expect_bind, ← M.runBehavioralFrom_add] at stopped
    rw [show (carriedSelectedTail M initial unknown who (stage.fuel + remaining)
      state).expect payoff =
      (carriedSelectedTail M initial unknown who remaining state).expect payoff from stopped]
    simp only [sub_self, le_refl]

/-- Actual forward expected replacement charges. Remaining fuel is recomputed
from the suffix, so each stage includes its late value before telescoping.
Private draws, histories and posteriors remain correlated in the incoming law. -/
def carriedSequenceExecutionCharge
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat) :
    List (CarriedResolveStage M K) →
      FinDist (PrivateIterationState M (CarriedResolveMemory M K)) → ℝ
  | [], _ => 0
  | stage :: stages, states =>
      states.expect (carriedReplacementExecutionCharge M initial unknown who stage
        (carriedResolveFuel M finalFuel stages)) +
      carriedSequenceExecutionCharge initial unknown who finalFuel stages
        (states.bind (carriedMemoryStep M initial unknown who stage))

/-- The complete recursive runner has a derived signed loss bound. This costs
native replacements, not the distance to an independently averaged-state runner. -/
theorem executeCarriedResolves_loss_le_executionCharge
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (payoff : E.History → ℝ) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ history, |payoff history| ≤ bound)
    (stages : List (CarriedResolveStage M K))
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K))) :
    states.expect (fun state => (carriedSelectedTail M initial unknown who
        (carriedResolveFuel M finalFuel stages) state).expect payoff) -
      (states.bind (executeCarriedResolves M initial unknown who finalFuel stages)).expect
        payoff ≤ bound * carriedSequenceExecutionCharge M initial unknown who
          finalFuel stages states := by
  induction stages generalizing states with
  | nil =>
      simp only [executeCarriedResolves, carriedResolveFuel, FinDist.expect_bind,
        carriedSequenceExecutionCharge, mul_zero, sub_self, le_refl]
  | cons stage stages ih =>
      have localBound := FinDist.expect_mono (μ := states) (fun state _ =>
        carriedMemoryStep_selected_loss_le M initial unknown who stage
          (carriedResolveFuel M finalFuel stages) state payoff bound nonneg bounded)
      rw [FinDist.expect_sub, FinDist.expect_smul] at localBound
      have tailBound := ih (states.bind (carriedMemoryStep M initial unknown who stage))
      simp only [executeCarriedResolves, FinDist.expect_bind, carriedResolveFuel,
        carriedSequenceExecutionCharge] at localBound tailBound ⊢
      nlinarith only [localBound, tailBound]

/-- Any already proved initial security lower bound survives the actual finite
sequence with its computed signed replacement cost. This interface preserves
the old finite-T and oracle terms inside lower without asserting a new rate. -/
theorem privateRecursiveResolve_inherits_executionCharge
    (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (cut finalFuel : Nat)
    (stages : List (CarriedResolveStage M K)) (payoff : E.History → ℝ)
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ history, |payoff history| ≤ bound)
    (lower : ℝ)
    (prior : lower ≤ (privateCarriedContinue M seed plays unknown who cut
      (carriedResolveFuel M finalFuel stages)).expect payoff) :
    lower - bound * carriedSequenceExecutionCharge M plays unknown who finalFuel stages
        ((privateCarriedPrefix M seed plays unknown who cut).map (enterCarriedMemory M)) ≤
      (privateRecursiveResolve M seed plays unknown who cut finalFuel stages).expect payoff := by
  have transferred := executeCarriedResolves_loss_le_executionCharge M plays unknown who
    finalFuel payoff bound nonneg bounded stages
    ((privateCarriedPrefix M seed plays unknown who cut).map (enterCarriedMemory M))
  have oldValue :
      ((privateCarriedPrefix M seed plays unknown who cut).map (enterCarriedMemory M)).expect
        (fun state => (carriedSelectedTail M plays unknown who
          (carriedResolveFuel M finalFuel stages) state).expect payoff) =
      (privateCarriedContinue M seed plays unknown who cut
        (carriedResolveFuel M finalFuel stages)).expect payoff := by
    simp only [FinDist.expect_map, privateCarriedContinue, FinDist.expect_bind,
      enterCarriedMemory, carriedSelectedTail, carriedMemoryProfile, List.headD_nil]
  rw [oldValue] at transferred
  unfold privateRecursiveResolve
  linarith only [prior, transferred]

/-- Primitive one-step discrepancy gives a finite-horizon replacement rate.
It compares the old and sampled OWN policies against the same unknown opponent;
a regret bound or a model-posterior identity is not this premise. -/
theorem carriedReplacementExecutionCharge_le_rate
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K))
    (rate : ℝ) (nonnegative : 0 ≤ rate)
    (steps : ∀ chosen ∈ (stage.resolver state.iteration
      (publicTrace M.toInfoSignals state.history.trace) state.belief).support,
      ∀ history, FinDist.atomVariation
        (M.runBehavioralFrom
          (Profile.update unknown who (carriedMemoryProfile M initial state.iteration who))
          1 history)
        (M.runBehavioralFrom (Profile.update unknown who (chosen who)) 1 history) ≤ rate) :
    carriedReplacementExecutionCharge M initial unknown who stage remaining state ≤
      ((stage.fuel + remaining : Nat) : ℝ) * rate := by
  unfold carriedReplacementExecutionCharge
  split
  · apply FinDist.expect_le_of_forall
    intro chosen sampled
    exact executionKernelCharge_le_mul M _ _ rate (steps chosen sampled) _ _
  · exact mul_nonneg (Nat.cast_nonneg _) nonnegative

/-- Construct the original signed stage certificate from primitive transition
rates. The horizon cap covers every remaining suffix, including finalFuel.
No stage-local payoff comparison is supplied as a hypothesis. -/
theorem carriedResolveStepBounds_of_executionRate
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel horizon : Nat)
    (payoff : E.History → ℝ) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ history, |payoff history| ≤ bound)
    (rate : CarriedResolveStage M K → ℝ)
    (nonnegative : ∀ stage, 0 ≤ rate stage)
    (steps : ∀ (stage : CarriedResolveStage M K)
      (state : PrivateIterationState M (CarriedResolveMemory M K)),
      ∀ chosen ∈ (stage.resolver state.iteration
        (publicTrace M.toInfoSignals state.history.trace) state.belief).support,
      ∀ history, FinDist.atomVariation
        (M.runBehavioralFrom
          (Profile.update unknown who (carriedMemoryProfile M initial state.iteration who))
          1 history)
        (M.runBehavioralFrom (Profile.update unknown who (chosen who)) 1 history) ≤ rate stage)
    (stages : List (CarriedResolveStage M K))
    (fuelBound : carriedResolveFuel M finalFuel stages ≤ horizon)
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K))) :
    CarriedResolveStepBounds M initial unknown who finalFuel payoff
      (fun stage => bound * (horizon : ℝ) * rate stage) stages states := by
  revert fuelBound states
  induction stages with
  | nil => intro _ _; trivial
  | cons stage stages ih =>
      intro fuelBound states
      constructor
      · intro state _
        have small := carriedReplacementExecutionCharge_le_rate M initial unknown who stage
          (carriedResolveFuel M finalFuel stages) state (rate stage) (nonnegative stage)
          (steps stage state)
        have horizonBound : ((stage.fuel + carriedResolveFuel M finalFuel stages : Nat) : ℝ)
            ≤ (horizon : ℝ) := by exact_mod_cast fuelBound
        have rateBound := mul_le_mul_of_nonneg_right horizonBound (nonnegative stage)
        have cost := mul_le_mul_of_nonneg_left (small.trans rateBound) nonneg
        have signed := carriedMemoryStep_selected_loss_le M initial unknown who stage
          (carriedResolveFuel M finalFuel stages) state payoff bound nonneg bounded
        exact signed.trans (by simpa only [mul_assoc] using cost)
      · exact ih ((Nat.le_add_left _ _).trans fuelBound) _



/-- The actual post-replacement outcome law includes the late continuation
under the SAME stored private draw. It does not run later re-solves early. -/
def carriedReplacementOutcome
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K)) : FinDist E.History :=
  (carriedMemoryStep M initial unknown who stage state).bind
    (carriedSelectedTail M initial unknown who remaining)

/-- Signed local loss computed from the two canonical continuation laws.
A gain remains negative, so different stages can cancel rather than being
charged by absolute history-law distance at every replacement. -/
def carriedReplacementSignedLoss
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K))
    (payoff : E.History → ℝ) : ℝ :=
  (carriedSelectedTail M initial unknown who (stage.fuel + remaining) state).expect payoff -
    (carriedReplacementOutcome M initial unknown who stage remaining state).expect payoff

/-- Kernel discrepancy is one valid bound on the signed local loss, not its
definition. This preserves the earlier bound as a conservative fallback. -/
theorem carriedReplacementSignedLoss_le_executionCharge
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K))
    (payoff : E.History → ℝ) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ history, |payoff history| ≤ bound) :
    carriedReplacementSignedLoss M initial unknown who stage remaining state payoff ≤
      bound * carriedReplacementExecutionCharge M initial unknown who stage remaining state := by
  simpa only [carriedReplacementSignedLoss, carriedReplacementOutcome, FinDist.expect_bind] using
    carriedMemoryStep_selected_loss_le M initial unknown who stage remaining state
      payoff bound nonneg bounded

/-- An outcome coupling supplies a value-sensitive alternative to history
variation. The first marginal is the NEW outcome and the second is the OLD
outcome, hence its directed cost charges old-minus-new payoff only. -/
theorem carriedReplacementSignedLoss_le_valueCoupling
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K))
    (payoff : E.History → ℝ) (joint : FinDist (E.History × E.History))
    (freshMarginal : joint.map Prod.fst =
      carriedReplacementOutcome M initial unknown who stage remaining state)
    (oldMarginal : joint.map Prod.snd =
      carriedSelectedTail M initial unknown who (stage.fuel + remaining) state) :
    carriedReplacementSignedLoss M initial unknown who stage remaining state payoff ≤
      FinDist.directedValueCost joint payoff payoff := by
  exact FinDist.expect_sub_le_directedValueCost _ _ joint payoff payoff
    freshMarginal oldMarginal

/-- Either independently justified bound may be used, without assuming that
a small finite-iteration Nash gap implies a small policy/kernel discrepancy. -/
theorem carriedReplacementSignedLoss_le_min
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K))
    (payoff : E.History → ℝ) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ history, |payoff history| ≤ bound)
    (joint : FinDist (E.History × E.History))
    (freshMarginal : joint.map Prod.fst =
      carriedReplacementOutcome M initial unknown who stage remaining state)
    (oldMarginal : joint.map Prod.snd =
      carriedSelectedTail M initial unknown who (stage.fuel + remaining) state) :
    carriedReplacementSignedLoss M initial unknown who stage remaining state payoff ≤
      min (bound * carriedReplacementExecutionCharge M initial unknown who stage remaining state)
        (FinDist.directedValueCost joint payoff payoff) :=
  le_min (carriedReplacementSignedLoss_le_executionCharge M initial unknown who stage
    remaining state payoff bound nonneg bounded)
    (carriedReplacementSignedLoss_le_valueCoupling M initial unknown who stage remaining
      state payoff joint freshMarginal oldMarginal)

/-- Signed local losses accumulated under actual forward full-state laws.
This definition evaluates each stage's retained tail, not an independently
resampled tail, model-state law, or the eventual remaining recursive solver. -/
def carriedSignedSequenceLoss
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (payoff : E.History → ℝ) :
    List (CarriedResolveStage M K) →
      FinDist (PrivateIterationState M (CarriedResolveMemory M K)) → ℝ
  | [], _ => 0
  | stage :: stages, states =>
      states.expect (fun state => carriedReplacementSignedLoss M initial unknown who stage
        (carriedResolveFuel M finalFuel stages) state payoff) +
      carriedSignedSequenceLoss initial unknown who finalFuel payoff stages
        (states.bind (carriedMemoryStep M initial unknown who stage))

/-- The signed forward sum is EXACTLY the complete native execution loss.
No local loss certificate, absolute value, or convergence premise is used. -/
theorem executeCarriedResolves_loss_eq_signed
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (payoff : E.History → ℝ) (stages : List (CarriedResolveStage M K))
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K))) :
    states.expect (fun state => (carriedSelectedTail M initial unknown who
        (carriedResolveFuel M finalFuel stages) state).expect payoff) -
      (states.bind (executeCarriedResolves M initial unknown who finalFuel stages)).expect
        payoff = carriedSignedSequenceLoss M initial unknown who finalFuel payoff stages
          states := by
  induction stages generalizing states with
  | nil =>
      simp only [executeCarriedResolves, carriedResolveFuel, FinDist.expect_bind,
        carriedSignedSequenceLoss, sub_self]
  | cons stage stages ih =>
      have tail := ih (states.bind (carriedMemoryStep M initial unknown who stage))
      simp only [carriedSignedSequenceLoss, carriedReplacementSignedLoss,
        carriedReplacementOutcome, FinDist.expect_sub, FinDist.expect_bind,
        executeCarriedResolves, carriedResolveFuel] at tail ⊢
      linarith only [tail]

/-- The exact signed accounting is bounded by the previously established
execution cost; replacing it by that cost can discard cancellation. -/
theorem carriedSignedSequenceLoss_le_executionCharge
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (payoff : E.History → ℝ) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ history, |payoff history| ≤ bound)
    (stages : List (CarriedResolveStage M K))
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K))) :
    carriedSignedSequenceLoss M initial unknown who finalFuel payoff stages states ≤
      bound * carriedSequenceExecutionCharge M initial unknown who finalFuel stages states := by
  rw [← executeCarriedResolves_loss_eq_signed]
  exact executeCarriedResolves_loss_le_executionCharge M initial unknown who finalFuel
    payoff bound nonneg bounded stages states

/-- Arbitrary outcome-label changes have no signed loss for constant payoff.
The result holds for the actual complete recursive schedule, including stops. -/
theorem carriedSignedSequenceLoss_const
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (value : ℝ) (stages : List (CarriedResolveStage M K))
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K))) :
    carriedSignedSequenceLoss M initial unknown who finalFuel (fun _ => value)
      stages states = 0 := by
  rw [← executeCarriedResolves_loss_eq_signed]
  simp only [FinDist.expect_const, sub_self]

/-- Coupling support bounds construct the existing signed stage certificate.
The premises are outcome marginal identities and pairwise payoff bounds,
not the stage expectation inequality or the final recursive guarantee. -/
theorem carriedResolveStepBounds_of_valueCoupling
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (payoff : E.History → ℝ) (allowance : CarriedResolveStage M K → ℝ)
    (nonneg : ∀ stage, 0 ≤ allowance stage)
    (joint : CarriedResolveStage M K → Nat →
      PrivateIterationState M (CarriedResolveMemory M K) → FinDist (E.History × E.History))
    (freshMarginal : ∀ stage remaining state, (joint stage remaining state).map Prod.fst =
      carriedReplacementOutcome M initial unknown who stage remaining state)
    (oldMarginal : ∀ stage remaining state, (joint stage remaining state).map Prod.snd =
      carriedSelectedTail M initial unknown who (stage.fuel + remaining) state)
    (bounded : ∀ stage remaining state pair, pair ∈ (joint stage remaining state).support →
      payoff pair.2 - payoff pair.1 ≤ allowance stage)
    (stages : List (CarriedResolveStage M K))
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K))) :
    CarriedResolveStepBounds M initial unknown who finalFuel payoff allowance stages states := by
  induction stages generalizing states with
  | nil => trivial
  | cons stage stages ih =>
      constructor
      · intro state _
        have localBound := carriedReplacementSignedLoss_le_valueCoupling M initial unknown who
          stage (carriedResolveFuel M finalFuel stages) state payoff
          (joint stage (carriedResolveFuel M finalFuel stages) state)
          (freshMarginal _ _ _) (oldMarginal _ _ _)
        have small := FinDist.directedValueCost_le_of_support
          (joint stage (carriedResolveFuel M finalFuel stages) state) payoff payoff
          (allowance stage) (nonneg stage) (bounded _ _ _)
        simpa only [carriedReplacementSignedLoss, carriedReplacementOutcome,
          FinDist.expect_bind, carriedResolveFuel] using localBound.trans small
      · exact ih _

/-- An initial security bound is inherited with the exact signed forward
loss. This sharper form retains gains as negative costs, but deriving small
solver-specific bounds on the signed sum is still a separate obligation. -/
theorem privateRecursiveResolve_inherits_signedLoss
    (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (cut finalFuel : Nat)
    (stages : List (CarriedResolveStage M K)) (payoff : E.History → ℝ)
    (lower : ℝ)
    (prior : lower ≤ (privateCarriedContinue M seed plays unknown who cut
      (carriedResolveFuel M finalFuel stages)).expect payoff) :
    lower - carriedSignedSequenceLoss M plays unknown who finalFuel payoff stages
        ((privateCarriedPrefix M seed plays unknown who cut).map (enterCarriedMemory M)) ≤
      (privateRecursiveResolve M seed plays unknown who cut finalFuel stages).expect payoff := by
  have identity := executeCarriedResolves_loss_eq_signed M plays unknown who finalFuel payoff
    stages ((privateCarriedPrefix M seed plays unknown who cut).map (enterCarriedMemory M))
  have oldValue :
      ((privateCarriedPrefix M seed plays unknown who cut).map (enterCarriedMemory M)).expect
        (fun state => (carriedSelectedTail M plays unknown who
          (carriedResolveFuel M finalFuel stages) state).expect payoff) =
      (privateCarriedContinue M seed plays unknown who cut
        (carriedResolveFuel M finalFuel stages)).expect payoff := by
    simp only [FinDist.expect_map, privateCarriedContinue, FinDist.expect_bind,
      enterCarriedMemory, carriedSelectedTail, carriedMemoryProfile, List.headD_nil]
  rw [oldValue] at identity
  unfold privateRecursiveResolve
  linarith only [prior, identity]

section InitialSecurity

variable [∀ who info, Fintype (M.Choice who info)]
variable [∀ who, DecidableEq (M.InfoState who)]

/-- Initial depth-limited CFR security now feeds the actual recursive runner
without a supplied signed replacement certificate. The finite-T residual,
oracle and child errors survive alongside the computed execution costs.
Smallness of the new costs is a separate solver-stability obligation. -/
theorem cfrDDepth_recursive_security_executionCharge (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (cut finalFuel : Nat) (oracle : CFRDValueOracle M) (bound error loss : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 ≤ loss)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (t : Nat) [NeZero t] (stages : List (CarriedResolveStage M (Fin t)))
    (accurate : CFRDDepthAccurate M clock fallback payoff cut
      (carriedResolveFuel M finalFuel stages) oracle error)
    (optimal : CFRDDepthLeafOptimal M clock fallback payoff cut
      (carriedResolveFuel M finalFuel stages) oracle loss)
    (reference : Profile M.behavioralSignature)
    (equilibrium : IsNash (M.toBehavioralGameForm
      (cut + carriedResolveFuel M finalFuel stages))
      (euPreference (fun history who => payoff who history)) reference)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) :
    (M.runBehavioral reference (cut + carriedResolveFuel M finalFuel stages)).expect
        (payoff who) -
      ((cfrDDepthErrorConstant M clock fallback cut (carriedResolveFuel M finalFuel stages) 0 +
          cfrDDepthErrorConstant M clock fallback cut (carriedResolveFuel M finalFuel stages) 1) *
          error +
        (cfrDDepthFiniteConstant M clock fallback cut
            (carriedResolveFuel M finalFuel stages) bound 0 +
          cfrDDepthFiniteConstant M clock fallback cut
            (carriedResolveFuel M finalFuel stages) bound 1) / Real.sqrt t +
        2 * loss) - bound * carriedSequenceExecutionCharge M
        (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut
          (carriedResolveFuel M finalFuel stages) oracle n.val)
        unknown who finalFuel stages
        ((privateCarriedPrefix M (cfrIterationLaw t)
          (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut
            (carriedResolveFuel M finalFuel stages) oracle n.val)
          unknown who cut).map (enterCarriedMemory M)) ≤
      (privateRecursiveResolve M (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut
          (carriedResolveFuel M finalFuel stages) oracle n.val)
        unknown who cut finalFuel stages).expect (payoff who) := by
  apply privateRecursiveResolve_inherits_executionCharge
  · exact hb
  · exact bounded who
  · exact cfrDDepth_carried_security M clock hrecall fallback payoff hzero cut
      (carriedResolveFuel M finalFuel stages) oracle bound error loss hb he hl bounded
      accurate optimal reference equilibrium unknown who t

/-- The original finite-T/oracle/child security bound feeds signed accounting
without a local replacement certificate. No learner convergence is assumed. -/
theorem cfrDDepth_recursive_security_signedLoss (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (cut finalFuel : Nat) (oracle : CFRDValueOracle M) (bound error loss : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 ≤ loss)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (t : Nat) [NeZero t] (stages : List (CarriedResolveStage M (Fin t)))
    (accurate : CFRDDepthAccurate M clock fallback payoff cut
      (carriedResolveFuel M finalFuel stages) oracle error)
    (optimal : CFRDDepthLeafOptimal M clock fallback payoff cut
      (carriedResolveFuel M finalFuel stages) oracle loss)
    (reference : Profile M.behavioralSignature)
    (equilibrium : IsNash (M.toBehavioralGameForm
      (cut + carriedResolveFuel M finalFuel stages))
      (euPreference (fun history who => payoff who history)) reference)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) :
    (M.runBehavioral reference (cut + carriedResolveFuel M finalFuel stages)).expect
        (payoff who) -
      ((cfrDDepthErrorConstant M clock fallback cut (carriedResolveFuel M finalFuel stages) 0 +
          cfrDDepthErrorConstant M clock fallback cut (carriedResolveFuel M finalFuel stages) 1) *
          error +
        (cfrDDepthFiniteConstant M clock fallback cut
            (carriedResolveFuel M finalFuel stages) bound 0 +
          cfrDDepthFiniteConstant M clock fallback cut
            (carriedResolveFuel M finalFuel stages) bound 1) / Real.sqrt t +
        2 * loss) - carriedSignedSequenceLoss M
        (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut
          (carriedResolveFuel M finalFuel stages) oracle n.val)
        unknown who finalFuel (payoff who) stages
        ((privateCarriedPrefix M (cfrIterationLaw t)
          (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut
            (carriedResolveFuel M finalFuel stages) oracle n.val)
          unknown who cut).map (enterCarriedMemory M)) ≤
      (privateRecursiveResolve M (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut
          (carriedResolveFuel M finalFuel stages) oracle n.val)
        unknown who cut finalFuel stages).expect (payoff who) := by
  apply privateRecursiveResolve_inherits_signedLoss
  exact cfrDDepth_carried_security M clock hrecall fallback payoff hzero cut
    (carriedResolveFuel M finalFuel stages) oracle bound error loss hb he hl bounded
    accurate optimal reference equilibrium unknown who t

end InitialSecurity

variable [∀ player, Fintype (E.Action player)]

/-- The actual noisy depth-parent resolver schedule consumes the constructed
signed bound. There is no supplied CarriedResolveStepBounds assumption and no
change to native private sampling or carried model posterior updates. -/
theorem pbsCarriedDepthSequence_value_loss_le
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (finalFuel : Nat) (schedule : List (PBSCarriedDepthParameters M))
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ history, |payoff who history| ≤ bound) :
    let stages := schedule.map (pbsCarriedDepthConfiguredStage M fallback payoff initial)
    states.expect (fun state =>
        (carriedSelectedTail (fullInformation M) initial unknown who
          (carriedResolveFuel (fullInformation M) finalFuel stages) state).expect (payoff who)) -
      (states.bind (executeCarriedResolves (fullInformation M) initial unknown who
        finalFuel stages)).expect (payoff who) ≤
      bound * carriedSequenceExecutionCharge (fullInformation M) initial unknown who
        finalFuel stages states :=
  executeCarriedResolves_loss_le_executionCharge (fullInformation M) initial unknown who
    finalFuel (payoff who) bound nonneg bounded _ states

end GameTheory.ReBeL
