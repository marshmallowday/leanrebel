/-
# Primitive policy charges for actual carried-PBS re-solving

The local charge measures action probabilities, not a desired continuation
value or final safety certificate. It follows the actual resolver draw and
forward state laws. No supplied belief is equated with the unknown opponent's
posterior. Terminal and zero-fuel stages make no new query and cost zero.
-/

import GameTheory.Analysis.ReBeL.PolicyStability
import GameTheory.Analysis.ReBeL.CFRDRefreshMix

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*} [Fintype E.History]

/-- Expected own-action displacement of the actual private resolver draw.
The unknown opponent is not an input; stopped stages never query the resolver. -/
def carriedPolicyRadius (initial : K → Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K)
    (state : PrivateIterationState M (CarriedResolveMemory M K)) : ℝ :=
  if cfrDCutLive stage.fuel state.history = true then
    (stage.resolver state.iteration (publicTrace M.toInfoSignals state.history.trace)
      state.belief).expect (fun chosen => behavioralPolicyDistance M who
        (carriedMemoryProfile M initial state.iteration who) (chosen who))
  else 0

/-- Primitive replacement costs are nonnegative. -/
theorem carriedPolicyRadius_nonneg (initial : K → Profile M.behavioralSignature)
    (who : Fin 2) (stage : CarriedResolveStage M K)
    (state : PrivateIterationState M (CarriedResolveMemory M K)) :
    0 ≤ carriedPolicyRadius M initial who stage state := by
  unfold carriedPolicyRadius
  split_ifs
  · have result := FinDist.expect_mono
      (stage.resolver state.iteration (publicTrace M.toInfoSignals state.history.trace)
        state.belief) (fun _ => 0) _
      (fun chosen _ => behavioralPolicyDistance_nonneg M who _ (chosen who))
    simpa only [FinDist.expect_const] using result
  · exact le_rfl

/-- A stopped branch has exactly zero charge, not a fictitious sampled cost. -/
theorem carriedPolicyRadius_stopped (initial : K → Profile M.behavioralSignature)
    (who : Fin 2) (stage : CarriedResolveStage M K)
    (state : PrivateIterationState M (CarriedResolveMemory M K))
    (stopped : cfrDCutLive stage.fuel state.history ≠ true) :
    carriedPolicyRadius M initial who stage state = 0 := by
  simp only [carriedPolicyRadius, if_neg stopped]

/-- A real replacement step loses at most remaining horizon times its
primitive expected action displacement, against every fixed unknown opponent. -/
theorem carriedMemoryStep_policy_loss (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K)
    (state : PrivateIterationState M (CarriedResolveMemory M K))
    (remaining : Nat) (payoff : E.History → ℝ) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ h, |payoff h| ≤ bound) :
    (carriedSelectedTail M initial unknown who (stage.fuel + remaining) state).expect payoff -
      (carriedMemoryStep M initial unknown who stage state).expect (fun next =>
        (carriedSelectedTail M initial unknown who remaining next).expect payoff) ≤
      bound * (stage.fuel + remaining) * carriedPolicyRadius M initial who stage state := by
  rw [carriedMemoryStep_selected_expect]
  by_cases live : cfrDCutLive stage.fuel state.history = true
  · rw [if_pos live]
    have averaged := FinDist.expect_mono
      (stage.resolver state.iteration (publicTrace M.toInfoSignals state.history.trace)
        state.belief)
      (fun chosen =>
        (carriedSelectedTail M initial unknown who (stage.fuel + remaining) state).expect
            payoff -
          (M.runBehavioralFrom (Profile.update unknown who (chosen who))
            (stage.fuel + remaining) state.history).expect payoff)
      (fun chosen => bound * (stage.fuel + remaining) * behavioralPolicyDistance M who
        (carriedMemoryProfile M initial state.iteration who) (chosen who))
      (fun chosen _ => (le_abs_self _).trans
        (runBehavioralFrom_policy_stability M unknown who
          (carriedMemoryProfile M initial state.iteration who) (chosen who)
          (stage.fuel + remaining) state.history payoff bound nonneg bounded))
    simpa only [FinDist.expect_sub, FinDist.expect_const, FinDist.expect_smul,
      carriedPolicyRadius, if_pos live] using averaged
  · rw [if_neg live, sub_self, carriedPolicyRadius_stopped M initial who stage state live,
      mul_zero]

/-- Add primitive charges along the ACTUAL forward carried-state distributions.
No payoff, Nash property or continuation-loss certificate is input to this computation. -/
def carriedPolicyCharge (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (bound : ℝ) (finalFuel : Nat) :
    List (CarriedResolveStage M K) →
      FinDist (PrivateIterationState M (CarriedResolveMemory M K)) → ℝ
  | [], _ => 0
  | stage :: stages, states =>
      states.expect (fun state => bound * carriedResolveFuel M finalFuel (stage :: stages) *
        carriedPolicyRadius M initial who stage state) +
      carriedPolicyCharge initial unknown who bound finalFuel stages
        (states.bind (carriedMemoryStep M initial unknown who stage))

/-- The actual recursive execution loss is DERIVED from action probabilities.
The estimate includes histories missing from the model's support. -/
theorem executeCarriedResolves_policy_loss (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (payoff : E.History → ℝ) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ h, |payoff h| ≤ bound) (stages : List (CarriedResolveStage M K))
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K))) :
    states.expect (fun state => (carriedSelectedTail M initial unknown who
        (carriedResolveFuel M finalFuel stages) state).expect payoff) -
      (states.bind (executeCarriedResolves M initial unknown who finalFuel stages)).expect
        payoff ≤ carriedPolicyCharge M initial unknown who bound finalFuel stages states := by
  induction stages generalizing states with
  | nil => simp only [executeCarriedResolves, carriedResolveFuel, FinDist.expect_bind,
      carriedPolicyCharge, sub_self, le_refl]
  | cons stage stages ih =>
      have localBound := FinDist.expect_mono states _ _ (fun state _ =>
        carriedMemoryStep_policy_loss M initial unknown who stage state
          (carriedResolveFuel M finalFuel stages) payoff bound nonneg bounded)
      rw [FinDist.expect_sub] at localBound
      have tailBound := ih (states.bind (carriedMemoryStep M initial unknown who stage))
      simp only [executeCarriedResolves, FinDist.expect_bind, carriedPolicyCharge,
        carriedResolveFuel] at localBound tailBound ⊢
      linarith

/-- Any established initial security guarantee survives actual independent
re-solving, with the computed primitive charge explicitly retained. -/
theorem privateRecursiveResolve_policy_bound (seed : FinDist K)
    (plays : K → Profile M.behavioralSignature) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut finalFuel : Nat) (stages : List (CarriedResolveStage M K))
    (payoff : E.History → ℝ) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ h, |payoff h| ≤ bound) (lower : ℝ)
    (prior : lower ≤ (privateCarriedContinue M seed plays unknown who cut
      (carriedResolveFuel M finalFuel stages)).expect payoff) :
    lower - carriedPolicyCharge M plays unknown who bound finalFuel stages
        ((privateCarriedPrefix M seed plays unknown who cut).map (enterCarriedMemory M)) ≤
      (privateRecursiveResolve M seed plays unknown who cut finalFuel stages).expect payoff := by
  have transferred := executeCarriedResolves_policy_loss M plays unknown who finalFuel
    payoff bound nonneg bounded stages
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
  linarith

/-- Primitive action-rate obligations, only at actually reached carried states.
Unlike StepBounds these contain no payoff or continuation-value comparison. -/
def CarriedResolvePolicyRates (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (rate : CarriedResolveStage M K → ℝ) : List (CarriedResolveStage M K) →
      FinDist (PrivateIterationState M (CarriedResolveMemory M K)) → Prop
  | [], _ => True
  | stage :: stages, states =>
      (∀ state, state ∈ states.support →
        carriedPolicyRadius M initial who stage state ≤ rate stage) ∧
      CarriedResolvePolicyRates initial unknown who rate stages
        (states.bind (carriedMemoryStep M initial unknown who stage))

/-- A primitive numerical rate proves the previously separate StepBounds.
The total horizon is explicit, and no state is replaced by its modeled PBS. -/
theorem CarriedResolvePolicyRates.stepBounds (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (payoff : E.History → ℝ) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ h, |payoff h| ≤ bound) (finalFuel horizon : Nat)
    (rate : CarriedResolveStage M K → ℝ) (rateNonneg : ∀ stage, 0 ≤ rate stage)
    (stages : List (CarriedResolveStage M K))
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K)))
    (budget : carriedResolveFuel M finalFuel stages ≤ horizon)
    (rates : CarriedResolvePolicyRates M initial unknown who rate stages states) :
    CarriedResolveStepBounds M initial unknown who finalFuel payoff
      (fun stage => bound * horizon * rate stage) stages states := by
  induction stages generalizing states with
  | nil => trivial
  | cons stage stages ih =>
      constructor
      · intro state reached
        have localBound := carriedMemoryStep_policy_loss M initial unknown who stage state
          (carriedResolveFuel M finalFuel stages) payoff bound nonneg bounded
        have changeBound := mul_le_mul_of_nonneg_left (rates.1 state reached)
          (mul_nonneg nonneg (Nat.cast_nonneg (stage.fuel +
            carriedResolveFuel M finalFuel stages)))
        have horizonBound := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr budget) nonneg) (rateNonneg stage)
        exact localBound.trans (changeBound.trans horizonBound)
      · apply ih (states.bind (carriedMemoryStep M initial unknown who stage))
        · exact le_trans (Nat.le_add_left _ _) budget
        · exact rates.2

end GameTheory.ReBeL
