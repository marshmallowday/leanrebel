/-
# Derived allowances for native carried re-solving

The coefficient is computed from the incumbent history law and the actual
resolver's one fresh draw followed by that draw's retained continuation. It is
payoff-independent and never uses the output of the remaining recursive chain.
Full private state and the unknown opponent remain in the native forward laws.
No pointwise replacement certificate or model/actual posterior equality is input.
-/

import GameTheory.Analysis.ReBeL.CFRDRefreshMix
import GameTheory.Math.Probability.FinDistTotalVariation
import Mathlib.Data.Finset.Lattice.Fold

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*}

/-- One fresh native draw is retained for the entire residual horizon. The
comparison is between probability laws, not their payoff values. Stopped stages
have exactly zero charge and do not consult their resolver. -/
def carriedStepVariation (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K)) : ℝ :=
  if cfrDCutLive stage.fuel state.history = true then
    FinDist.totalVariation
      (carriedSelectedTail M initial unknown who (stage.fuel + remaining) state)
      ((stage.resolver state.iteration (publicTrace M.toInfoSignals state.history.trace)
        state.belief).bind fun chosen =>
          M.runBehavioralFrom (Profile.update unknown who (chosen who))
            (stage.fuel + remaining) state.history)
  else 0

/-- Every native replacement has a probability coefficient in the unit interval. -/
theorem carriedStepVariation_bounds (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K)) :
    0 ≤ carriedStepVariation M initial unknown who stage remaining state ∧
      carriedStepVariation M initial unknown who stage remaining state ≤ 1 := by
  unfold carriedStepVariation
  split_ifs
  · exact ⟨FinDist.totalVariation_nonneg _ _, FinDist.totalVariation_le_one _ _⟩
  · exact ⟨le_rfl, by norm_num⟩

/-- Zero execution fuel never pays a replacement charge, even with a nonzero tail. -/
theorem carriedStepVariation_zero_fuel (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K)) (zero : stage.fuel = 0) :
    carriedStepVariation M initial unknown who stage remaining state = 0 := by
  simp only [carriedStepVariation, zero, cfrDCutLive_zero, Bool.false_eq_true, if_false]

/-- A resolver that retains the incumbent has zero variation at every history,
including histories outside the model support. -/
theorem carriedStepVariation_retained (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K))
    (retained : stage.resolver state.iteration
      (publicTrace M.toInfoSignals state.history.trace) state.belief =
        FinDist.pure (carriedMemoryProfile M initial state.iteration)) :
    carriedStepVariation M initial unknown who stage remaining state = 0 := by
  unfold carriedStepVariation
  split_ifs
  · rw [retained, FinDist.pure_bind]
    exact FinDist.totalVariation_self _
  · rfl

/-- The actual memory step's local loss is bounded without assuming a strategic
replacement inequality. Its posterior/private-profile pairing is left intact. -/
theorem carriedStep_loss_le_variation (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K))
    (value : E.History → ℝ) (bound : ℝ) (bounded : ∀ h, |value h| ≤ bound) :
    (carriedSelectedTail M initial unknown who (stage.fuel + remaining) state).expect value -
      (carriedMemoryStep M initial unknown who stage state).expect (fun next =>
        (carriedSelectedTail M initial unknown who remaining next).expect value) ≤
      2 * bound * carriedStepVariation M initial unknown who stage remaining state := by
  rw [carriedMemoryStep_selected_expect]
  unfold carriedStepVariation
  split_ifs with live
  · rw [← FinDist.expect_bind]
    exact (le_abs_self _).trans
      (FinDist.abs_expect_sub_le_totalVariation _ _ value bound bounded)
  · simp only [sub_self, mul_zero, le_refl]

/-- A finite maximum over the ACTUAL incoming state support, not all possible
model beliefs or an unrelated training distribution. -/
def carriedStepVariationMax (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K))) : ℝ := by
  classical
  have nonempty : states.supportFinset.Nonempty := by
    obtain ⟨state, reached⟩ := states.support_nonempty
    exact ⟨state, FinDist.mem_supportFinset.mpr reached⟩
  exact max 0 (states.supportFinset.sup' nonempty
    (carriedStepVariation M initial unknown who stage remaining))

/-- Every reached state occurs in the finite maximum. -/
theorem carriedStepVariation_le_max (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K) (remaining : Nat)
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K)))
    (state : PrivateIterationState M (CarriedResolveMemory M K))
    (reached : state ∈ states.support) :
    carriedStepVariation M initial unknown who stage remaining state ≤
      carriedStepVariationMax M initial unknown who stage remaining states := by
  classical
  unfold carriedStepVariationMax
  apply le_trans _ (le_max_right _ _)
  exact Finset.le_sup' _ (FinDist.mem_supportFinset.mpr reached)

/-- The largest local variation in the actual finite chain. Repeated equal
stage descriptions still use their own residual horizons and reached state laws. -/
def carriedResolveMaxVariation (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat) :
    List (CarriedResolveStage M K) →
      FinDist (PrivateIterationState M (CarriedResolveMemory M K)) → ℝ
  | [], _ => 0
  | stage :: stages, states =>
      max (carriedStepVariationMax M initial unknown who stage
        (carriedResolveFuel M finalFuel stages) states)
        (carriedResolveMaxVariation initial unknown who finalFuel stages
          (states.bind (carriedMemoryStep M initial unknown who stage)))

/-- Increasing a stage allowance preserves the existing native safety interface. -/
theorem carriedResolveStepBounds_mono (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (value : E.History → ℝ) (first second : CarriedResolveStage M K → ℝ)
    (stages : List (CarriedResolveStage M K))
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K)))
    (larger : ∀ stage, first stage ≤ second stage)
    (bounds : CarriedResolveStepBounds M initial unknown who finalFuel value first stages states) :
    CarriedResolveStepBounds M initial unknown who finalFuel value second stages states := by
  induction stages generalizing states with
  | nil => trivial
  | cons stage stages ih =>
      exact ⟨fun state reached => (bounds.1 state reached).trans (larger stage),
        ih _ bounds.2⟩

/-- The existing step-bound interface is now DERIVED from the native probability
laws. No local no-loss, Nash, or final recursive-value certificate is supplied. -/
theorem carriedResolveStepBounds_from_variation
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (value : E.History → ℝ) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ h, |value h| ≤ bound) (stages : List (CarriedResolveStage M K))
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K))) :
    CarriedResolveStepBounds M initial unknown who finalFuel value
      (fun _ => 2 * bound * carriedResolveMaxVariation M initial unknown who finalFuel stages states)
      stages states := by
  induction stages generalizing states with
  | nil => trivial
  | cons stage stages ih =>
      constructor
      · intro state reached
        have rate : carriedStepVariation M initial unknown who stage
            (carriedResolveFuel M finalFuel stages) state ≤
            carriedResolveMaxVariation M initial unknown who finalFuel (stage :: stages) states :=
          (carriedStepVariation_le_max M initial unknown who stage
            (carriedResolveFuel M finalFuel stages) states state reached).trans (le_max_left _ _)
        exact (carriedStep_loss_le_variation M initial unknown who stage
          (carriedResolveFuel M finalFuel stages) state value bound bounded).trans
            (mul_le_mul_of_nonneg_left rate (mul_nonneg (by norm_num) nonneg))
      · apply carriedResolveStepBounds_mono M initial unknown who finalFuel value _ _ stages
          (states.bind (carriedMemoryStep M initial unknown who stage)) _ (ih _)
        intro later
        exact mul_le_mul_of_nonneg_left (le_max_right _ _)
          (mul_nonneg (by norm_num) nonneg)

/-- The sharper budget sums expected variations at native forward states.
It does not multiply a worst-case bound by the number of stages. -/
def carriedResolveVariationBudget (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat) :
    List (CarriedResolveStage M K) →
      FinDist (PrivateIterationState M (CarriedResolveMemory M K)) → ℝ
  | [], _ => 0
  | stage :: stages, states =>
      states.expect (carriedStepVariation M initial unknown who stage
        (carriedResolveFuel M finalFuel stages)) +
      carriedResolveVariationBudget initial unknown who finalFuel stages
        (states.bind (carriedMemoryStep M initial unknown who stage))

/-- Each actual step costs at most one unit of variation; the sum remains explicit. -/
theorem carriedResolveVariationBudget_bounds (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (stages : List (CarriedResolveStage M K))
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K))) :
    0 ≤ carriedResolveVariationBudget M initial unknown who finalFuel stages states ∧
      carriedResolveVariationBudget M initial unknown who finalFuel stages states ≤ stages.length := by
  induction stages generalizing states with
  | nil => simp only [carriedResolveVariationBudget, List.length_nil, Nat.cast_zero, le_refl, and_self]
  | cons stage stages ih =>
      have lower := FinDist.expect_mono (μ := states) (fun state _ =>
        (carriedStepVariation_bounds M initial unknown who stage
          (carriedResolveFuel M finalFuel stages) state).1)
      rw [FinDist.expect_const] at lower
      have upper := FinDist.expect_le_of_forall states _ 1 (fun state _ =>
        (carriedStepVariation_bounds M initial unknown who stage
          (carriedResolveFuel M finalFuel stages) state).2)
      have tail := ih (states.bind (carriedMemoryStep M initial unknown who stage))
      simp only [carriedResolveVariationBudget, List.length_cons, Nat.cast_add, Nat.cast_one]
      constructor <;> linarith

/-- An unconditional finite replacement estimate for the actual recursive
runner, with a computed, payoff-independent native-law budget. -/
theorem executeCarriedResolves_loss_le_variation
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (value : E.History → ℝ) (bound : ℝ) (bounded : ∀ h, |value h| ≤ bound)
    (stages : List (CarriedResolveStage M K))
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K))) :
    states.expect (fun state => (carriedSelectedTail M initial unknown who
        (carriedResolveFuel M finalFuel stages) state).expect value) -
      (states.bind (executeCarriedResolves M initial unknown who finalFuel stages)).expect value ≤
      2 * bound * carriedResolveVariationBudget M initial unknown who finalFuel stages states := by
  induction stages generalizing states with
  | nil =>
      simp only [executeCarriedResolves, carriedResolveFuel, FinDist.expect_bind,
        carriedResolveVariationBudget, sub_self, mul_zero, le_refl]
  | cons stage stages ih =>
      have localBound := FinDist.expect_mono (μ := states) (fun state _ =>
        carriedStep_loss_le_variation M initial unknown who stage
          (carriedResolveFuel M finalFuel stages) state value bound bounded)
      rw [FinDist.expect_sub, FinDist.expect_smul] at localBound
      have tailBound := ih (states.bind (carriedMemoryStep M initial unknown who stage))
      simp only [executeCarriedResolves, FinDist.expect_bind, carriedResolveFuel,
        carriedResolveVariationBudget] at localBound tailBound ⊢
      nlinarith only [localBound, tailBound]

/-- Any already established initial security bound transfers to fresh native
re-solving. The actual unknown-opponent prefix supplies the state distribution. -/
theorem privateRecursiveResolve_inherits_variation (seed : FinDist K)
    (plays : K → Profile M.behavioralSignature) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut finalFuel : Nat) (stages : List (CarriedResolveStage M K))
    (value : E.History → ℝ) (bound lower : ℝ) (bounded : ∀ h, |value h| ≤ bound)
    (prior : lower ≤ (privateCarriedContinue M seed plays unknown who cut
      (carriedResolveFuel M finalFuel stages)).expect value) :
    lower - 2 * bound * carriedResolveVariationBudget M plays unknown who finalFuel stages
        ((privateCarriedPrefix M seed plays unknown who cut).map (enterCarriedMemory M)) ≤
      (privateRecursiveResolve M seed plays unknown who cut finalFuel stages).expect value := by
  have transferred := executeCarriedResolves_loss_le_variation M plays unknown who finalFuel value
    bound bounded stages
    ((privateCarriedPrefix M seed plays unknown who cut).map (enterCarriedMemory M))
  have oldValue :
      ((privateCarriedPrefix M seed plays unknown who cut).map (enterCarriedMemory M)).expect
        (fun state => (carriedSelectedTail M plays unknown who
          (carriedResolveFuel M finalFuel stages) state).expect value) =
        (privateCarriedContinue M seed plays unknown who cut
          (carriedResolveFuel M finalFuel stages)).expect value := by
    simp only [FinDist.expect_map, privateCarriedContinue, FinDist.expect_bind,
      enterCarriedMemory, carriedSelectedTail, carriedMemoryProfile, List.headD_nil]
  rw [oldValue] at transferred
  unfold privateRecursiveResolve
  linarith

end GameTheory.ReBeL
