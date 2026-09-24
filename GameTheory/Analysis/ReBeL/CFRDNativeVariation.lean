/-
# Derived allowances for native carried re-solving

The coefficient is computed from the incumbent history law and the actual
resolver's one fresh draw followed by that draw's retained continuation. It is
payoff-independent and never uses the output of the remaining recursive chain.
Full private state and the unknown opponent remain in the native forward laws.
No pointwise replacement certificate or model/actual posterior equality is input.
-/

import GameTheory.Analysis.ReBeL.CFRDRefreshMix
import GameTheory.Analysis.ReBeL.CFRDFreshValueDrift
import GameTheory.Analysis.ReBeL.PBSRecursiveDepth
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
      (fun _ => 2 * bound *
        carriedResolveMaxVariation M initial unknown who finalFuel stages states) stages states := by
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
      carriedResolveVariationBudget M initial unknown who finalFuel stages states ≤
        stages.length := by
  induction stages generalizing states with
  | nil =>
      simp only [carriedResolveVariationBudget, List.length_nil, Nat.cast_zero, le_refl, and_self]
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

section FreshModel

variable [∀ who info, Fintype (M.Choice who info)]

/-- Old and fresh model continuations start on the SAME old reference fiber.
The returned coefficient contains no payoff and no final safety conclusion. -/
def cfrDFreshQueryVariation (base next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2)
    (cut remaining : Nat) (info : M.InfoState who) : ℝ :=
  let query := (unilateralReferenceLaw M base fallback who cut).condOnFibre
    (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h)) (info, true)
  FinDist.totalVariation (query.bind (M.runBehavioralFrom next remaining))
    (query.bind (M.runBehavioralFrom base remaining))

/-- The source's signed fresh-model value change has a derived two-sided bound. -/
theorem cfrDFreshValueChange_abs_le_variation
    (base next : Profile M.behavioralSignature) (fallback : Profile M.strategicSignature)
    (who : Fin 2) (payoff : E.History → ℝ) (cut remaining : Nat) (info : M.InfoState who)
    (bound : ℝ) (bounded : ∀ h, |payoff h| ≤ bound) :
    |cfrDFreshValueChange M base next fallback who payoff cut remaining info| ≤
      2 * bound * cfrDFreshQueryVariation M base next fallback who cut remaining info := by
  unfold cfrDFreshValueChange conditionalOracleValue cfrDFreshQueryVariation
  rw [FinDist.expect_sub, ← FinDist.expect_bind, ← FinDist.expect_bind]
  exact FinDist.abs_expect_sub_le_totalVariation _ _ payoff bound bounded

/-- Keeping the model continuation gives zero conditional law variation. -/
theorem cfrDFreshQueryVariation_self (base : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2)
    (cut remaining : Nat) (info : M.InfoState who) :
    cfrDFreshQueryVariation M base base fallback who cut remaining info = 0 :=
  FinDist.totalVariation_self _

variable [Fintype E.History]

/-- Only supported LIVE old-reference queries enter this finite maximum.
A zero-mass query's total conditional is not treated as a queried posterior. -/
def cfrDFreshVariationMax (base next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (cut remaining : Nat) : ℝ := by
  classical
  exact max 0 ((Finset.univ : Finset E.History).sup'
    ⟨E.initHistory, Finset.mem_univ _⟩ fun h =>
      if (M.infoOf who h.trace, true) ∈ ((unilateralReferenceLaw M base fallback who cut).map
          (fun leaf => (M.infoOf who leaf.trace, cfrDCutLive remaining leaf))).support then
        cfrDFreshQueryVariation M base next fallback who cut remaining (M.infoOf who h.trace)
      else 0)

/-- The maximum is nonnegative, including when there are no live queries. -/
theorem cfrDFreshVariationMax_nonneg (base next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (cut remaining : Nat) :
    0 ≤ cfrDFreshVariationMax M base next fallback who cut remaining := le_max_left _ _

/-- Every supported information query has a representative in the maximum. -/
theorem cfrDFreshQueryVariation_le_max (base next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (cut remaining : Nat)
    (info : M.InfoState who)
    (sampled : (info, true) ∈ ((unilateralReferenceLaw M base fallback who cut).map
      (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h))).support) :
    cfrDFreshQueryVariation M base next fallback who cut remaining info ≤
      cfrDFreshVariationMax M base next fallback who cut remaining := by
  classical
  have witness := sampled
  rw [FinDist.support_map] at witness
  obtain ⟨history, _, same⟩ := witness
  have observed : M.infoOf who history.trace = info := congrArg Prod.fst same
  unfold cfrDFreshVariationMax
  apply le_trans _ (le_max_right _ _)
  have member := Finset.le_sup'
    (s := (Finset.univ : Finset E.History))
    (fun h => if (M.infoOf who h.trace, true) ∈
        ((unilateralReferenceLaw M base fallback who cut).map
          (fun leaf => (M.infoOf who leaf.trace, cfrDCutLive remaining leaf))).support then
      cfrDFreshQueryVariation M base next fallback who cut remaining (M.infoOf who h.trace)
      else 0) (Finset.mem_univ history)
  simpa only [observed, if_pos sampled] using member

/-- The existing fresh-value drift is now bounded by a probability-only
coefficient on its exact old reference queries, without assuming value drift. -/
theorem cfrDFreshValueDrift_le_variation (base next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ h, |payoff h| ≤ bound) :
    cfrDFreshValueDrift M base next fallback who payoff cut remaining ≤
      2 * bound * cfrDFreshVariationMax M base next fallback who cut remaining := by
  apply cfrDFreshValueDrift_le M base next fallback who payoff cut remaining
  · exact mul_nonneg (mul_nonneg (by norm_num) nonneg)
      (cfrDFreshVariationMax_nonneg M base next fallback who cut remaining)
  · intro info sampled
    exact ((le_abs_self _).trans
      (cfrDFreshValueChange_abs_le_variation M base next fallback who payoff cut remaining
        info bound bounded)).trans
      (mul_le_mul_of_nonneg_left
        (cfrDFreshQueryVariation_le_max M base next fallback who cut remaining info sampled)
        (mul_nonneg (by norm_num) nonneg))

end FreshModel

end GameTheory.ReBeL

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe u
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {K : Type*}

/-- Numerical inputs for one actual recursive PBS solve and execution stage.
No Nash, value, local-loss, or whole-chain certificate is stored here. -/
structure PBSRecursiveResolveParameters where
  /-- Original transition counts at the successive training cuts. -/
  cuts : List Nat
  /-- Requested solver accuracy; strategic guarantees separately require positivity. -/
  tolerance : ℝ
  /-- Actual execution transitions before the next fresh public solve. -/
  fuel : Nat

/-- Every entry installs the already-constructed recursive solver unchanged. -/
def pbsRecursiveVariationStages (noise : PBSRecursiveDepthNoise.{u})
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (parameters : List PBSRecursiveResolveParameters) :
    List (CarriedResolveStage (fullInformation M) K) :=
  parameters.map fun p =>
    pbsRecursiveDepthStage noise p.cuts M fallback payoff bound p.tolerance p.fuel initial

/-- Missing model beliefs retain the incumbent and therefore have zero law
variation even at arbitrary off-model histories and positive execution fuel. -/
theorem pbsRecursiveDepthStage_none_variation (noise : PBSRecursiveDepthNoise.{u})
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (p : PBSRecursiveResolveParameters) (remaining : Nat)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) (missing : state.belief = none) :
    carriedStepVariation (fullInformation M) initial unknown who
      (pbsRecursiveDepthStage noise p.cuts M fallback payoff bound p.tolerance p.fuel initial)
      remaining state = 0 := by
  apply carriedStepVariation_retained
  simp only [pbsRecursiveDepthStage, missing, pbsRecursiveDepthResolver]

/-- The actual fresh recursive solver discharges the existing step-bound
interface from its native law coefficient, rather than receiving that interface. -/
theorem pbsRecursiveResolve_stepBounds (noise : PBSRecursiveDepthNoise.{u})
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (finalFuel : Nat)
    (parameters : List PBSRecursiveResolveParameters)
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)))
    (value : E.History → ℝ) (observableBound : ℝ) (nonneg : 0 ≤ observableBound)
    (bounded : ∀ h, |value h| ≤ observableBound) :
    let stages := pbsRecursiveVariationStages M noise fallback payoff bound initial parameters
    CarriedResolveStepBounds (fullInformation M) initial unknown who finalFuel value
      (fun _ => 2 * observableBound * carriedResolveMaxVariation (fullInformation M)
        initial unknown who finalFuel stages states) stages states := by
  dsimp only
  exact carriedResolveStepBounds_from_variation (fullInformation M) initial unknown who
    finalFuel value observableBound nonneg bounded _ states

/-- Complete native re-solving by the actual structurally recursive PBS solver
inherits a prior bound with the sharper sum of expected native variations. The
coefficient is not identified with a numerical/Nash tolerance or assumed small. -/
theorem pbsRecursiveResolve_inherits_variation (noise : PBSRecursiveDepthNoise.{u})
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (seed : FinDist K) (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (cut finalFuel : Nat) (parameters : List PBSRecursiveResolveParameters)
    (value : E.History → ℝ) (observableBound lower : ℝ)
    (bounded : ∀ h, |value h| ≤ observableBound)
    (prior : lower ≤ (privateCarriedContinue (fullInformation M) seed initial unknown who cut
      (carriedResolveFuel (fullInformation M) finalFuel
        (pbsRecursiveVariationStages M noise fallback payoff bound initial parameters))).expect
          value) :
    let stages := pbsRecursiveVariationStages M noise fallback payoff bound initial parameters
    lower - 2 * observableBound * carriedResolveVariationBudget (fullInformation M)
        initial unknown who finalFuel stages
        ((privateCarriedPrefix (fullInformation M) seed initial unknown who cut).map
          (enterCarriedMemory (fullInformation M))) ≤
      (privateRecursiveResolve (fullInformation M) seed initial unknown who cut finalFuel
        stages).expect value := by
  dsimp only
  exact privateRecursiveResolve_inherits_variation (fullInformation M) seed initial unknown
    who cut finalFuel _ value observableBound lower bounded prior

end GameTheory.ReBeL
