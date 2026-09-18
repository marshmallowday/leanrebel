/-
# Geometry of the canonical joint-PBS value

Lemma 2 and Theorem 1 are connected to actual legal behavioral strategies
through `PBSValue`, not only to a type-local matrix illustration. A fixed
compatible conditional-history slice defines the own-belief domain. The
extension is the bounded lower envelope plus an affine mass correction;
it is deliberately not Appendix F's generally nonconcave radial formula.
-/

import GameTheory.Analysis.ReBeL.PBSValue
import GameTheory.Math.Probability.Simplex

noncomputable section

namespace GameTheory.ReBeL.TypeBeliefSlice

open GameTheory.Protocol InformationModel GameTheory.Math.Probability

universe us ua up uq uk ut
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable {M : InformationModel.{0, us, ua, up, uq, uk} E}
variable [Fintype E.History] [∀ i, Fintype (E.Action i)]
variable {observations : List M.PublicSignal} {T : Type ut} [Fintype T]
variable (slice : TypeBeliefSlice M observations 0 T)

/-- Lemma 2: the canonical conditional-value envelope is concave. Bounded
finite-history payoffs supply the hypothesis needed for its real infimum. -/
theorem value_concaveOn (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) : ConcaveOn ℝ Set.univ (slice.value fallback fuel payoff) := by
  let : Nonempty (Profile M.behavioralSignature) := ⟨fun i => (fallback i).toBehavioral⟩
  exact ValueGeometry.envelope_concave (slice.infoValue fallback fuel payoff)
    (slice.branches_bounded_below fallback fuel payoff)

/-- In particular, concavity holds on the entire own-belief simplex. -/
theorem value_concaveOn_simplex (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) :
    ConcaveOn ℝ (stdSimplex ℝ T) (slice.value fallback fuel payoff) :=
  (slice.value_concaveOn fallback fuel payoff).subset
    (fun _ _ => Set.mem_univ _) (convex_stdSimplex ℝ T)

/-- The centered conditional best-response vector in Equation (2). -/
def centeredVector (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) (base : T → ℝ)
    (opponents : Profile M.behavioralSignature) (type : T) : ℝ :=
  slice.infoValue fallback fuel payoff opponents type - slice.value fallback fuel payoff base

/-- A real-valued concave extension to every signed own-weight vector. -/
def allSpaceExtension (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) (base point : T → ℝ) : ℝ :=
  ValueGeometry.extension (slice.infoValue fallback fuel payoff)
    (slice.value fallback fuel payoff base) point

/-- The repaired extension agrees with the value at every probability vector. -/
theorem allSpaceExtension_eq_on_simplex (fallback : Profile M.strategicSignature)
    (fuel : ℕ) (payoff : E.History → ℝ) (base : T → ℝ) :
    Set.EqOn (slice.allSpaceExtension fallback fuel payoff base)
      (slice.value fallback fuel payoff) (stdSimplex ℝ T) := by
  intro point hpoint
  exact ValueGeometry.extension_eq_of_mass_one _ _ point hpoint.2

/-- Concavity on the full vector space includes neighborhoods of boundary
beliefs; it is stronger than concavity only on the nonnegative cone. -/
theorem allSpaceExtension_concave (fallback : Profile M.strategicSignature)
    (fuel : ℕ) (payoff : E.History → ℝ) (base : T → ℝ) :
    ConcaveOn ℝ Set.univ (slice.allSpaceExtension fallback fuel payoff base) := by
  let : Nonempty (Profile M.behavioralSignature) := ⟨fun i => (fallback i).toBehavioral⟩
  exact ValueGeometry.extension_concave (slice.infoValue fallback fuel payoff)
    (slice.value fallback fuel payoff base) (slice.branches_bounded_below fallback fuel payoff)

/-- Any attaining opponent supplies support for the same base-anchored
extension. This does not require unique equilibria or differentiability. -/
theorem allSpaceExtension_support (fallback : Profile M.strategicSignature)
    (fuel : ℕ) (payoff : E.History → ℝ) {base : T → ℝ}
    (hbase : base ∈ stdSimplex ℝ T) (opponents : Profile M.behavioralSignature)
    (optimal : slice.weightedBranch fallback fuel payoff base opponents =
      slice.value fallback fuel payoff base) (point : T → ℝ) :
    slice.allSpaceExtension fallback fuel payoff base point ≤
      slice.allSpaceExtension fallback fuel payoff base base +
        ∑ type, slice.centeredVector fallback fuel payoff base opponents type *
          (point type - base type) := by
  have active : ValueGeometry.envelope (slice.infoValue fallback fuel payoff) base =
      ValueGeometry.pairing (slice.infoValue fallback fuel payoff opponents) base := optimal.symm
  have supporting := ValueGeometry.centered_support (slice.infoValue fallback fuel payoff)
    (slice.branches_bounded_below fallback fuel payoff) base hbase.2 opponents active point
  simpa only [allSpaceExtension, centeredVector, value, ValueGeometry.pairing,
    Pi.sub_apply, mul_comm] using supporting

/-- The same centered vector supports the unextended value on the simplex. -/
theorem simplex_support (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) {base point : T → ℝ}
    (hbase : base ∈ stdSimplex ℝ T) (hpoint : point ∈ stdSimplex ℝ T)
    (opponents : Profile M.behavioralSignature)
    (optimal : slice.weightedBranch fallback fuel payoff base opponents =
      slice.value fallback fuel payoff base) :
    slice.value fallback fuel payoff point ≤ slice.value fallback fuel payoff base +
      ∑ type, slice.centeredVector fallback fuel payoff base opponents type *
        (point type - base type) := by
  have supporting := slice.allSpaceExtension_support fallback fuel payoff
    hbase opponents optimal point
  rw [slice.allSpaceExtension_eq_on_simplex fallback fuel payoff base hpoint,
    slice.allSpaceExtension_eq_on_simplex fallback fuel payoff base hbase] at supporting
  exact supporting

/-- The optimality premise above is supplied by canonical Nash, not by an
unproved value-vector certificate. The entire correlated PBS is retained. -/
theorem weightedBranch_eq_value_of_nash (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility) (own : FinDist T)
    (profile : Profile M.behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreference utility) profile) :
    slice.weightedBranch fallback fuel (fun history => utility history 0) own.prob profile =
      slice.value fallback fuel (fun history => utility history 0) own.prob := by
  rw [← slice.branch_eq_weightedBranch fallback fuel
    (fun history => utility history 0) own profile]
  exact (slice.branch_eq_equilibriumPayoff hrecall fallback fuel utility
    own profile equilibrium).trans (slice.value_eq_equilibriumPayoff hrecall fallback fuel
      utility hzero own profile equilibrium).symm

/-- Theorem 1's existential-extension interpretation for the actual joint
PBS game. Eq. (2) is tied to its canonical expected equilibrium utility.
The Nash existence theorem in `PBSValue` discharges nonvacuity separately. -/
theorem theorem1_canonicalPBS (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility) (own : FinDist T)
    (profile : Profile M.behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreference utility) profile) :
    ∃ extension : (T → ℝ) → ℝ,
      Set.EqOn extension (slice.value fallback fuel (fun history => utility history 0))
        (stdSimplex ℝ T) ∧ ConcaveOn ℝ Set.univ extension ∧
      (∀ point : T → ℝ, extension point ≤ extension own.prob +
        ∑ type, slice.centeredVector fallback fuel (fun history => utility history 0)
          own.prob profile type * (point type - own.prob type)) ∧
      (∀ type, slice.infoValue fallback fuel (fun history => utility history 0) profile type =
        expectedUtility utility 0
          ((behavioralBeliefForm M (slice.mixture own) fuel).play profile) +
        slice.centeredVector fallback fuel (fun history => utility history 0)
          own.prob profile type) := by
  refine ⟨slice.allSpaceExtension fallback fuel (fun history => utility history 0) own.prob,
    slice.allSpaceExtension_eq_on_simplex fallback fuel _ own.prob,
    slice.allSpaceExtension_concave fallback fuel _ own.prob,
    slice.allSpaceExtension_support fallback fuel _ own.prob_mem_stdSimplex profile
      (slice.weightedBranch_eq_value_of_nash hrecall fallback fuel utility hzero
        own profile equilibrium), ?_⟩
  intro type
  unfold centeredVector
  rw [slice.value_eq_equilibriumPayoff hrecall fallback fuel utility hzero own profile equilibrium]
  ring

/-- Finite convex averaging preserves global support. The `FinDist` weights
are nonnegative and normalized; arbitrary linear combinations are not asserted. -/
theorem averaged_global_support (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) {base : T → ℝ} (hbase : base ∈ stdSimplex ℝ T)
    (opponents : FinDist (Profile M.behavioralSignature))
    (optimal : ∀ profile ∈ opponents.support,
      slice.weightedBranch fallback fuel payoff base profile =
        slice.value fallback fuel payoff base) (point : T → ℝ) :
    slice.allSpaceExtension fallback fuel payoff base point ≤
      slice.allSpaceExtension fallback fuel payoff base base +
        ∑ type, opponents.expect (fun profile =>
          slice.centeredVector fallback fuel payoff base profile type) *
          (point type - base type) := by
  calc
    slice.allSpaceExtension fallback fuel payoff base point = opponents.expect
        (fun _ => slice.allSpaceExtension fallback fuel payoff base point) :=
      (FinDist.expect_const _ _).symm
    _ ≤ opponents.expect (fun profile => slice.allSpaceExtension fallback fuel payoff base base +
        ∑ type, slice.centeredVector fallback fuel payoff base profile type *
          (point type - base type)) := FinDist.expect_mono fun profile supported =>
      slice.allSpaceExtension_support fallback fuel payoff hbase profile
        (optimal profile supported) point
    _ = _ := by
      rw [FinDist.expect_add, FinDist.expect_const, ← FinDist.expect_sum_comm]
      simp only [FinDist.expect_mul_const]

end GameTheory.ReBeL.TypeBeliefSlice
