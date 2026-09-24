/-
# Unnormalized source-law rates for conditional transport

OLD observation mass cancels conditional normalization. The bounds include
NEW-only atoms and disappearing NEW queries, and never use a minimum reach.
The finite carrier assumption is used only for explicit source-atom sums.
-/

import GameTheory.Math.Probability.FinDistConditioning

noncomputable section

namespace GameTheory.Math.Probability.FinDist

universe u v
variable {α : Type u} {β : Type v} [Fintype α]

/-- The L1 difference of finite source atoms, before conditioning. -/
def atomVariation (old fresh : FinDist α) : ℝ :=
  ∑ x, |old.prob x - fresh.prob x|

/-- Source-atom variation is nonnegative. -/
theorem atomVariation_nonneg (old fresh : FinDist α) : 0 ≤ atomVariation old fresh :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Identical source laws have zero variation. -/
theorem atomVariation_self (law : FinDist α) : atomVariation law law = 0 := by
  simp [atomVariation]

/-- The source-atom distance of probability laws is at most two. -/
theorem atomVariation_le_two (old fresh : FinDist α) : atomVariation old fresh ≤ 2 := by
  calc
    _ ≤ ∑ x, (old.prob x + fresh.prob x) := by
      apply Finset.sum_le_sum
      intro x _
      exact abs_le.mpr ⟨by linarith [prob_nonneg old x], by linarith [prob_nonneg fresh x]⟩
    _ = 2 := by rw [Finset.sum_add_distrib, sum_prob, sum_prob]; norm_num

/-- Bounded payoffs are stable under a change of their actual outcome law. -/
theorem abs_expect_sub_le_atomVariation (old fresh : FinDist α) (value : α → ℝ)
    (bound : ℝ) (bounded : ∀ x, |value x| ≤ bound) :
    |old.expect value - fresh.expect value| ≤ bound * atomVariation old fresh := by
  calc
    _ = |∑ x, (old.prob x - fresh.prob x) * value x| := by
      rw [expect_eq_sum, expect_eq_sum, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ ∑ x, |(old.prob x - fresh.prob x) * value x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, bound * |old.prob x - fresh.prob x| := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (bounded x)
        (abs_nonneg (old.prob x - fresh.prob x))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Unnormalized atom change within one observed fiber. NEW-only atoms are
included, even though the OLD conditional cannot sample them. -/
def fiberAtomVariation (old fresh : FinDist α) (observe : α → β) (tag : β) : ℝ := by
  classical
  exact ∑ x, if observe x = tag then |old.prob x - fresh.prob x| else 0

/-- Every fiber discrepancy is nonnegative, including an absent fiber. -/
theorem fiberAtomVariation_nonneg (old fresh : FinDist α) (observe : α → β) (tag : β) :
    0 ≤ fiberAtomVariation old fresh observe tag := by
  classical
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact abs_nonneg _
  · exact le_refl _

private theorem observation_prob_sum (law : FinDist α) (observe : α → β) (tag : β) :
    (law.map observe).prob tag = ∑ x, if observe x = tag then law.prob x else 0 := by
  classical
  rw [prob_map_eq_probOf_preimage_singleton, ← expect_indicator_eq_probOf, expect_eq_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases same : observe x = tag <;> simp [same]

/-- Multiplying by observation mass removes normalization, even for an absent
OLD query: its zero multiplier does not turn its fallback into a posterior. -/
theorem observation_prob_mul_conditional_prob (law : FinDist α)
    (observe : α → β) (tag : β) (x : α) :
    (law.map observe).prob tag * (law.condOnFibre observe tag).prob x =
      if observe x = tag then law.prob x else 0 := by
  classical
  by_cases reached : tag ∈ (law.map observe).support
  · have possible : ∃ y ∈ observe ⁻¹' {tag}, y ∈ law.support := by
      rw [support_map] at reached
      obtain ⟨y, hy, same⟩ := reached
      exact ⟨y, same, hy⟩
    rw [condOnFibre, dif_pos possible, prob_condOn, prob_map_eq_probOf_preimage_singleton]
    by_cases same : observe x = tag
    · simp only [Set.mem_preimage, Set.mem_singleton_iff, same, if_true]
      field_simp [(probOf_pos possible).ne']
    · simp only [Set.mem_preimage, Set.mem_singleton_iff, same, if_false, mul_zero]
  · rw [prob_eq_zero_iff.mpr reached, zero_mul]
    by_cases same : observe x = tag
    · rw [if_pos same]
      symm
      apply prob_eq_zero_iff.mpr
      intro hx
      exact reached (by rw [support_map]; exact ⟨x, hx, same⟩)
    · rw [if_neg same]

/-- Marginal mass changes are already included in the fiber atom discrepancy. -/
theorem abs_observation_prob_sub_le_fiberAtomVariation (old fresh : FinDist α)
    (observe : α → β) (tag : β) :
    |(old.map observe).prob tag - (fresh.map observe).prob tag| ≤
      fiberAtomVariation old fresh observe tag := by
  classical
  rw [observation_prob_sum, observation_prob_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x, |(if observe x = tag then old.prob x else 0) -
        (if observe x = tag then fresh.prob x else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases same : observe x = tag <;> simp [same]

/-- OLD query mass cancels conditional normalization. A disappearing NEW
query is charged explicitly rather than evaluated using a fabricated posterior. -/
theorem observation_prob_mul_transport_le (old fresh : FinDist α)
    (observe : α → β) (tag : β) :
    (old.map observe).prob tag * conditionalTransportDefect old fresh observe tag ≤
      2 * fiberAtomVariation old fresh observe tag := by
  classical
  have massDifference := abs_observation_prob_sub_le_fiberAtomVariation old fresh observe tag
  have variationNonneg := fiberAtomVariation_nonneg old fresh observe tag
  by_cases oldReached : tag ∈ (old.map observe).support
  · by_cases newReached : tag ∈ (fresh.map observe).support
    · rw [conditionalTransportDefect, if_pos oldReached, if_pos newReached, Finset.mul_sum]
      calc
        _ ≤ ∑ x, ((if observe x = tag then |old.prob x - fresh.prob x| else 0) +
            |(old.map observe).prob tag - (fresh.map observe).prob tag| *
              (fresh.condOnFibre observe tag).prob x) := by
          apply Finset.sum_le_sum
          intro x _
          calc
            _ = |(old.map observe).prob tag * (old.condOnFibre observe tag).prob x -
                (old.map observe).prob tag * (fresh.condOnFibre observe tag).prob x| := by
              rw [← mul_sub, abs_mul, abs_of_nonneg (prob_nonneg _ _)]
            _ ≤ |(old.map observe).prob tag * (old.condOnFibre observe tag).prob x -
                  (fresh.map observe).prob tag * (fresh.condOnFibre observe tag).prob x| +
                |((fresh.map observe).prob tag - (old.map observe).prob tag) *
                  (fresh.condOnFibre observe tag).prob x| := by
              have split := abs_add_le
                ((old.map observe).prob tag * (old.condOnFibre observe tag).prob x -
                  (fresh.map observe).prob tag * (fresh.condOnFibre observe tag).prob x)
                (((fresh.map observe).prob tag - (old.map observe).prob tag) *
                  (fresh.condOnFibre observe tag).prob x)
              convert split using 1 <;> ring
            _ = _ := by
              rw [observation_prob_mul_conditional_prob, observation_prob_mul_conditional_prob,
                abs_mul, abs_of_nonneg (prob_nonneg _ _),
                abs_sub_comm ((fresh.map observe).prob tag) ((old.map observe).prob tag)]
              by_cases same : observe x = tag <;> simp [same]
        _ = fiberAtomVariation old fresh observe tag +
            |(old.map observe).prob tag - (fresh.map observe).prob tag| := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_prob, mul_one]
          rfl
        _ ≤ _ := by linarith
    · rw [conditionalTransportDefect, if_pos oldReached, if_neg newReached, mul_one]
      rw [prob_eq_zero_iff.mpr newReached, sub_zero,
        abs_of_nonneg (prob_nonneg _ _)] at massDifference
      linarith
  · rw [conditionalTransportDefect, if_neg oldReached, mul_zero]
    exact mul_nonneg (by norm_num) variationNonneg

/-- A relative unnormalized FIBER rate controls supported conditional error.
There is no minimum query mass, full-support or equality-of-marginals premise. -/
theorem conditionalTransportDefect_le_of_fiberRate (old fresh : FinDist α)
    (observe : α → β) (tag : β) (reached : tag ∈ (old.map observe).support)
    (rate : ℝ) (small : fiberAtomVariation old fresh observe tag ≤
      rate * (old.map observe).prob tag) :
    conditionalTransportDefect old fresh observe tag ≤ 2 * rate := by
  have positive := prob_pos_iff.mpr reached
  have estimate := observation_prob_mul_transport_le old fresh observe tag
  nlinarith

/-- A pointwise source-atom relative rate implies the fiber rate. This is a
sufficient source hypothesis, not a purported consequence of child Nash. -/
theorem fiberAtomVariation_le_of_atomRate (old fresh : FinDist α)
    (observe : α → β) (tag : β) (rate : ℝ)
    (small : ∀ x, |old.prob x - fresh.prob x| ≤ rate * old.prob x) :
    fiberAtomVariation old fresh observe tag ≤ rate * (old.map observe).prob tag := by
  classical
  rw [observation_prob_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases same : observe x = tag
  · simpa only [same, if_true] using small x
  · simp only [same, if_false, mul_zero, le_refl]

/-- An atomwise source rate yields a query bound independent of query reach. -/
theorem conditionalTransportDefect_le_of_atomRate (old fresh : FinDist α)
    (observe : α → β) (tag : β) (reached : tag ∈ (old.map observe).support)
    (rate : ℝ) (small : ∀ x, |old.prob x - fresh.prob x| ≤ rate * old.prob x) :
    conditionalTransportDefect old fresh observe tag ≤ 2 * rate :=
  conditionalTransportDefect_le_of_fiberRate old fresh observe tag reached rate
    (fiberAtomVariation_le_of_atomRate old fresh observe tag rate small)

/-- Query-dependent weights can be moved back to the unnormalized source atoms.
The observation type itself need not be finite; only the source carrier is. -/
theorem expect_weighted_transport_le (old fresh : FinDist α) (observe : α → β)
    (weight : β → ℝ) (nonneg : ∀ tag, 0 ≤ weight tag) :
    (old.map observe).expect (fun tag => weight tag *
      conditionalTransportDefect old fresh observe tag) ≤
      2 * ∑ x, weight (observe x) * |old.prob x - fresh.prob x| := by
  classical
  let tags := (Finset.univ : Finset α).image observe
  have contains : (old.map observe).support ⊆ (tags : Set β) := by
    intro tag reached
    rw [support_map] at reached
    obtain ⟨x, _, same⟩ := reached
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, same⟩
  rw [expect_eq_sum_of_subset _ _ tags contains]
  calc
    _ ≤ ∑ tag ∈ tags, 2 * (weight tag * fiberAtomVariation old fresh observe tag) := by
      apply Finset.sum_le_sum
      intro tag _
      have bound := mul_le_mul_of_nonneg_left
        (observation_prob_mul_transport_le old fresh observe tag) (nonneg tag)
      nlinarith only [bound]
    _ = 2 * ∑ x, weight (observe x) * |old.prob x - fresh.prob x| := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [fiberAtomVariation, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single (observe x)]
      · simp
      · intro tag _ different
        simp only [Ne.symm different, if_false, mul_zero]
      · intro absent
        exact (absent (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)).elim

/-- The OLD-observation expected conditional defect is controlled by twice the
source-law L1 distance, even when queries appear or disappear. -/
theorem expect_transport_le_atomVariation (old fresh : FinDist α) (observe : α → β) :
    (old.map observe).expect (conditionalTransportDefect old fresh observe) ≤
      2 * atomVariation old fresh := by
  simpa only [one_mul, atomVariation] using
    expect_weighted_transport_le old fresh observe (fun _ => 1) (fun _ => by norm_num)

/-- An information-local change of measure preserves the source-atom rate with
its ACTUAL density. Dropping that density is not valid for arbitrary opponents. -/
theorem expect_transport_le_of_density (old fresh actual : FinDist α)
    (observe : α → β) (density gate : β → ℝ)
    (densityNonneg : ∀ tag, 0 ≤ density tag) (gateNonneg : ∀ tag, 0 ≤ gate tag)
    (change : ∀ x, actual.prob x = old.prob x * density (observe x)) :
    actual.expect (fun x => gate (observe x) *
      conditionalTransportDefect old fresh observe (observe x)) ≤
      2 * ∑ x, (density (observe x) * gate (observe x)) *
        |old.prob x - fresh.prob x| := by
  calc
    _ = (old.map observe).expect (fun tag => (density tag * gate tag) *
        conditionalTransportDefect old fresh observe tag) := by
      rw [expect_map, expect_eq_sum, expect_eq_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [change]
      ring
    _ ≤ _ := expect_weighted_transport_le old fresh observe (fun tag => density tag * gate tag)
      (fun tag => mul_nonneg (densityNonneg tag) (gateNonneg tag))

end GameTheory.Math.Probability.FinDist
