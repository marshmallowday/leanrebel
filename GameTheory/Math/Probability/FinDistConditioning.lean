/-
# Supported conditioning: exact recoding and bounded transport

Two events may differ outside the actual law without changing a conditional.
The same fact applies to lossless encodings of observed fibers. No PMF
representation or positive lower bound is used. The transport section uses a
finite carrier to measure changed conditionals and explicitly charge lost support.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Math.Probability.FinDist

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- Conditioning on events agreeing everywhere with positive mass gives the
same law. Equal events outside the support are deliberately not required. -/
theorem condOn_eq_of_support_iff (law : FinDist α) (first second : Set α)
    (firstPossible : ∃ x ∈ first, x ∈ law.support)
    (secondPossible : ∃ x ∈ second, x ∈ law.support)
    (same : ∀ x ∈ law.support, x ∈ first ↔ x ∈ second) :
    law.condOn first firstPossible = law.condOn second secondPossible := by
  have contained : (law.condOn first firstPossible).support ⊆ second := by
    intro x reached
    have member := support_condOn law first firstPossible reached
    exact (same x member.2).mp member.1
  have smaller : second ∩ law.support ⊆ first := by
    intro x member
    exact (same x member.2).mpr member.1
  have possible : ∃ x ∈ second, x ∈ (law.condOn first firstPossible).support := by
    obtain ⟨x, reached⟩ := (law.condOn first firstPossible).support_nonempty
    exact ⟨x, contained reached, reached⟩
  calc
    _ = (law.condOn first firstPossible).condOn second possible :=
      (condOn_of_support_subset _ second possible contained).symm
    _ = _ := condOn_condOn law firstPossible secondPossible smaller possible

/-- Lossless observation recoding preserves its conditional law. This also
handles the jointly empty fiber, where both total conditionals use the SAME
original-law fallback, not unrelated fabricated posteriors. -/
theorem condOnFibre_eq_of_support_iff (law : FinDist α) (first : α → β) (second : α → γ)
    (left : β) (right : γ)
    (same : ∀ x ∈ law.support, first x = left ↔ second x = right) :
    law.condOnFibre first left = law.condOnFibre second right := by
  classical
  by_cases possible : ∃ x ∈ first ⁻¹' {left}, x ∈ law.support
  · have other : ∃ x ∈ second ⁻¹' {right}, x ∈ law.support := by
      obtain ⟨x, equal, reached⟩ := possible
      exact ⟨x, (same x reached).mp equal, reached⟩
    rw [condOnFibre, dif_pos possible, condOnFibre, dif_pos other]
    exact condOn_eq_of_support_iff law _ _ possible other same
  · have absent : ¬ ∃ x ∈ second ⁻¹' {right}, x ∈ law.support := by
      rintro ⟨x, equal, reached⟩
      exact possible ⟨x, (same x reached).mpr equal, reached⟩
    simp only [condOnFibre, dif_neg possible, dif_neg absent]


section Transport

variable [Fintype α]

/-- Query-local transport cost. An absent OLD query costs zero because it is
not used; an OLD-only query costs one rather than consulting a NEW fallback.
On jointly supported queries this is the L1 distance of the actual conditionals. -/
def conditionalTransportDefect (old fresh : FinDist α) (observe : α → β) (tag : β) : ℝ := by
  classical
  exact if tag ∈ (old.map observe).support then
    if tag ∈ (fresh.map observe).support then
      ∑ x, |(old.condOnFibre observe tag).prob x - (fresh.condOnFibre observe tag).prob x|
    else 1
  else 0

/-- Transport costs are nonnegative, including disappearing and absent queries. -/
theorem conditionalTransportDefect_nonneg (old fresh : FinDist α)
    (observe : α → β) (tag : β) : 0 ≤ conditionalTransportDefect old fresh observe tag := by
  classical
  unfold conditionalTransportDefect
  split_ifs
  · exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · norm_num
  · exact le_refl _

/-- The cost is at most two, without a uniform positive atom-mass premise. -/
theorem conditionalTransportDefect_le_two (old fresh : FinDist α)
    (observe : α → β) (tag : β) : conditionalTransportDefect old fresh observe tag ≤ 2 := by
  classical
  unfold conditionalTransportDefect
  split_ifs
  · calc
      _ ≤ ∑ x, ((old.condOnFibre observe tag).prob x +
          (fresh.condOnFibre observe tag).prob x) := by
        apply Finset.sum_le_sum
        intro x _
        have first := prob_nonneg (old.condOnFibre observe tag) x
        have second := prob_nonneg (fresh.condOnFibre observe tag) x
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      _ = 2 := by rw [Finset.sum_add_distrib, sum_prob, sum_prob]; norm_num
  · norm_num
  · norm_num

/-- Equal supported conditionals cost zero; unsupported OLD queries remain unused. -/
theorem conditionalTransportDefect_eq_zero (old fresh : FinDist α)
    (observe : α → β) (tag : β)
    (covered : tag ∈ (old.map observe).support → tag ∈ (fresh.map observe).support)
    (same : tag ∈ (old.map observe).support →
      old.condOnFibre observe tag = fresh.condOnFibre observe tag) :
    conditionalTransportDefect old fresh observe tag = 0 := by
  classical
  by_cases sampled : tag ∈ (old.map observe).support
  · simp only [conditionalTransportDefect, if_pos sampled, if_pos (covered sampled),
      same sampled, sub_self, abs_zero, Finset.sum_const_zero]
  · simp only [conditionalTransportDefect, if_neg sampled]

/-- Transfer a supported NEW query's upper bound to the OLD conditional.
If the NEW query has disappeared, use the bounded observable directly and
charge the explicit support defect. No fictitious NEW posterior is consulted. -/
theorem condOnFibre_expect_le_add_transport (old fresh : FinDist α)
    (observe : α → β) (tag : β) (sampled : tag ∈ (old.map observe).support)
    (value : α → ℝ) (bound loss : ℝ) (nonneg : 0 ≤ loss)
    (bounded : ∀ x, |value x| ≤ bound)
    (quality : tag ∈ (fresh.map observe).support →
      (fresh.condOnFibre observe tag).expect value ≤ loss) :
    (old.condOnFibre observe tag).expect value ≤
      loss + bound * conditionalTransportDefect old fresh observe tag := by
  classical
  by_cases present : tag ∈ (fresh.map observe).support
  · rw [conditionalTransportDefect, if_pos sampled, if_pos present]
    have distance :
        |(old.condOnFibre observe tag).expect value -
          (fresh.condOnFibre observe tag).expect value| ≤
        bound * ∑ x, |(old.condOnFibre observe tag).prob x -
          (fresh.condOnFibre observe tag).prob x| := by
      calc
        _ = |∑ x, ((old.condOnFibre observe tag).prob x -
            (fresh.condOnFibre observe tag).prob x) * value x| := by
          rw [expect_eq_sum, expect_eq_sum, ← Finset.sum_sub_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ ≤ ∑ x, |((old.condOnFibre observe tag).prob x -
            (fresh.condOnFibre observe tag).prob x) * value x| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ x, bound * |(old.condOnFibre observe tag).prob x -
            (fresh.condOnFibre observe tag).prob x| := by
          apply Finset.sum_le_sum
          intro x _
          rw [abs_mul]
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left (bounded x)
            (abs_nonneg ((old.condOnFibre observe tag).prob x -
              (fresh.condOnFibre observe tag).prob x))
        _ = _ := (Finset.mul_sum _ _ _).symm
    have upper := (abs_le.mp distance).2
    have localQuality := quality present
    linarith
  · rw [conditionalTransportDefect, if_pos sampled, if_neg present, mul_one]
    have upper := expect_le_of_forall (old.condOnFibre observe tag) value bound
      (fun x _ => (abs_le.mp (bounded x)).2)
    linarith

end Transport

end GameTheory.Math.Probability.FinDist
