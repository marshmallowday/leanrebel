/-
# Conditional expectations through label-preserving kernels

Finite-support execution can be conditioned before or after a kernel when the
observed label is retained. Supported fibers use their actual masses; jointly
absent fibers keep the same total original-law fallback.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {A B Label : Type*}

open Classical in
/-- A supported conditional value is its gated numerator divided by the
actual label mass. No uniform positive lower bound is required. -/
theorem condOnFibre_expect_div (law : FinDist A) (tag : A → Label)
    (label : Label) (value : A → ℝ) (present : label ∈ (law.map tag).support) :
    (law.condOnFibre tag label).expect value =
      (law.expect fun a => if tag a = label then value a else 0) /
        (law.map tag).prob label := by
  classical
  have possible : ∃ a ∈ tag ⁻¹' {label}, a ∈ law.support := by
    rw [FinDist.support_map] at present
    obtain ⟨a, ha, equal⟩ := present
    exact ⟨a, equal, ha⟩
  dsimp only [FinDist.condOnFibre]
  rw [dif_pos possible]
  calc
    _ = (law.condOn (tag ⁻¹' {label}) possible).expect
        (fun a => if tag a = label then value a else 0) := by
      apply FinDist.expect_congr
      intro a ha
      exact (if_pos (FinDist.support_condOn law _ possible ha).1).symm
    _ = _ := by
      rw [FinDist.expect_condOn_eq_div_of_eq_zero_off]
      · rw [FinDist.prob_map_eq_probOf_preimage_singleton]
      · intro a _ outside
        exact if_neg outside

/-- The total convention for an absent label remains the original law. -/
theorem condOnFibre_expect_absent (law : FinDist A) (tag : A → Label)
    (label : Label) (value : A → ℝ) (absent : label ∉ (law.map tag).support) :
    (law.condOnFibre tag label).expect value = law.expect value := by
  classical
  have impossible : ¬ ∃ a ∈ tag ⁻¹' {label}, a ∈ law.support := by
    rintro ⟨a, equal, ha⟩
    apply absent
    rw [FinDist.support_map]
    exact ⟨a, ha, equal⟩
  dsimp only [FinDist.condOnFibre]
  rw [dif_neg impossible]

/-- Execution preserves the entire law of a remembered label, not merely
the set of possible labels. The hypothesis is checked on supported transitions. -/
theorem map_bind_of_retained (law : FinDist A) (kernel : A → FinDist B)
    (before : A → Label) (after : B → Label)
    (retained : ∀ a ∈ law.support, ∀ b ∈ (kernel a).support, after b = before a) :
    ((law.bind kernel).map after) = law.map before := by
  rw [FinDist.map_bind, FinDist.map_eq_bind before]
  apply FinDist.bind_congr
  intro a ha
  calc
    (kernel a).map after = (kernel a).map (fun _ => before a) :=
      FinDist.map_congr_of_eq_on_support (fun b hb => retained a ha b hb)
    _ = _ := FinDist.map_const _ _

/-- A remembered-label conditional can be taken before or after execution.
Both supported conditionals and the common absent-label fallback are covered. -/
theorem condOnFibre_expect_bind (law : FinDist A) (kernel : A → FinDist B)
    (before : A → Label) (after : B → Label)
    (retained : ∀ a ∈ law.support, ∀ b ∈ (kernel a).support, after b = before a)
    (label : Label) (value : B → ℝ) :
    ((law.bind kernel).condOnFibre after label).expect value =
      (law.condOnFibre before label).expect (fun a => (kernel a).expect value) := by
  classical
  have labels := map_bind_of_retained law kernel before after retained
  by_cases present : label ∈ (law.map before).support
  · have later : label ∈ ((law.bind kernel).map after).support := by
      rw [labels]
      exact present
    rw [condOnFibre_expect_div _ _ _ _ later,
      condOnFibre_expect_div _ _ _ _ present, labels, FinDist.expect_bind]
    congr 1
    apply FinDist.expect_congr
    intro a ha
    by_cases same : before a = label
    · simp only [if_pos same]
      apply FinDist.expect_congr
      intro b hb
      rw [retained a ha b hb, if_pos same]
    · rw [if_neg same]
      calc
        _ = (kernel a).expect (fun _ => (0 : ℝ)) := by
          apply FinDist.expect_congr
          intro b hb
          rw [retained a ha b hb, if_neg same]
        _ = 0 := FinDist.expect_const _ _
  · have later : label ∉ ((law.bind kernel).map after).support := by
      rw [labels]
      exact present
    rw [condOnFibre_expect_absent _ _ _ _ later,
      condOnFibre_expect_absent _ _ _ _ present, FinDist.expect_bind]

/-- Deterministic recoding is a special case of the same conditional law
identity, including labels absent from the pushforward. -/
theorem condOnFibre_expect_map (law : FinDist A) (encode : A → B) (tag : B → Label)
    (label : Label) (value : B → ℝ) :
    ((law.map encode).condOnFibre tag label).expect value =
      (law.condOnFibre (fun a => tag (encode a)) label).expect
        (fun a => value (encode a)) := by
  have retained : ∀ a ∈ law.support, ∀ b ∈ (FinDist.pure (encode a)).support,
      tag b = tag (encode a) := by
    intro a _ b hb
    rw [FinDist.mem_support_pure] at hb
    subst b
    rfl
  simpa only [FinDist.map_eq_bind, FinDist.expect_pure] using
    condOnFibre_expect_bind law (fun a => FinDist.pure (encode a))
      (fun a => tag (encode a)) tag retained label value


end GameTheory.Math.Probability.FinDist
