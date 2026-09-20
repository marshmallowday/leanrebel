/-
# Conditioning respects event equality on the supported domain

Two events may differ outside the actual law without changing a conditional.
The same fact applies to lossless encodings of observed fibers. No PMF
representation, finiteness of the carrier, or positive lower bound is used.
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

end GameTheory.Math.Probability.FinDist
