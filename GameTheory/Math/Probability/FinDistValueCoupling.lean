/-
# One-sided payoff comparison through finite couplings

A coupling keeps both actual marginals. Its directed cost charges only an
increase of the selected payoff, not a change of outcome labels. No symmetry,
independence, optimal transport construction or probability floor is assumed.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Math.Probability.FinDist

universe u v
variable {α : Type u} {β : Type v}

/-- Expected positive new-minus-old payoff under one explicit joint law. -/
def directedValueCost (joint : FinDist (α × β)) (oldValue : α → ℝ)
    (newValue : β → ℝ) : ℝ :=
  joint.expect fun pair => max 0 (newValue pair.2 - oldValue pair.1)

/-- Directed payoff cost is nonnegative without any marginal assumptions. -/
theorem directedValueCost_nonneg (joint : FinDist (α × β)) (oldValue : α → ℝ)
    (newValue : β → ℝ) : 0 ≤ directedValueCost joint oldValue newValue := by
  have lower := expect_mono (μ := joint) (u := fun _ => (0 : ℝ))
    (fun pair _ => le_max_left 0 (newValue pair.2 - oldValue pair.1))
  simpa only [directedValueCost, expect_const] using lower

/-- The exact marginal identities, not independent resampling, justify the
one-sided expectation comparison. Decreases in payoff need no allowance. -/
theorem expect_sub_le_directedValueCost (old : FinDist α) (fresh : FinDist β)
    (joint : FinDist (α × β)) (oldValue : α → ℝ) (newValue : β → ℝ)
    (oldMarginal : joint.map Prod.fst = old) (newMarginal : joint.map Prod.snd = fresh) :
    fresh.expect newValue - old.expect oldValue ≤ directedValueCost joint oldValue newValue := by
  rw [← oldMarginal, ← newMarginal, expect_map, expect_map, ← expect_sub]
  exact expect_mono (fun pair _ => le_max_right 0 (newValue pair.2 - oldValue pair.1))

/-- A supported pairwise payoff bound supplies a quantitative cost. No
condition is imposed on pairs outside the support of the proposed coupling. -/
theorem directedValueCost_le_of_support (joint : FinDist (α × β))
    (oldValue : α → ℝ) (newValue : β → ℝ) (error : ℝ) (nonneg : 0 ≤ error)
    (bounded : ∀ pair ∈ joint.support, newValue pair.2 - oldValue pair.1 ≤ error) :
    directedValueCost joint oldValue newValue ≤ error := by
  apply expect_le_of_forall
  intro pair reached
  exact max_le nonneg (bounded pair reached)

/-- A coupling supported on non-increasing payoff pairs has exactly zero
cost, even when its two outcome laws have disjoint supports. -/
theorem directedValueCost_eq_zero_of_support (joint : FinDist (α × β))
    (oldValue : α → ℝ) (newValue : β → ℝ)
    (decreasing : ∀ pair ∈ joint.support, newValue pair.2 ≤ oldValue pair.1) :
    directedValueCost joint oldValue newValue = 0 := by
  apply le_antisymm
  · exact directedValueCost_le_of_support joint oldValue newValue 0 (le_refl _)
      (fun pair reached => sub_nonpos.mpr (decreasing pair reached))
  · exact directedValueCost_nonneg joint oldValue newValue


section SummaryCoupling

variable {S : Type*}

/-- Couple two finite laws by matching a common summary, then condition the
second law inside that summary. The first outcome is sampled only once. -/
def summaryCoupling (first : FinDist α) (second : FinDist β)
    (left : α → S) (right : β → S) : FinDist (α × β) :=
  first.bind fun a => (second.condOnFibre right (left a)).map fun b => (a, b)

/-- The first marginal is exact even before equal summary laws are proved. -/
theorem summaryCoupling_fst (first : FinDist α) (second : FinDist β)
    (left : α → S) (right : β → S) :
    (summaryCoupling first second left right).map Prod.fst = first := by
  rw [summaryCoupling, map_bind]
  calc
    _ = first.bind (fun a => pure a) := by
      apply bind_congr
      intro a _
      rw [map_comp]
      exact map_const _ a
    _ = first := bind_pure _

/-- Equal summary laws recover the complete second marginal, including every
positive atom. Matching means alone would not justify this identity. -/
theorem summaryCoupling_snd (first : FinDist α) (second : FinDist β)
    (left : α → S) (right : β → S) (same : first.map left = second.map right) :
    (summaryCoupling first second left right).map Prod.snd = second := by
  rw [summaryCoupling, map_bind]
  calc
    _ = first.bind (fun a => second.condOnFibre right (left a)) := by
      apply bind_congr
      intro a _
      rw [map_comp]
      exact map_id _
    _ = (first.map left).bind (second.condOnFibre right) := (bind_map _ _ _).symm
    _ = second := by rw [same, ← eq_bind_condOnFibre]

/-- Every constructed pair has positive mass in both input laws and equal
summaries. No unsupported conditional fallback is used in the coupling. -/
theorem summaryCoupling_support (first : FinDist α) (second : FinDist β)
    (left : α → S) (right : β → S) (same : first.map left = second.map right)
    (pair : α × β) (reached : pair ∈ (summaryCoupling first second left right).support) :
    pair.1 ∈ first.support ∧ pair.2 ∈ second.support ∧ left pair.1 = right pair.2 := by
  classical
  rw [summaryCoupling, support_bind] at reached
  obtain ⟨a, ha, hab⟩ := Set.mem_iUnion₂.mp reached
  rw [support_map] at hab
  obtain ⟨b, hb, equal⟩ := hab
  subst pair
  have present : left a ∈ (second.map right).support := by
    rw [← same, support_map]
    exact ⟨a, ha, rfl⟩
  rw [support_map] at present
  obtain ⟨witness, hw, tag⟩ := present
  have positive : ∃ b ∈ right ⁻¹' {left a}, b ∈ second.support :=
    ⟨witness, tag, hw⟩
  rw [condOnFibre, dif_pos positive] at hb
  have supported := support_condOn second _ positive hb
  have tagEqual : right b = left a := supported.1
  exact ⟨ha, supported.2, tagEqual.symm⟩

/-- A payoff diameter within matched summaries bounds the constructed cost.
The only law premise is equality of summary distributions, not a coupling
witness or a bound on the final expected payoff difference. -/
theorem directedValueCost_summaryCoupling_le (first : FinDist α) (second : FinDist β)
    (left : α → S) (right : β → S) (same : first.map left = second.map right)
    (firstValue : α → ℝ) (secondValue : β → ℝ) (error : ℝ) (nonneg : 0 ≤ error)
    (bounded : ∀ a ∈ first.support, ∀ b ∈ second.support,
      left a = right b → secondValue b - firstValue a ≤ error) :
    directedValueCost (summaryCoupling first second left right) firstValue secondValue ≤
      error := by
  apply directedValueCost_le_of_support _ _ _ error nonneg
  intro pair reached
  obtain ⟨ha, hb, sameTag⟩ := summaryCoupling_support first second left right same pair reached
  exact bounded pair.1 ha pair.2 hb sameTag

/-- Equal payoff distributions construct a zero-cost coupling, even when
the history supports are disjoint and the payoff is not constant. -/
theorem directedValueCost_summaryCoupling_payoff (first : FinDist α) (second : FinDist β)
    (firstValue : α → ℝ) (secondValue : β → ℝ)
    (same : first.map firstValue = second.map secondValue) :
    directedValueCost (summaryCoupling first second firstValue secondValue)
      firstValue secondValue = 0 := by
  apply le_antisymm
  · apply directedValueCost_summaryCoupling_le first second firstValue secondValue same
      firstValue secondValue 0 (le_refl _)
    intro a _ b _ equal
    exact sub_nonpos.mpr equal.ge
  · exact directedValueCost_nonneg _ _ _

end SummaryCoupling

end GameTheory.Math.Probability.FinDist
