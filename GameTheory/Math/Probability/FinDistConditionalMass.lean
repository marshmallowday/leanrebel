/-
# Conditional event mass averaged with actual query weights

Model-weighted conditional shares integrate to the original event mass.
Other incoming laws retain a source-law variation term. The total conditional
at an absent label is only a fallback, never an observed posterior.
-/

import GameTheory.Math.Probability.FinDistTransportRate

noncomputable section

namespace GameTheory.Math.Probability.FinDist

universe u v
variable {A : Type u} {Label : Type v}

/-- Event probability in the model's total conditional at a query label. -/
def conditionalEventShare (model : FinDist A) (observe : A → Label)
    (event : Set A) (label : Label) : ℝ :=
  (model.condOnFibre observe label).probOf event

/-- Every total conditional event share lies between zero and one. -/
theorem conditionalEventShare_bounds (model : FinDist A) (observe : A → Label)
    (event : Set A) (label : Label) :
    0 ≤ conditionalEventShare model observe event label ∧
      conditionalEventShare model observe event label ≤ 1 := by
  classical
  constructor
  · exact ENNReal.toReal_nonneg
  · unfold conditionalEventShare
    rw [← expect_indicator_eq_probOf]
    apply expect_le_of_forall
    intro x _
    split_ifs <;> norm_num

/-- On a possible query this is precisely event mass divided by reach. -/
theorem conditionalEventShare_eq_ratio (model : FinDist A) (observe : A → Label)
    (event : Set A) (label : Label)
    (possible : ∃ x ∈ observe ⁻¹' {label}, x ∈ model.support) :
    conditionalEventShare model observe event label =
      model.probOf ((observe ⁻¹' {label}) ∩ event) /
        model.probOf (observe ⁻¹' {label}) := by
  rw [conditionalEventShare, condOnFibre, dif_pos possible, probOf_condOn_eq_inter]

/-- Model query weights cancel the conditional normalization exactly.
No finite label carrier or lower bound on query reach is required. -/
theorem expect_conditionalEventShare (model : FinDist A) (observe : A → Label)
    (event : Set A) :
    (model.map observe).expect (conditionalEventShare model observe event) =
      model.probOf event := by
  classical
  calc
    _ = (model.map observe).expect (fun label =>
        (model.condOnFibre observe label).expect (fun x => if x ∈ event then 1 else 0)) := by
      apply expect_congr
      intro label _
      exact (expect_indicator_eq_probOf _ event).symm
    _ = ((model.map observe).bind (model.condOnFibre observe)).expect
        (fun x => if x ∈ event then 1 else 0) := (expect_bind _ _ _).symm
    _ = model.probOf event := by
      rw [← eq_bind_condOnFibre, expect_indicator_eq_probOf]

variable [Fintype A]

/-- Changing actual query weights retains source-law discrepancy. It does
not identify actual histories with the model or condition an absent event. -/
theorem expect_conditionalEventShare_le (actual model : FinDist A)
    (observe : A → Label) (event : Set A) :
    (actual.map observe).expect (conditionalEventShare model observe event) ≤
      model.probOf event + atomVariation actual model := by
  have distance := abs_expect_sub_le_atomVariation actual model
    (fun x => conditionalEventShare model observe event (observe x)) 1 (by
      intro x
      obtain ⟨lower, upper⟩ := conditionalEventShare_bounds model observe event (observe x)
      rw [abs_of_nonneg lower]
      exact upper)
  rw [one_mul] at distance
  have modelMean := expect_conditionalEventShare model observe event
  rw [expect_map] at modelMean ⊢
  rw [modelMean] at distance
  have upper := (abs_le.mp distance).2
  linarith only [upper]

/-- Integrate a query-local allowance with the incoming law's own weights.
The coefficient may be zero; no uniform minimum query mass is introduced. -/
theorem expect_le_conditionalEventShare_budget (actual model : FinDist A)
    (observe : A → Label) (event : Set A) (value : Label → ℝ)
    (base coefficient : ℝ) (nonneg : 0 ≤ coefficient)
    (bounded : ∀ label ∈ (actual.map observe).support,
      value label ≤ base + coefficient * conditionalEventShare model observe event label) :
    (actual.map observe).expect value ≤
      base + coefficient * (model.probOf event + atomVariation actual model) := by
  have pointwise := expect_mono bounded
  rw [expect_add, expect_const, expect_smul] at pointwise
  exact pointwise.trans (add_le_add_left
    (mul_le_mul_of_nonneg_left
      (expect_conditionalEventShare_le actual model observe event) nonneg) base)

end GameTheory.Math.Probability.FinDist
