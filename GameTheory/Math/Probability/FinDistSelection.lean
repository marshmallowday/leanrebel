/-
# Conditioning actual tagged executions

Selecting a positive-mass event may correlate an initially independent tag
with an outcome. The conditional tag law is dominated by its original law
with the derived factor 1 / event probability. No support or density
certificate is assumed, and impossible events have no conditioning witness.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Math.Probability.FinDist

universe u v
variable {A : Type u} {B : Type v}

/-- Selection can amplify a nonnegative observable by at most the reciprocal
of the ACTUAL event probability. Nonnegativity is needed only on support. -/
theorem expect_condOn_le_div_of_nonneg (law : FinDist A) (event : Set A)
    (possible : ∃ x ∈ event, x ∈ law.support) (value : A → ℝ)
    (nonneg : ∀ x ∈ law.support, 0 ≤ value x) :
    (law.condOn event possible).expect value ≤ law.expect value / law.probOf event := by
  classical
  calc
    _ = (law.condOn event possible).expect
        (fun x => if x ∈ event then value x else 0) := by
      apply expect_congr
      intro x reached
      exact (if_pos (support_condOn law event possible reached).1).symm
    _ = law.expect (fun x => if x ∈ event then value x else 0) / law.probOf event :=
      expect_condOn_eq_div_of_eq_zero_off law event possible _ (fun _ _ outside => if_neg outside)
    _ ≤ _ := div_le_div_of_nonneg_right
      (expect_mono (fun x reached => by
        split
        · exact le_rfl
        · exact nonneg x reached)) (probOf_pos possible).le

/-- Retain the original tag through a genuine dependent execution kernel and
then select an event in the COMPLETE tag/outcome state. No independence after
selection is inferred. The kernel may depend on the tag in any way. -/
theorem tagged_condOn_expect_le_div (prior : FinDist A) (kernel : A → FinDist B)
    (event : Set (A × B))
    (possible : ∃ x ∈ event,
      x ∈ (prior.bind (fun a => (kernel a).map (fun b => (a, b)))).support)
    (value : A → ℝ) (nonneg : ∀ a, 0 ≤ value a) :
    (((prior.bind (fun a => (kernel a).map (fun b => (a, b)))).condOn event possible).map
      Prod.fst).expect value ≤ prior.expect value /
        (prior.bind (fun a => (kernel a).map (fun b => (a, b)))).probOf event := by
  rw [expect_map]
  have selected := expect_condOn_le_div_of_nonneg
    (prior.bind (fun a => (kernel a).map (fun b => (a, b)))) event possible
    (fun pair => value pair.1) (fun pair _ => nonneg pair.1)
  simpa only [expect_bind, expect_map, expect_const] using selected

/-- Atom domination is DERIVED from the tagged execution and conditioning,
not postulated as a density hypothesis. The factor can be large for rare events. -/
theorem tagged_condOn_prob_le_div (prior : FinDist A) (kernel : A → FinDist B)
    (event : Set (A × B))
    (possible : ∃ x ∈ event,
      x ∈ (prior.bind (fun a => (kernel a).map (fun b => (a, b)))).support)
    (a : A) :
    (((prior.bind (fun a => (kernel a).map (fun b => (a, b)))).condOn event possible).map
      Prod.fst).prob a ≤ prior.prob a /
        (prior.bind (fun a => (kernel a).map (fun b => (a, b)))).probOf event := by
  classical
  have selected := tagged_condOn_expect_le_div prior kernel event possible
    (fun tag => if a = tag then (1 : ℝ) else 0) (fun _ => by split <;> norm_num)
  simpa only [expect_ite_eq, mul_one] using selected

/-- A selected execution cannot introduce a tag absent from the original law.
This covers zero-probability types without assigning them a new posterior. -/
theorem tagged_condOn_support (prior : FinDist A) (kernel : A → FinDist B)
    (event : Set (A × B))
    (possible : ∃ x ∈ event,
      x ∈ (prior.bind (fun a => (kernel a).map (fun b => (a, b)))).support) :
    (((prior.bind (fun a => (kernel a).map (fun b => (a, b)))).condOn event possible).map
      Prod.fst).support ⊆ prior.support := by
  intro a reached
  by_contra absent
  have upper := tagged_condOn_prob_le_div prior kernel event possible a
  rw [prob_eq_zero_iff.mpr absent, zero_div] at upper
  exact (not_le_of_gt (prob_pos_iff.mpr reached)) upper

/-- The actual probability ratio supplies the bounded-density contract.
Its bound is proved on model support; off-support density is exactly zero. -/
theorem tagged_condOn_density (prior : FinDist A) (kernel : A → FinDist B)
    (event : Set (A × B))
    (possible : ∃ x ∈ event,
      x ∈ (prior.bind (fun a => (kernel a).map (fun b => (a, b)))).support) :
    let actual :=
      (((prior.bind (fun a => (kernel a).map (fun b => (a, b)))).condOn event possible).map
        Prod.fst)
    (∀ a, actual.prob a = prior.prob a * (actual.prob a / prior.prob a)) ∧
      (∀ a ∈ prior.support, actual.prob a / prior.prob a ≤
        1 / (prior.bind (fun a => (kernel a).map (fun b => (a, b)))).probOf event) := by
  classical
  dsimp only
  constructor
  · intro a
    by_cases present : a ∈ prior.support
    · field_simp [(prob_pos_iff.mpr present).ne']
    · have absent : a ∉
          (((prior.bind (fun tag => (kernel tag).map (fun b => (tag, b)))).condOn
            event possible).map Prod.fst).support := by
        intro reached
        exact present (tagged_condOn_support prior kernel event possible reached)
      rw [prob_eq_zero_iff.mpr absent, prob_eq_zero_iff.mpr present]
      simp only [zero_div, mul_zero]
  · intro a present
    apply (div_le_iff₀ (prob_pos_iff.mpr present)).mpr
    calc
      _ ≤ prior.prob a /
          (prior.bind (fun a => (kernel a).map (fun b => (a, b)))).probOf event :=
        tagged_condOn_prob_le_div prior kernel event possible a
      _ = _ := by ring

end GameTheory.Math.Probability.FinDist
