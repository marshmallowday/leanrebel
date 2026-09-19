/-
# Reusing one information-value vector after a policy change

A unilateral change of perfect-recall policy changes own reach by a factor
measurable at the information state. These finite-law lemmas isolate exactly
that condition. The reference joint law and continuation values stay fixed:
no new oracle is queried for each deviation. Normalization of the alternative
law preserves the original error constant, even for large density ratios.
-/

import GameTheory.ReBeL.ConditionalOracle

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Math.Probability

variable {Leaf Info : Type*}

/-- An information-local density computes expectations under the changed law.
No independence of the hidden components of the reference law is required. -/
theorem informationReweight_expect (reference alternative : FinDist Leaf)
    (observe : Leaf → Info) (weight : Info → ℝ)
    (density : ∀ leaf, alternative.prob leaf = reference.prob leaf * weight (observe leaf))
    (value : Leaf → ℝ) :
    alternative.expect value =
      reference.expect (fun leaf => weight (observe leaf) * value leaf) := by
  unfold FinDist.expect
  apply tsum_congr
  intro leaf
  rw [density, mul_assoc]

/-- A changed policy cannot create mass outside a dominating reference law.
The reference can dominate counterfactual play while factual own reach is zero. -/
theorem informationReweight_support (reference alternative : FinDist Leaf)
    (observe : Leaf → Info) (weight : Info → ℝ)
    (density : ∀ leaf, alternative.prob leaf = reference.prob leaf * weight (observe leaf)) :
    alternative.support ⊆ reference.support := by
  intro leaf reached
  by_contra absent
  have hzero : alternative.prob leaf = 0 := by
    rw [density, FinDist.prob_eq_zero_iff.mpr absent, zero_mul]
  exact (FinDist.prob_eq_zero_iff.mp hzero) reached

/-- The SAME exact conditional vector backs up correctly under every
normalized law with an information-local density. In particular the factor
must not depend on unobserved history within an information fiber. -/
theorem conditionalOracle_reweight_exact (reference alternative : FinDist Leaf)
    (observe : Leaf → Info) (weight : Info → ℝ)
    (density : ∀ leaf, alternative.prob leaf = reference.prob leaf * weight (observe leaf))
    (value : Leaf → ℝ) :
    (alternative.map observe).expect (conditionalOracleValue reference observe value) =
      alternative.expect value := by
  rw [FinDist.expect_map, informationReweight_expect reference alternative observe weight density,
    informationReweight_expect reference alternative observe weight density]
  simpa only [FinDist.expect_map] using
    (conditionalOracle_weighted_expect reference observe value weight).symm

/-- A uniform error of delta in a single reference vector remains delta after
any normalized information-local reweighting. Unlike a crude weighted bound,
this does not multiply delta by a worst-case inverse reach probability. -/
theorem conditionalOracle_reweight_error (reference alternative : FinDist Leaf)
    (observe : Leaf → Info) (weight : Info → ℝ)
    (density : ∀ leaf, alternative.prob leaf = reference.prob leaf * weight (observe leaf))
    (value : Leaf → ℝ) (prediction : Info → ℝ) (error : ℝ)
    (accurate : ∀ info ∈ (reference.map observe).support,
      |prediction info - conditionalOracleValue reference observe value info| ≤ error) :
    |(alternative.map observe).expect prediction - alternative.expect value| ≤ error := by
  rw [← conditionalOracle_reweight_exact reference alternative observe weight density value,
    ← FinDist.expect_sub]
  apply FinDist.abs_expect_le_of_abs_bound
  intro info sampled
  apply accurate
  rw [FinDist.support_map] at sampled ⊢
  obtain ⟨leaf, reached, same⟩ := sampled
  exact ⟨leaf, informationReweight_support reference alternative observe weight density reached,
    same⟩

/-- A fiber's probability changes by its one information-local density factor. -/
theorem informationReweight_fiber_mass (reference alternative : FinDist Leaf)
    (observe : Leaf → Info) (weight : Info → ℝ)
    (density : ∀ leaf, alternative.prob leaf = reference.prob leaf * weight (observe leaf))
    (info : Info) :
    alternative.probOf (observe ⁻¹' {info}) =
      weight info * reference.probOf (observe ⁻¹' {info}) := by
  classical
  rw [← FinDist.expect_indicator_eq_probOf, informationReweight_expect reference alternative
    observe weight density, ← FinDist.expect_indicator_eq_probOf, ← FinDist.expect_smul]
  apply FinDist.expect_congr
  intro leaf _
  by_cases same : observe leaf = info
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, same, if_true]
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, same, if_false, mul_zero]

/-- On positive-probability observations the reference and changed laws have
identical hidden-history conditionals. Zero-mass observations are deliberately
not equated: their total fallbacks are not posteriors. -/
theorem informationReweight_conditional (reference alternative : FinDist Leaf)
    (observe : Leaf → Info) (weight : Info → ℝ)
    (density : ∀ leaf, alternative.prob leaf = reference.prob leaf * weight (observe leaf))
    (info : Info) (sampled : info ∈ (alternative.map observe).support) :
    alternative.condOnFibre observe info = reference.condOnFibre observe info := by
  classical
  have altPossible : ∃ leaf ∈ observe ⁻¹' {info}, leaf ∈ alternative.support := by
    rw [FinDist.support_map] at sampled
    obtain ⟨leaf, reached, same⟩ := sampled
    exact ⟨leaf, same, reached⟩
  have refPossible : ∃ leaf ∈ observe ⁻¹' {info}, leaf ∈ reference.support := by
    obtain ⟨leaf, same, reached⟩ := altPossible
    exact ⟨leaf, same,
      informationReweight_support reference alternative observe weight density reached⟩
  have mass := informationReweight_fiber_mass reference alternative observe weight density info
  have weight_ne : weight info ≠ 0 := by
    intro zero
    have positive := FinDist.probOf_pos altPossible
    rw [mass, zero, zero_mul] at positive
    exact lt_irrefl _ positive
  rw [FinDist.condOnFibre, dif_pos altPossible, FinDist.condOnFibre, dif_pos refPossible]
  apply FinDist.ext_of_prob
  intro leaf
  rw [FinDist.prob_condOn, FinDist.prob_condOn]
  by_cases same : observe leaf = info
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, same, if_true]
    rw [density, same, mass]
    field_simp
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, same, if_false]

/-- Thus a reference value vector is also the ordinary posterior value vector
on every observation that the changed policy actually reaches. -/
theorem conditionalOracle_reweight_value (reference alternative : FinDist Leaf)
    (observe : Leaf → Info) (weight : Info → ℝ)
    (density : ∀ leaf, alternative.prob leaf = reference.prob leaf * weight (observe leaf))
    (info : Info) (sampled : info ∈ (alternative.map observe).support) (value : Leaf → ℝ) :
    conditionalOracleValue alternative observe value info =
      conditionalOracleValue reference observe value info := by
  unfold conditionalOracleValue
  rw [informationReweight_conditional reference alternative observe weight density info sampled]

end GameTheory.ReBeL
