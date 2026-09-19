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

/-- Restricting a value to live leaves commutes with conditioning on the
information state and live flag. No terminal-status observability assumption
is smuggled into the player's policy type. -/
theorem conditionalOracle_live_value (law : FinDist Leaf) (observe : Leaf → Info)
    (live : Leaf → Bool) (value : Leaf → ℝ) (tag : Info × Bool)
    (sampled : tag ∈ (law.map (fun leaf => (observe leaf, live leaf))).support) :
    conditionalOracleValue law (fun leaf => (observe leaf, live leaf))
        (fun leaf => if live leaf = true then value leaf else 0) tag =
      if tag.2 = true then
        conditionalOracleValue law (fun leaf => (observe leaf, live leaf)) value tag else 0 := by
  unfold conditionalOracleValue
  by_cases active : tag.2 = true
  · rw [if_pos active]
    apply FinDist.expect_congr
    intro leaf reached
    have same := congrArg Prod.snd (conditionalOracle_support law
      (fun leaf => (observe leaf, live leaf)) tag sampled leaf reached)
    rw [if_pos (same.trans active)]
  · rw [if_neg active]
    calc
      _ = (law.condOnFibre (fun leaf => (observe leaf, live leaf)) tag).expect
          (fun _ => (0 : ℝ)) := by
        apply FinDist.expect_congr
        intro leaf reached
        have same := congrArg Prod.snd (conditionalOracle_support law
          (fun leaf => (observe leaf, live leaf)) tag sampled leaf reached)
        rw [if_neg (fun h => active (same.symm.trans h))]
      _ = 0 := FinDist.expect_const _ _

/-- Exact terminal rewards plus approximate LIVE conditional values have the
same delta backup bound under every dominated unilateral law. The prediction
is not queried at a terminal leaf, and no accuracy premise is imposed there. -/
theorem terminalExact_reweight_error (reference alternative : FinDist Leaf)
    (observe : Leaf → Info) (live : Leaf → Bool) (weight : Info → ℝ)
    (density : ∀ leaf, alternative.prob leaf = reference.prob leaf * weight (observe leaf))
    (value : Leaf → ℝ) (prediction : Info → ℝ) (error : ℝ) (nonneg : 0 ≤ error)
    (accurate : ∀ info,
      (info, true) ∈ (reference.map (fun leaf => (observe leaf, live leaf))).support →
      |prediction info - conditionalOracleValue reference
        (fun leaf => (observe leaf, live leaf)) value (info, true)| ≤ error) :
    |alternative.expect (fun leaf =>
        if live leaf = true then prediction (observe leaf) else value leaf) -
      alternative.expect value| ≤ error := by
  have estimate := conditionalOracle_reweight_error reference alternative
    (fun leaf => (observe leaf, live leaf)) (fun tag : Info × Bool => weight tag.1)
    density (fun leaf => if live leaf = true then value leaf else 0)
    (fun tag => if tag.2 = true then prediction tag.1 else 0) error (by
      intro tag sampled
      rw [conditionalOracle_live_value reference observe live value tag sampled]
      rcases tag with ⟨info, flag⟩
      cases flag
      · simpa using nonneg
      · simpa using accurate info sampled)
  have identity :
      alternative.expect (fun leaf =>
          if live leaf = true then prediction (observe leaf) else value leaf) -
        alternative.expect value =
      (alternative.map (fun leaf => (observe leaf, live leaf))).expect
          (fun tag => if tag.2 = true then prediction tag.1 else 0) -
        alternative.expect (fun leaf => if live leaf = true then value leaf else 0) := by
    rw [FinDist.expect_map, ← FinDist.expect_sub, ← FinDist.expect_sub]
    apply FinDist.expect_congr
    intro leaf _
    dsimp only
    by_cases active : live leaf = true <;> simp [active]
  rw [identity]
  exact estimate

/-- When no sampled leaf is live, the backup is exact for every prediction,
including an arbitrarily inaccurate one. This is the no-oracle boundary. -/
theorem terminalExact_no_live (law : FinDist Leaf) (observe : Leaf → Info)
    (live : Leaf → Bool) (value : Leaf → ℝ) (prediction : Info → ℝ)
    (stopped : ∀ leaf ∈ law.support, live leaf ≠ true) :
    law.expect (fun leaf => if live leaf = true then prediction (observe leaf) else value leaf) =
      law.expect value := by
  apply FinDist.expect_congr
  intro leaf reached
  exact if_neg (stopped leaf reached)

end GameTheory.ReBeL
