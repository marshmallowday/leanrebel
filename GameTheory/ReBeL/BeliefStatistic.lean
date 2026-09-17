/-
# Joint information statistics retain a fixed conditional history kernel

A likelihood that depends only on a joint observation changes the law of that
observation but not the conditional hidden-history kernel of the fixed prior.
Consequently the joint observation law, together with that fixed kernel, is
sufficient. Separate player marginals do not satisfy this theorem.
-/

import GameTheory.ReBeL.CompactBelief

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Math.Probability
open scoped BigOperators

universe uh ui uι

namespace ReachEncoding

variable {H : Type uh} [Fintype H] {I : Type ui}

/-- Multiply a fixed history prior by a likelihood of its observed statistic. -/
def tiltWeights (prior : FinDist H) (observe : H → I) (likelihood : I → ℝ)
    (nonneg : ∀ i, 0 ≤ likelihood i) : ReachWeights H where
  weight h := prior.prob h * likelihood (observe h)
  nonneg h := mul_nonneg (prior.prob_nonneg h) (nonneg (observe h))

/-- Finite Bayes reweighting preserves the usual weighted-expectation formula. -/
theorem expect_tilt (prior : FinDist H) (observe : H → I) (likelihood : I → ℝ)
    (nonneg : ∀ i, 0 ≤ likelihood i)
    (positive : 0 < (tiltWeights prior observe likelihood nonneg).mass) (value : H → ℝ) :
    ((tiltWeights prior observe likelihood nonneg).normalize positive).expect value =
      prior.expect (fun h => likelihood (observe h) * value h) /
        (tiltWeights prior observe likelihood nonneg).mass := by
  rw [FinDist.expect_eq_sum, FinDist.expect_eq_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h _
  rw [ReachWeights.prob_normalize]
  simp only [tiltWeights]
  ring

/-- Reweighting cannot create support where the fixed chance law has zero mass. -/
theorem tilt_support_subset (prior : FinDist H) (observe : H → I) (likelihood : I → ℝ)
    (nonneg : ∀ i, 0 ≤ likelihood i)
    (positive : 0 < (tiltWeights prior observe likelihood nonneg).mass) :
    ((tiltWeights prior observe likelihood nonneg).normalize positive).support ⊆ prior.support := by
  intro h reached
  by_contra missing
  have positiveProb := FinDist.prob_pos_iff.mpr reached
  rw [ReachWeights.prob_normalize] at positiveProb
  simp [tiltWeights, FinDist.prob_eq_zero_iff.mpr missing] at positiveProb

/-- The fixed-prior conditional fallback is never used at a sampled reweighted statistic. -/
theorem tilt_statistic_possible (prior : FinDist H) (observe : H → I) (likelihood : I → ℝ)
    (nonneg : ∀ i, 0 ≤ likelihood i)
    (positive : 0 < (tiltWeights prior observe likelihood nonneg).mass)
    (value : I)
    (reached : value ∈ (((tiltWeights prior observe likelihood nonneg).normalize positive).map
      observe).support) : ∃ h ∈ observe ⁻¹' {value}, h ∈ prior.support := by
  rw [FinDist.support_map] at reached
  obtain ⟨h, support, equal⟩ := reached
  exact ⟨h, equal, tilt_support_subset prior observe likelihood nonneg positive support⟩

/-- Joint statistic sufficiency is derived, with the conditional kernel fixed before
choosing the likelihood. This is stronger than using a posterior-dependent decoder. -/
theorem tilt_reconstruct (prior : FinDist H) (observe : H → I) (likelihood : I → ℝ)
    (nonneg : ∀ i, 0 ≤ likelihood i)
    (positive : 0 < (tiltWeights prior observe likelihood nonneg).mass) :
    (((tiltWeights prior observe likelihood nonneg).normalize positive).map observe).bind
        (prior.condOnFibre observe) =
      (tiltWeights prior observe likelihood nonneg).normalize positive := by
  classical
  apply FinDist.ext_of_prob
  intro target
  rw [FinDist.prob_bind, FinDist.expect_map, expect_tilt, ReachWeights.prob_normalize]
  have fixed := congrArg (fun law : FinDist H => law.prob target)
    (FinDist.eq_bind_condOnFibre prior observe).symm
  rw [FinDist.prob_bind, FinDist.expect_map] at fixed
  have weighted : prior.expect (fun h =>
        likelihood (observe h) * (prior.condOnFibre observe (observe h)).prob target) =
      likelihood (observe target) * prior.prob target := by
    calc
      _ = prior.expect (fun h =>
          likelihood (observe target) * (prior.condOnFibre observe (observe h)).prob target) := by
        apply FinDist.expect_congr
        intro h support
        by_cases same : observe h = observe target
        · rw [same]
        · have zero : (prior.condOnFibre observe (observe h)).prob target = 0 := by
            rw [FinDist.condOnFibre, dif_pos ⟨h, rfl, support⟩, FinDist.prob_condOn,
              if_neg (show target ∉ observe ⁻¹' {observe h} from fun equal => same equal.symm)]
          rw [zero, mul_zero, mul_zero]
      _ = _ := by rw [FinDist.expect_smul, fixed]
  rw [weighted]
  simp only [tiltWeights]
  ring

/-- Every continuation kernel is preserved after reconstructing from the joint statistic. -/
theorem tilt_reconstruct_continuation {Outcome : Type*}
    (prior : FinDist H) (observe : H → I) (likelihood : I → ℝ)
    (nonneg : ∀ i, 0 ≤ likelihood i)
    (positive : 0 < (tiltWeights prior observe likelihood nonneg).mass)
    (continuation : H → FinDist Outcome) :
    (((tiltWeights prior observe likelihood nonneg).normalize positive).map observe).bind
        (fun value => (prior.condOnFibre observe value).bind continuation) =
      ((tiltWeights prior observe likelihood nonneg).normalize positive).bind continuation := by
  rw [← FinDist.bind_bind, tilt_reconstruct]

/-- On the fixed-prior likelihood family, equal joint statistics imply equal history laws. -/
theorem tilt_joint_statistic_injective (prior : FinDist H) (observe : H → I)
    (first second : I → ℝ) (firstNonneg : ∀ i, 0 ≤ first i) (secondNonneg : ∀ i, 0 ≤ second i)
    (firstPos : 0 < (tiltWeights prior observe first firstNonneg).mass)
    (secondPos : 0 < (tiltWeights prior observe second secondNonneg).mass)
    (equal : ((tiltWeights prior observe first firstNonneg).normalize firstPos).map observe =
      ((tiltWeights prior observe second secondNonneg).normalize secondPos).map observe) :
    (tiltWeights prior observe first firstNonneg).normalize firstPos =
      (tiltWeights prior observe second secondNonneg).normalize secondPos := by
  rw [← tilt_reconstruct prior observe first firstNonneg firstPos,
    ← tilt_reconstruct prior observe second secondNonneg secondPos, equal]

/-- Apply the fixed-kernel theorem to the compatibility-aware product of private reach
factors. The observed statistic here is the JOINT tuple, never a tuple of marginal laws. -/
theorem joint_reconstruct {ι : Type uι} [Fintype ι] {Info : ι → Type ui}
    (chance : ReachWeights H) (observe : (i : ι) → H → Info i)
    (factors : (i : ι) → ReachWeights (Info i)) (chancePos : 0 < chance.mass)
    (jointPos : 0 < (joint chance observe factors).mass) :
    (((joint chance observe factors).normalize jointPos).map (fun h i => observe i h)).bind
        ((chance.normalize chancePos).condOnFibre (fun h i => observe i h)) =
      (joint chance observe factors).normalize jointPos := by
  let statistic : H → (i : ι) → Info i := fun h i => observe i h
  let likelihood : ((i : ι) → Info i) → ℝ := fun infos => ∏ i, (factors i).weight (infos i)
  have nonneg : ∀ infos, 0 ≤ likelihood infos :=
    fun infos => Finset.prod_nonneg fun i _ => (factors i).nonneg (infos i)
  have scaleEq : tiltWeights (chance.normalize chancePos) statistic likelihood nonneg =
      (joint chance observe factors).scale (1 / chance.mass) (one_div_pos.mpr chancePos).le := by
    apply ReachWeights.ext
    intro h
    simp only [tiltWeights, ReachWeights.prob_normalize, ReachWeights.scale,
      joint, statistic, likelihood]
    ring
  have positive : 0 <
      (tiltWeights (chance.normalize chancePos) statistic likelihood nonneg).mass := by
    rw [scaleEq, ReachWeights.mass_scale]
    exact mul_pos (one_div_pos.mpr chancePos) jointPos
  have normalizeEq :
      (tiltWeights (chance.normalize chancePos) statistic likelihood nonneg).normalize positive =
        (joint chance observe factors).normalize jointPos := by
    simpa only [scaleEq] using ReachWeights.normalize_scale (joint chance observe factors)
      (1 / chance.mass) (one_div_pos.mpr chancePos) jointPos
  have reconstruct := tilt_reconstruct (chance.normalize chancePos) statistic likelihood
    nonneg positive
  simpa only [normalizeEq, statistic] using reconstruct

end ReachEncoding

end GameTheory.ReBeL
