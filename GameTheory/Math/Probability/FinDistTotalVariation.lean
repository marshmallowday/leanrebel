/-
# Total variation of finite-support laws

The probability-only coefficient uses the union of the two finite supports;
no finite carrier or representation escape hatch is needed. It bounds every
bounded observable, contracts under a common future kernel, and controls the
probability of leaving another law's support. This is not a payoff certificate.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Math.Probability.FinDist

universe u v
variable {A : Type u} {B : Type v}

/-- Half the finite L1 difference of the real probability masses. -/
def totalVariation (first second : FinDist A) : ℝ := by
  classical
  exact (∑ x ∈ first.supportFinset ∪ second.supportFinset,
    |first.prob x - second.prob x|) / 2

/-- Any common finite support superset computes the same coefficient. -/
theorem totalVariation_eq_sum_of_subset (first second : FinDist A) (points : Finset A)
    (firstSupport : first.support ⊆ ↑points) (secondSupport : second.support ⊆ ↑points) :
    totalVariation first second =
      (∑ x ∈ points, |first.prob x - second.prob x|) / 2 := by
  classical
  unfold totalVariation
  congr 1
  apply Finset.sum_subset
  · intro x member
    rcases Finset.mem_union.mp member with member | member
    · exact firstSupport (mem_supportFinset.mp member)
    · exact secondSupport (mem_supportFinset.mp member)
  · intro x _ missing
    have notFirst : x ∉ first.support := fun reached =>
      missing (Finset.mem_union_left _ (mem_supportFinset.mpr reached))
    have notSecond : x ∉ second.support := fun reached =>
      missing (Finset.mem_union_right _ (mem_supportFinset.mpr reached))
    rw [prob_eq_zero_iff.mpr notFirst, prob_eq_zero_iff.mpr notSecond, sub_self, abs_zero]

/-- Finite enumerations are an optional way of evaluating total variation. -/
theorem totalVariation_eq_sum [Fintype A] (first second : FinDist A) :
    totalVariation first second = (∑ x, |first.prob x - second.prob x|) / 2 := by
  classical
  exact totalVariation_eq_sum_of_subset first second Finset.univ
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)

/-- The coefficient is nonnegative. -/
theorem totalVariation_nonneg (first second : FinDist A) :
    0 ≤ totalVariation first second := by
  classical
  unfold totalVariation
  exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

/-- Identical distributions have zero variation, even on infinite carriers. -/
theorem totalVariation_self (law : FinDist A) : totalVariation law law = 0 := by
  classical
  simp only [totalVariation, sub_self, abs_zero, Finset.sum_const_zero, zero_div]

/-- Swapping the two laws leaves the coefficient unchanged. -/
theorem totalVariation_comm (first second : FinDist A) :
    totalVariation first second = totalVariation second first := by
  classical
  unfold totalVariation
  rw [Finset.union_comm]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => abs_sub_comm _ _

/-- The normalization makes total variation at most one. -/
theorem totalVariation_le_one (first second : FinDist A) :
    totalVariation first second ≤ 1 := by
  classical
  let points := first.supportFinset ∪ second.supportFinset
  have firstSupport : first.support ⊆ ↑points := fun _ reached =>
    Finset.mem_union_left _ (mem_supportFinset.mpr reached)
  have secondSupport : second.support ⊆ ↑points := fun _ reached =>
    Finset.mem_union_right _ (mem_supportFinset.mpr reached)
  have firstMass : (∑ x ∈ points, first.prob x) = 1 := by
    simpa only [expect_const, mul_one] using
      (expect_eq_sum_of_subset first (fun _ => 1) points firstSupport).symm
  have secondMass : (∑ x ∈ points, second.prob x) = 1 := by
    simpa only [expect_const, mul_one] using
      (expect_eq_sum_of_subset second (fun _ => 1) points secondSupport).symm
  have bounded : (∑ x ∈ points, |first.prob x - second.prob x|) ≤ 2 := by
    calc
      _ ≤ ∑ x ∈ points, (first.prob x + second.prob x) := by
        apply Finset.sum_le_sum
        intro x _
        calc
          _ ≤ |first.prob x| + |second.prob x| := abs_sub _ _
          _ = _ := by rw [abs_of_nonneg (prob_nonneg first x),
            abs_of_nonneg (prob_nonneg second x)]
      _ = 2 := by rw [Finset.sum_add_distrib, firstMass, secondMass]; norm_num
  rw [totalVariation_eq_sum_of_subset first second points firstSupport secondSupport]
  linarith

/-- Probability-only variation controls every uniformly bounded observation. -/
theorem abs_expect_sub_le_totalVariation (first second : FinDist A)
    (value : A → ℝ) (bound : ℝ) (bounded : ∀ x, |value x| ≤ bound) :
    |first.expect value - second.expect value| ≤
      2 * bound * totalVariation first second := by
  classical
  let points := first.supportFinset ∪ second.supportFinset
  have firstSupport : first.support ⊆ ↑points := fun _ reached =>
    Finset.mem_union_left _ (mem_supportFinset.mpr reached)
  have secondSupport : second.support ⊆ ↑points := fun _ reached =>
    Finset.mem_union_right _ (mem_supportFinset.mpr reached)
  have difference : first.expect value - second.expect value =
      ∑ x ∈ points, (first.prob x - second.prob x) * value x := by
    rw [expect_eq_sum_of_subset first value points firstSupport,
      expect_eq_sum_of_subset second value points secondSupport, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [difference]
  calc
    _ ≤ ∑ x ∈ points, |(first.prob x - second.prob x) * value x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ points, |first.prob x - second.prob x| * bound := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (bounded x) (abs_nonneg _)
    _ = 2 * bound * totalVariation first second := by
      rw [← Finset.sum_mul]
      unfold totalVariation
      dsimp only [points]
      ring

/-- A bounded, probability-derived test attaining twice total variation. -/
def variationTest (first second : FinDist A) (x : A) : ℝ := by
  classical
  exact if second.prob x ≤ first.prob x then 1 else -1

/-- The extremal test is uniformly bounded by one. -/
theorem variationTest_abs_le (first second : FinDist A) (x : A) :
    |variationTest first second x| ≤ 1 := by
  classical
  unfold variationTest
  split_ifs <;> norm_num

/-- The extremal test is constructed from masses, not supplied as an optimizer. -/
theorem expect_variationTest_sub (first second : FinDist A) :
    first.expect (variationTest first second) - second.expect (variationTest first second) =
      2 * totalVariation first second := by
  classical
  let points := first.supportFinset ∪ second.supportFinset
  have firstSupport : first.support ⊆ ↑points := fun _ reached =>
    Finset.mem_union_left _ (mem_supportFinset.mpr reached)
  have secondSupport : second.support ⊆ ↑points := fun _ reached =>
    Finset.mem_union_right _ (mem_supportFinset.mpr reached)
  rw [expect_eq_sum_of_subset first _ points firstSupport,
    expect_eq_sum_of_subset second _ points secondSupport, ← Finset.sum_sub_distrib]
  have terms : (∑ x ∈ points,
      (first.prob x * variationTest first second x -
        second.prob x * variationTest first second x)) =
      ∑ x ∈ points, |first.prob x - second.prob x| := by
    apply Finset.sum_congr rfl
    intro x _
    unfold variationTest
    split_ifs with ordered
    · rw [mul_one, mul_one, abs_of_nonneg (sub_nonneg.mpr ordered)]
    · rw [abs_of_nonpos (by linarith : first.prob x - second.prob x ≤ 0)]
      ring
  rw [terms]
  unfold totalVariation
  dsimp only [points]
  ring

/-- Averaging different kernels cannot increase their mean variation. -/
theorem totalVariation_bind_le_expect (law : FinDist A) (first second : A → FinDist B) :
    totalVariation (law.bind first) (law.bind second) ≤
      law.expect (fun x => totalVariation (first x) (second x)) := by
  let value := variationTest (law.bind first) (law.bind second)
  have localBound (x : A) :
      (first x).expect value - (second x).expect value ≤
        2 * totalVariation (first x) (second x) := by
    have estimate := abs_expect_sub_le_totalVariation (first x) (second x) value 1
      (variationTest_abs_le _ _)
    exact (le_abs_self _).trans (by simpa only [mul_one] using estimate)
  have estimate := expect_mono (μ := law) (fun x _ => localBound x)
  rw [expect_sub, expect_smul, ← expect_bind, ← expect_bind] at estimate
  have identity := expect_variationTest_sub (law.bind first) (law.bind second)
  dsimp only [value] at estimate
  rw [identity] at estimate
  linarith

/-- A shared arbitrary future kernel contracts total variation. -/
theorem totalVariation_bind_le (first second : FinDist A) (kernel : A → FinDist B) :
    totalVariation (first.bind kernel) (second.bind kernel) ≤ totalVariation first second := by
  let value := variationTest (first.bind kernel) (second.bind kernel)
  have bounded (x : A) : |(kernel x).expect value| ≤ 1 :=
    abs_expect_le_of_abs_bound _ _ (fun y _ => variationTest_abs_le _ _ y)
  have estimate := abs_expect_sub_le_totalVariation first second
    (fun x => (kernel x).expect value) 1 bounded
  rw [← expect_bind, ← expect_bind] at estimate
  dsimp only [value] at estimate
  rw [expect_variationTest_sub] at estimate
  have positive := totalVariation_nonneg (first.bind kernel) (second.bind kernel)
  rw [abs_of_nonneg (by positivity)] at estimate
  linarith

/-- An event's probability difference has the sharp coefficient one. -/
theorem abs_probOf_sub_le_totalVariation (first second : FinDist A) (event : Set A) :
    |first.probOf event - second.probOf event| ≤ totalVariation first second := by
  classical
  let value := fun x : A => (if x ∈ event then (1 : ℝ) else 0) - 1 / 2
  have bounded (x : A) : |value x| ≤ (1 / 2 : ℝ) := by
    dsimp only [value]
    split_ifs <;> norm_num
  calc
    _ = |first.expect value - second.expect value| := by
      simp only [value, expect_sub, expect_const, expect_indicator_eq_probOf]
      congr 1
      ring
    _ ≤ 2 * (1 / 2 : ℝ) * totalVariation first second :=
      abs_expect_sub_le_totalVariation first second value (1 / 2) bounded
    _ = totalVariation first second := by ring

/-- In particular unsupported actual outcomes cost at most the model-law variation. -/
theorem probOf_outside_support_le_totalVariation (actual model : FinDist A) :
    actual.probOf {x | x ∉ model.support} ≤ totalVariation actual model := by
  classical
  have modelZero : model.probOf {x | x ∉ model.support} = 0 := by
    rw [← expect_indicator_eq_probOf]
    calc
      _ = model.expect (fun _ => 0) := by
        apply expect_congr
        intro x reached
        exact if_neg (by simpa only [Set.mem_setOf_eq, not_not] using reached)
      _ = 0 := expect_const _ _
  have estimate := abs_probOf_sub_le_totalVariation actual model {x | x ∉ model.support}
  rw [modelZero, sub_zero] at estimate
  exact (le_abs_self _).trans estimate

end GameTheory.Math.Probability.FinDist
