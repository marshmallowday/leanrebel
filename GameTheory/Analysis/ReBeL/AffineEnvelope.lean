/-
# Concave envelopes of bounded affine branches

A uniformly bounded family of slope vectors has a finite lower envelope on
its entire real vector space. This elementary analytic construction does not
postulate minimax: the PBS application separately proves equality with the
canonical game value on the probability simplex.
-/

import GameTheory.Math.Probability.Simplex
import Mathlib.Analysis.Convex.Function

noncomputable section

namespace GameTheory.ReBeL.AffineEnvelope

open GameTheory.Math.Probability

universe ut uo
variable {T : Type ut} {O : Type uo} [Fintype T]
variable (slopes : O → T → ℝ)

/-- The linear payoff branch of a fixed opponent. -/
def branch (weight : T → ℝ) (opponent : O) : ℝ :=
  ∑ type, weight type * slopes opponent type

/-- The lower envelope is a real-valued function even away from mass-one
weights. Its boundedness and game interpretation are proved independently. -/
def value (weight : T → ℝ) : ℝ := sInf (Set.range (branch slopes weight))

/-- A uniform coordinate bound makes every set of affine branch values
bounded below, including at signed, unnormalized weight vectors. -/
theorem branch_bddBelow {bound : ℝ}
    (bounded : ∀ opponent type, |slopes opponent type| ≤ bound) (weight : T → ℝ) :
    BddBelow (Set.range (branch slopes weight)) := by
  refine ⟨-(∑ type, |weight type| * bound), ?_⟩
  rintro result ⟨opponent, rfl⟩
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro type _
  have bound' : |weight type * slopes opponent type| ≤ |weight type| * bound := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (bounded opponent type) (abs_nonneg _)
  exact (neg_le_neg bound').trans (neg_abs_le _)

/-- Every actual opponent gives a global upper affine bound on the envelope. -/
theorem value_le_branch {bound : ℝ}
    (bounded : ∀ opponent type, |slopes opponent type| ≤ bound)
    (weight : T → ℝ) (opponent : O) :
    value slopes weight ≤ branch slopes weight opponent :=
  csInf_le (branch_bddBelow slopes bounded weight) ⟨opponent, rfl⟩

/-- Any lower bound for all branches is a lower bound for their envelope. -/
theorem le_value [Nonempty O] (weight : T → ℝ) (lower : ℝ)
    (bounded : ∀ opponent, lower ≤ branch slopes weight opponent) :
    lower ≤ value slopes weight := by
  apply le_csInf (Set.range_nonempty _)
  rintro result ⟨opponent, rfl⟩
  exact bounded opponent

/-- An independently proved attained minimum identifies the envelope exactly. -/
theorem value_eq_of_isLeast (weight : T → ℝ) (minimum : ℝ)
    (attained : IsLeast (Set.range (branch slopes weight)) minimum) :
    value slopes weight = minimum := by
  apply le_antisymm
  · exact csInf_le ⟨minimum, attained.2⟩ attained.1
  · exact le_csInf ⟨minimum, attained.1⟩ attained.2

/-- Each opponent branch is linear on the whole weight space. -/
theorem branch_linear (first second : T → ℝ) (a b : ℝ) (opponent : O) :
    branch slopes (a • first + b • second) opponent =
      a * branch slopes first opponent + b * branch slopes second opponent := by
  unfold branch
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]

/-- The lower envelope of this bounded affine family is globally concave.
The proof does not require a differentiable value or a unique minimizing branch. -/
theorem value_concaveOn [Nonempty O] {bound : ℝ}
    (bounded : ∀ opponent type, |slopes opponent type| ≤ bound) :
    ConcaveOn ℝ Set.univ (value slopes) := by
  refine ⟨convex_univ, ?_⟩
  intro first _ second _ a b ha hb _
  apply le_value
  intro opponent
  have hfirst := value_le_branch slopes bounded first opponent
  have hsecond := value_le_branch slopes bounded second opponent
  have result := add_le_add (mul_le_mul_of_nonneg_left hfirst ha)
    (mul_le_mul_of_nonneg_left hsecond hb)
  rw [← branch_linear] at result
  simpa only [smul_eq_mul] using result

/-- The centered Eq. (2) vector at a chosen base weight. -/
def centeredVector (base : T → ℝ) (opponent : O) (type : T) : ℝ :=
  slopes opponent type - value slopes base

/-- Centering changes only the component normal to the probability simplex. -/
theorem centered_dot_eq (base point : T → ℝ) (opponent : O) :
    (∑ type, centeredVector slopes base opponent type * (point type - base type)) =
      branch slopes point opponent - branch slopes base opponent -
        ((∑ type, point type) - ∑ type, base type) * value slopes base := by
  calc
    _ = ∑ type, ((point type * slopes opponent type - base type * slopes opponent type) -
        (point type - base type) * value slopes base) := by
      apply Finset.sum_congr rfl
      intro type _
      unfold centeredVector
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        Finset.sum_sub_distrib]
      rfl

/-- A concave ambient extension with the desired normal component at the base.
It is deliberately not the radial-normalization construction in Appendix F. -/
def centeredExtension (base point : T → ℝ) : ℝ :=
  value slopes point + (1 - ∑ type, point type) * value slopes base

/-- The extension agrees with the envelope at every probability vector. -/
theorem centeredExtension_eq_on_simplex (base : T → ℝ) :
    Set.EqOn (centeredExtension slopes base) (value slopes) (stdSimplex ℝ T) := by
  intro point hpoint
  simp only [centeredExtension, hpoint.2, sub_self, zero_mul, add_zero]

/-- Affine mass correction preserves global concavity. -/
theorem centeredExtension_concaveOn [Nonempty O] {bound : ℝ}
    (bounded : ∀ opponent type, |slopes opponent type| ≤ bound) (base : T → ℝ) :
    ConcaveOn ℝ Set.univ (centeredExtension slopes base) := by
  refine ⟨convex_univ, ?_⟩
  intro first hfirst second hsecond a b ha hb hab
  have inequality := (value_concaveOn slopes bounded).2 hfirst hsecond ha hb hab
  have mass : (∑ type, (a • first + b • second) type) =
      a * (∑ type, first type) + b * ∑ type, second type := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
  have affine : a * ((1 - ∑ type, first type) * value slopes base) +
      b * ((1 - ∑ type, second type) * value slopes base) =
        (1 - ∑ type, (a • first + b • second) type) * value slopes base := by
    rw [mass]
    calc
      _ = ((a + b) - (a * (∑ type, first type) + b * ∑ type, second type)) *
          value slopes base := by ring
      _ = _ := by rw [hab]
  calc
    a • centeredExtension slopes base first + b • centeredExtension slopes base second =
        (a * value slopes first + b * value slopes second) +
          (1 - ∑ type, (a • first + b • second) type) * value slopes base := by
      rw [← affine]
      simp only [centeredExtension, smul_eq_mul]
      ring
    _ ≤ centeredExtension slopes base (a • first + b • second) := by
      simpa only [centeredExtension, smul_eq_mul, add_comm] using
        add_le_add_right inequality
          ((1 - ∑ type, (a • first + b • second) type) * value slopes base)

/-- Every active branch yields a globally supporting centered vector for the
corrected extension, including at boundary or nondifferentiable base points. -/
theorem centeredExtension_support {bound : ℝ}
    (bounded : ∀ opponent type, |slopes opponent type| ≤ bound)
    {base : T → ℝ} (mass : ∑ type, base type = 1)
    (point : T → ℝ) (opponent : O)
    (active : branch slopes base opponent = value slopes base) :
    centeredExtension slopes base point ≤ centeredExtension slopes base base +
      ∑ type, centeredVector slopes base opponent type * (point type - base type) := by
  have inequality := value_le_branch slopes bounded point opponent
  rw [centered_dot_eq, active, mass]
  simp only [centeredExtension, mass, sub_self, zero_mul, add_zero]
  nlinarith

/-- The centered coordinate relation is the source's Eq. (2). Its significance
comes from the independent global support theorem, not this algebra alone. -/
theorem slope_eq_value_add_centered (base : T → ℝ) (opponent : O) (type : T) :
    slopes opponent type = value slopes base + centeredVector slopes base opponent type := by
  unfold centeredVector
  ring

/-- Finite convex combinations of active value vectors preserve global support.
The finite distribution supplies nonnegative weights with total mass one. -/
theorem averaged_centeredExtension_support {bound : ℝ}
    (bounded : ∀ opponent type, |slopes opponent type| ≤ bound)
    {base : T → ℝ} (mass : ∑ type, base type = 1) (point : T → ℝ)
    (opponents : FinDist O)
    (active : ∀ opponent ∈ opponents.support,
      branch slopes base opponent = value slopes base) :
    centeredExtension slopes base point ≤ centeredExtension slopes base base +
      ∑ type, opponents.expect (fun opponent => centeredVector slopes base opponent type) *
        (point type - base type) := by
  calc
    _ = opponents.expect (fun _ => centeredExtension slopes base point) :=
      (FinDist.expect_const _ _).symm
    _ ≤ opponents.expect (fun opponent => centeredExtension slopes base base +
        ∑ type, centeredVector slopes base opponent type * (point type - base type)) :=
      FinDist.expect_mono fun opponent supported =>
        centeredExtension_support slopes bounded mass point opponent (active opponent supported)
    _ = _ := by
      rw [FinDist.expect_add, FinDist.expect_const, ← FinDist.expect_sum_comm]
      simp only [FinDist.expect_mul_const]

end GameTheory.ReBeL.AffineEnvelope
