/-
# One continuous concave extension for every base belief

A base-anchored affine mass correction proves support at one belief. To avoid
changing the extension when the base changes, subtract a fixed absolute-mass
penalty instead. The resulting single continuous concave function agrees with
the value on the whole simplex and admits every active centered value vector.
-/

import GameTheory.Analysis.ReBeL.AffineEnvelope
import Mathlib.Analysis.Convex.Continuous

noncomputable section

namespace GameTheory.ReBeL.AffineEnvelope

open GameTheory.Math.Probability

universe ut uo
variable {T : Type ut} {O : Type uo} [Fintype T]
variable (slopes : O → T → ℝ)

/-- One globally defined extension, independent of any selected base belief
or equilibrium. The extra normal-direction crease is intentional. -/
def globalExtension (bound : ℝ) (point : T → ℝ) : ℝ :=
  value slopes point - bound * |1 - ∑ type, point type|

/-- The fixed absolute-mass penalty vanishes everywhere on the simplex. -/
theorem globalExtension_eq_on_simplex (bound : ℝ) :
    Set.EqOn (globalExtension slopes bound) (value slopes) (stdSimplex ℝ T) := by
  intro point hpoint
  simp [globalExtension, hpoint.2]

/-- A probability-weighted branch has the same uniform absolute bound as its
conditional slope coordinates, including at boundary probability vectors. -/
theorem branch_abs_le_simplex {bound : ℝ}
    (bounded : ∀ opponent type, |slopes opponent type| ≤ bound)
    {base : T → ℝ} (hbase : base ∈ stdSimplex ℝ T) (opponent : O) :
    |branch slopes base opponent| ≤ bound := by
  apply abs_le.mpr
  constructor
  · calc
      -bound = (∑ type, base type) * (-bound) := by rw [hbase.2, one_mul]
      _ = ∑ type, base type * (-bound) := Finset.sum_mul.symm
      _ ≤ branch slopes base opponent := by
        apply Finset.sum_le_sum
        intro type _
        exact mul_le_mul_of_nonneg_left
          ((neg_le_neg (bounded opponent type)).trans (neg_abs_le _)) (hbase.1 type)
  · calc
      branch slopes base opponent ≤ ∑ type, base type * bound := by
        apply Finset.sum_le_sum
        intro type _
        exact mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (bounded opponent type)) (hbase.1 type)
      _ = (∑ type, base type) * bound := Finset.sum_mul
      _ = bound := by rw [hbase.2, one_mul]

/-- Subtracting the convex absolute mass deviation preserves global concavity. -/
theorem globalExtension_concaveOn [Nonempty O] {bound : ℝ} (nonneg : 0 ≤ bound)
    (bounded : ∀ opponent type, |slopes opponent type| ≤ bound) :
    ConcaveOn ℝ Set.univ (globalExtension slopes bound) := by
  refine ⟨convex_univ, ?_⟩
  intro first hfirst second hsecond a b ha hb hab
  have inequality := (value_concaveOn slopes bounded).2 hfirst hsecond ha hb hab
  have mass : (1 - ∑ type, (a • first + b • second) type) =
      a * (1 - ∑ type, first type) + b * (1 - ∑ type, second type) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    nlinarith
  have absolute : |1 - ∑ type, (a • first + b • second) type| ≤
      a * |1 - ∑ type, first type| + b * |1 - ∑ type, second type| := by
    rw [mass]
    simpa only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using
      abs_add_le (a * (1 - ∑ type, first type)) (b * (1 - ∑ type, second type))
  have penalty := mul_le_mul_of_nonneg_left absolute nonneg
  simp only [globalExtension, smul_eq_mul]
  simp only [smul_eq_mul] at inequality
  nlinarith

/-- Finite-dimensional global concavity gives continuity of this real-valued
extension on the entire ambient space, not just relative continuity on a face. -/
theorem globalExtension_continuous [Nonempty O] {bound : ℝ} (nonneg : 0 ≤ bound)
    (bounded : ∀ opponent type, |slopes opponent type| ≤ bound) :
    Continuous (globalExtension slopes bound) := by
  have negative : ConvexOn ℝ Set.univ (-globalExtension slopes bound) :=
    (globalExtension_concaveOn slopes nonneg bounded).neg
  have continuousNegative : Continuous (-globalExtension slopes bound) :=
    continuousOn_univ.mp (negative.continuousOn isOpen_univ)
  simpa using continuousNegative.neg

/-- Every active centered value vector supports the same global extension.
Neither the extension nor its bound is chosen after the base or opponent. -/
theorem globalExtension_support {bound : ℝ}
    (bounded : ∀ opponent type, |slopes opponent type| ≤ bound)
    {base : T → ℝ} (hbase : base ∈ stdSimplex ℝ T)
    (point : T → ℝ) (opponent : O)
    (active : branch slopes base opponent = value slopes base) :
    globalExtension slopes bound point ≤ globalExtension slopes bound base +
      ∑ type, centeredVector slopes base opponent type * (point type - base type) := by
  have hvalue : |value slopes base| ≤ bound := by
    rw [← active]
    exact branch_abs_le_simplex slopes bounded hbase opponent
  have absolute : |(1 - ∑ type, point type) * value slopes base| ≤
      |1 - ∑ type, point type| * bound := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hvalue (abs_nonneg _)
  have lower := (neg_le_neg absolute).trans
    (neg_abs_le ((1 - ∑ type, point type) * value slopes base))
  have capped : globalExtension slopes bound point ≤ centeredExtension slopes base point := by
    unfold globalExtension centeredExtension
    nlinarith
  have supported := centeredExtension_support slopes bounded hbase.2 point opponent active
  have result := capped.trans supported
  simpa [centeredExtension, globalExtension, hbase.2] using result

/-- Restricting the global support to probability vectors proves the simplex
support inequality with the centered Eq. (2) vector. -/
theorem simplex_support {bound : ℝ}
    (bounded : ∀ opponent type, |slopes opponent type| ≤ bound)
    {base point : T → ℝ} (hbase : base ∈ stdSimplex ℝ T) (hpoint : point ∈ stdSimplex ℝ T)
    (opponent : O) (active : branch slopes base opponent = value slopes base) :
    value slopes point ≤ value slopes base +
      ∑ type, centeredVector slopes base opponent type * (point type - base type) := by
  have supported := globalExtension_support slopes bounded hbase point opponent active
  simpa [globalExtension, hbase.2, hpoint.2] using supported

/-- Footnote 8's valid form: convex averages of active vectors retain support
for this one fixed extension, even when optimal opponents are nonunique. -/
theorem averaged_globalExtension_support {bound : ℝ}
    (bounded : ∀ opponent type, |slopes opponent type| ≤ bound)
    {base : T → ℝ} (hbase : base ∈ stdSimplex ℝ T) (point : T → ℝ)
    (opponents : FinDist O)
    (active : ∀ opponent ∈ opponents.support,
      branch slopes base opponent = value slopes base) :
    globalExtension slopes bound point ≤ globalExtension slopes bound base +
      ∑ type, opponents.expect (fun opponent => centeredVector slopes base opponent type) *
        (point type - base type) := by
  calc
    _ = opponents.expect (fun _ => globalExtension slopes bound point) :=
      (FinDist.expect_const _ _).symm
    _ ≤ opponents.expect (fun opponent => globalExtension slopes bound base +
        ∑ type, centeredVector slopes base opponent type * (point type - base type)) :=
      FinDist.expect_mono fun opponent supported =>
        globalExtension_support slopes bounded hbase point opponent (active opponent supported)
    _ = _ := by
      rw [FinDist.expect_add, FinDist.expect_const, ← FinDist.expect_sum_comm]
      simp only [FinDist.expect_mul_const]

end GameTheory.ReBeL.AffineEnvelope
