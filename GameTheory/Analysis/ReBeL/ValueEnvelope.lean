/-
# Lower-envelope geometry for ReBeL values

The opponent index may be infinite: replacing all mixed opponents by finitely
many pure opponents would give the wrong value. Boundedness is explicit.
The affine mass correction is distinct from degree-zero radial normalization.
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace GameTheory.ReBeL.ValueGeometry

open scoped BigOperators

variable {I J : Type*} [Fintype I]

/-- Coordinate pairing, with the belief in the second argument. -/
def pairing (v x : I → ℝ) : ℝ := ∑ i, x i * v i

/-- Infimum of opponent-indexed linear best-response branches. -/
def envelope (q : J → I → ℝ) (x : I → ℝ) : ℝ :=
  sInf (Set.range fun j => pairing (q j) x)

/-- The finite coordinate sum; no sign or normalization is implicit. -/
def mass (x : I → ℝ) : ℝ := ∑ i, x i

/-- Anchored affine correction of the homogeneous lower envelope. -/
def extension (q : J → I → ℝ) (c : ℝ) (x : I → ℝ) : ℝ :=
  envelope q x - (mass x - 1) * c

theorem pairing_add (v x y : I → ℝ) :
    pairing v (x + y) = pairing v x + pairing v y := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

theorem pairing_sub (v x y : I → ℝ) :
    pairing v (x - y) = pairing v x - pairing v y := by
  simp [pairing, sub_mul, Finset.sum_sub_distrib]

theorem pairing_smul (v x : I → ℝ) (a : ℝ) :
    pairing v (a • x) = a * pairing v x := by
  simp [pairing, Finset.mul_sum, mul_assoc]

theorem pairing_center (v x : I → ℝ) (c : ℝ) :
    pairing (fun i => v i - c) x = pairing v x - mass x * c := by
  simp [pairing, mass, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]

theorem mass_mix (x y : I → ℝ) (a b : ℝ) :
    mass (a • x + b • y) = a * mass x + b * mass y := by
  simp [mass, Finset.sum_add_distrib, Finset.mul_sum]

/-- A uniform payoff bound supplies the lower-bound obligation even away
from the simplex, including signed coordinates. -/
theorem bounded_below_of_abs_bound (q : J → I → ℝ) (B : ℝ)
    (hB : ∀ j i, |q j i| ≤ B) (x : I → ℝ) :
    BddBelow (Set.range fun j => pairing (q j) x) := by
  refine ⟨∑ i, -(|x i| * B), ?_⟩
  rintro _ ⟨j, rfl⟩
  apply Finset.sum_le_sum
  intro i _
  have h : |x i * q j i| ≤ |x i| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB j i) (abs_nonneg _)
  exact (abs_le.mp h).1

/-- Every branch is an upper bound on the lower envelope. -/
theorem envelope_le (q : J → I → ℝ)
    (hb : ∀ x, BddBelow (Set.range fun j => pairing (q j) x))
    (x : I → ℝ) (j : J) : envelope q x ≤ pairing (q j) x :=
  csInf_le (hb x) ⟨j, rfl⟩

/-- The corrected extension agrees with the value on the mass-one plane,
in particular on the entire simplex, including its boundary. -/
theorem extension_eq_of_mass_one (q : J → I → ℝ) (c : ℝ)
    (x : I → ℝ) (hx : mass x = 1) : extension q c x = envelope q x := by
  simp [extension, hx]

variable [Nonempty J]

/-- A simultaneous lower bound for all branches bounds their infimum. -/
theorem le_envelope (q : J → I → ℝ) (x : I → ℝ) (a : ℝ)
    (h : ∀ j, a ≤ pairing (q j) x) : a ≤ envelope q x := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  exact h j

/-- Minimax values expressed as lower envelopes are concave. Neither
attainment nor a unique equilibrium is required for this step. -/
theorem envelope_concave (q : J → I → ℝ)
    (hb : ∀ x, BddBelow (Set.range fun j => pairing (q j) x)) :
    ConcaveOn ℝ Set.univ (envelope q) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb' _
  apply le_envelope
  intro j
  simpa only [pairing_add, pairing_smul, smul_eq_mul] using
    add_le_add (mul_le_mul_of_nonneg_left (envelope_le q hb x j) ha)
      (mul_le_mul_of_nonneg_left (envelope_le q hb y j) hb')

/-- An affine correction preserves concavity; radial normalization need not. -/
theorem extension_concave (q : J → I → ℝ) (c : ℝ)
    (hb : ∀ x, BddBelow (Set.range fun j => pairing (q j) x)) :
    ConcaveOn ℝ Set.univ (extension q c) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb' hab
  have h := (envelope_concave q hb).2 (Set.mem_univ x) (Set.mem_univ y) ha hb' hab
  have hc := congrArg (fun t : ℝ => t * c) hab
  simp only [smul_eq_mul] at h ⊢
  simp only [extension, mass_mix]
  nlinarith only [h, hc]

omit [Nonempty J] in
/-- An active opponent branch gives the centered global supergradient of
our corrected extension. This is not a claim about the radial extension. -/
theorem centered_support (q : J → I → ℝ)
    (hb : ∀ x, BddBelow (Set.range fun j => pairing (q j) x))
    (base : I → ℝ) (hbase : mass base = 1) (j : J)
    (hactive : envelope q base = pairing (q j) base) (x : I → ℝ) :
    extension q (envelope q base) x ≤
      extension q (envelope q base) base +
        pairing (fun i => q j i - envelope q base) (x - base) := by
  have h := envelope_le q hb x j
  rw [pairing_sub, pairing_center, pairing_center]
  simp only [extension, hbase]
  nlinarith

omit [Nonempty J] in
/-- The unextended value has the same centered supporting inequality when
both beliefs have mass one. No positive-coordinate assumption is needed. -/
theorem simplex_support (q : J → I → ℝ)
    (hb : ∀ x, BddBelow (Set.range fun j => pairing (q j) x))
    (base x : I → ℝ) (hbase : mass base = 1) (hx : mass x = 1) (j : J)
    (hactive : envelope q base = pairing (q j) base) :
    envelope q x ≤ envelope q base +
      pairing (fun i => q j i - envelope q base) (x - base) := by
  simpa only [extension_eq_of_mass_one q _ _ hx,
    extension_eq_of_mass_one q _ _ hbase] using
    centered_support q hb base hbase j hactive x

end GameTheory.ReBeL.ValueGeometry
