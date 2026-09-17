/-
# Unnormalized reach weights

Reach weights are not probability laws. A positive total is required to
normalize them; a zero total represents an impossible event, not a posterior.
The real-valued specification uses the canonical `FinDist` after normalization.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Math.Probability
open scoped BigOperators

universe u

/-- Nonnegative, not necessarily normalized reach weights.
The finite enumeration is supplied to operations, not stored in this data. -/
structure ReachWeights (α : Type u) where
  /-- Unnormalized mass assigned to each carrier element. -/
  weight : α → ℝ
  /-- Reach factors cannot assign negative mass. -/
  nonneg : ∀ a, 0 ≤ weight a

namespace ReachWeights

variable {α : Type u} [Fintype α]

/-- The normalizing constant; unlike a probability law, it may be zero. -/
def mass (w : ReachWeights α) : ℝ := ∑ a, w.weight a

theorem mass_nonneg (w : ReachWeights α) : 0 ≤ w.mass :=
  Finset.sum_nonneg fun a _ => w.nonneg a

/-- Normalize only a positive-mass reach vector. -/
def normalize (w : ReachWeights α) (positive : 0 < w.mass) : FinDist α :=
  FinDist.ofWeights (fun a => w.weight a / w.mass)
    (fun a => div_nonneg (w.nonneg a) positive.le) (by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      exact mul_inv_cancel₀ positive.ne')

@[simp]
theorem prob_normalize (w : ReachWeights α) (positive : 0 < w.mass) (a : α) :
    (w.normalize positive).prob a = w.weight a / w.mass :=
  FinDist.prob_ofWeights ..

/-- Impossible events return `none`; no uniform or prior fallback is a posterior. -/
def normalize? (w : ReachWeights α) : Option (FinDist α) := by
  classical
  exact if positive : 0 < w.mass then some (w.normalize positive) else none

@[simp]
theorem normalize?_eq_none (w : ReachWeights α) : w.normalize? = none ↔ w.mass = 0 := by
  classical
  by_cases positive : 0 < w.mass
  · simp [normalize?, positive, ne_of_gt positive]
  · have hz : w.mass = 0 := le_antisymm (le_of_not_gt positive) w.mass_nonneg
    simp [normalize?, hz]

/-- A canonical probability law can be viewed as normalized reach weights. -/
def ofLaw (law : FinDist α) : ReachWeights α := ⟨law.prob, law.prob_nonneg⟩

@[simp]
theorem mass_ofLaw (law : FinDist α) : (ofLaw law).mass = 1 := law.sum_prob

@[simp]
theorem normalize_ofLaw (law : FinDist α) (positive : 0 < (ofLaw law).mass) :
    (ofLaw law).normalize positive = law := by
  apply FinDist.ext_of_prob
  intro a
  simp [ofLaw, prob_normalize, mass, FinDist.sum_prob]

/-- Multiplying all reaches by the same positive constant does not change belief. -/
def scale (w : ReachWeights α) (c : ℝ) (nonnegative : 0 ≤ c) : ReachWeights α :=
  ⟨fun a => c * w.weight a, fun a => mul_nonneg nonnegative (w.nonneg a)⟩

@[simp]
theorem mass_scale (w : ReachWeights α) (c : ℝ) (nonnegative : 0 ≤ c) :
    (w.scale c nonnegative).mass = c * w.mass := by
  simp only [mass, scale, Finset.mul_sum]

theorem normalize_scale (w : ReachWeights α) (c : ℝ) (hc : 0 < c)
    (positive : 0 < w.mass) :
    (w.scale c hc.le).normalize (by rw [mass_scale]; exact mul_pos hc positive) =
      w.normalize positive := by
  apply FinDist.ext_of_prob
  intro a
  simp only [prob_normalize, scale, mass, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc.ne'

/-- Restriction to a public event retains the original joint weights. -/
def restrict (w : ReachWeights α) (event : Set α) : ReachWeights α := by
  classical
  exact ⟨fun a => if a ∈ event then w.weight a else 0, fun a => by
    split_ifs
    · exact w.nonneg a
    · exact le_rfl⟩

theorem mass_restrict_ofLaw (law : FinDist α) (event : Set α) :
    ((ofLaw law).restrict event).mass = law.probOf event := by
  classical
  rw [← FinDist.expect_indicator_eq_probOf, FinDist.expect_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ event <;> simp [restrict, ofLaw, ha]

/-- Normalizing restricted probability weights is exactly canonical Bayes conditioning. -/
theorem normalize_restrict_ofLaw (law : FinDist α) (event : Set α)
    (possible : ∃ a ∈ event, a ∈ law.support) :
    ((ofLaw law).restrict event).normalize
      (by rw [mass_restrict_ofLaw]; exact FinDist.probOf_pos possible) =
      law.condOn event possible := by
  classical
  apply FinDist.ext_of_prob
  intro a
  rw [prob_normalize, mass_restrict_ofLaw, FinDist.prob_condOn]
  by_cases ha : a ∈ event <;> simp [restrict, ofLaw, ha]

end ReachWeights

end GameTheory.ReBeL
