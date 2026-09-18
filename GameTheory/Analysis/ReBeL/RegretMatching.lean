/-
# Regret matching with an explicit fallback

The positive-regret rule is the existing finite-law regret matcher. Only the
zero-positive-mass branch makes the fallback explicit, so a rational reference
implementation can refine it without a hidden Classical.choice operation.
-/

import GameTheory.Analysis.Approachability

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Math.Probability GameTheory.Analysis.Approachability
open GameTheory.Math.Approachability GameTheory.Math.OrthantProjection

variable {A Q : Type*} [Fintype A]

/-- Proportional positive regret, with a specified legal pure fallback if no
coordinate has positive regret. This is the real-valued specification. -/
def regretMatchWith (fallback : A) (x : EuclideanSpace ℝ A) : FinDist A :=
  if h : 0 < ∑ a, max (x.ofLp a) 0 then
    FinDist.ofWeights
      (fun a => max (x.ofLp a) 0 / ∑ b, max (x.ofLp b) 0)
      (fun a => div_nonneg (le_max_right _ _)
        (Finset.sum_nonneg fun b _ => le_max_right _ _))
      (by rw [← Finset.sum_div]; exact div_self h.ne')
  else FinDist.pure fallback

/-- Every nonpositive table uses exactly the specified fallback. -/
theorem regretMatchWith_of_nonpos (fallback : A) (x : EuclideanSpace ℝ A)
    (hx : ∀ a, x.ofLp a ≤ 0) : regretMatchWith fallback x = FinDist.pure fallback := by
  have hsum : (∑ a, max (x.ofLp a) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact max_eq_right (hx a)
  simp [regretMatchWith, hsum]

/-- The initial, zero-regret iteration is completely specified. -/
@[simp]
theorem regretMatchWith_zero (fallback : A) :
    regretMatchWith fallback 0 = FinDist.pure fallback := by
  apply regretMatchWith_of_nonpos
  simp

/-- Positive total regret agrees with the canonical matcher, independently
of whichever fallback its Nonempty instance would otherwise select. -/
theorem regretMatchWith_eq_regretMatch [Nonempty A] (fallback : A)
    (x : EuclideanSpace ℝ A) (hpos : 0 < ∑ a, max (x.ofLp a) 0) :
    regretMatchWith fallback x = regretMatch x := by
  simp only [regretMatchWith, regretMatch, dif_pos hpos]

/-- A legal fallback does not alter Blackwell's steering argument: with no
positive coordinate the displacement from the target orthant is zero. -/
theorem regretMatchWith_steering (fallback : A) (utility : A → Q → ℝ)
    (x : EuclideanSpace ℝ A) (environment : Q) :
    inner ℝ (regretPayoff utility (regretMatchWith fallback x) environment - orthantProj x)
      (x - orthantProj x) ≤ 0 := by
  let : Nonempty A := ⟨fallback⟩
  by_cases hpos : 0 < ∑ a, max (x.ofLp a) 0
  · rw [regretMatchWith_eq_regretMatch fallback x hpos]
    exact regretMatch_steering utility x environment
  · have hsum : (∑ a, max (x.ofLp a) 0) = 0 :=
      le_antisymm (le_of_not_gt hpos) (Finset.sum_nonneg fun a _ => le_max_right _ _)
    have hall : ∀ a, max (x.ofLp a) 0 = 0 := by
      intro a
      exact (Finset.sum_eq_zero_iff_of_nonneg fun b _ => le_max_right (x.ofLp b) 0).mp
        hsum a (Finset.mem_univ a)
    have hzero : x - orthantProj x = 0 := by
      ext a
      simpa only [sub_orthantProj_ofLp, WithLp.ofLp_zero, Pi.zero_apply] using hall a
    rw [hzero]
    simp

/-- The explicit-fallback matcher retains the canonical finite-time estimate
against every environment sequence. The payoff bound is uniform in all local
laws, not an assumption about the solution's realized regret. -/
theorem regretMatchWith_sq_infDist_avg_le (fallback : A) (utility : A → Q → ℝ)
    {bound : ℝ} (hbound0 : 0 ≤ bound)
    (hbound : ∀ law environment, ‖regretPayoff utility law environment‖ ≤ bound)
    (environments : ℕ → Q) (t : ℕ) :
    Metric.infDist
        (avgVec (regretPayoff utility) (regretMatchWith fallback) environments t)
        nonposOrthant ^ 2 * (t : ℝ) ≤ (2 * bound) ^ 2 := by
  have hraw := sq_infDist_avg_le (S := nonposOrthant) (C := 2 * bound)
    (avgVec_succ (regretPayoff utility) (regretMatchWith fallback) environments)
    (fun n => by
      refine ⟨orthantProj (avgVec (regretPayoff utility)
        (regretMatchWith fallback) environments n), orthantProj_mem _,
        (infDist_eq_norm_sub_orthantProj _).symm,
        regretMatchWith_steering fallback utility _ (environments n), ?_⟩
      set current := avgVec (regretPayoff utility) (regretMatchWith fallback) environments n
      have hcurrent : ‖current‖ ≤ bound :=
        avgVec_norm_le (regretPayoff utility) (regretMatchWith fallback)
          environments hbound0 hbound n
      calc
        ‖regretPayoff utility (regretMatchWith fallback current) (environments n) -
            orthantProj current‖ ≤
          ‖regretPayoff utility (regretMatchWith fallback current) (environments n)‖ +
            ‖orthantProj current‖ := norm_sub_le _ _
        _ ≤ bound + ‖current‖ := add_le_add (hbound _ _) (norm_orthantProj_le current)
        _ ≤ 2 * bound := by linarith) t
  by_cases ht : t = 0
  · subst t
    simp [sq_nonneg]
  · have hpositive : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht
    nlinarith [sq_nonneg (Metric.infDist
      (avgVec (regretPayoff utility) (regretMatchWith fallback) environments t) nonposOrthant)]

end GameTheory.ReBeL
