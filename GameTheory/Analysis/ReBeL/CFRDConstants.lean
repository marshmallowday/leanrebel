/-
# Explicit finite-time depth-limited constants

All constants are finite sums over the canonical legal decision schedule.
They depend on depth, legal action counts and payoff size, not on iteration
count, learned reach probabilities, prediction error or the unknown opponent.
The continuation loss stays separate from numerical value-prediction error.
-/

import GameTheory.Analysis.ReBeL.CFRDRootRegret

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel

private theorem cfrD_mean_algebra (c d bound error : ℝ)
    (hc : 0 ≤ c) (he : 0 ≤ error) (t : Nat) [NeZero t] :
    (c * (bound + error) * Real.sqrt t + (t : ℝ) * (d * error)) / t ≤
      (c + d) * error + (c * bound) / Real.sqrt t := by
  have ht : 0 < (t : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne t))
  have hs : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr ht
  have tone : (1 : ℝ) ≤ t := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne t)
  have sone : 1 ≤ Real.sqrt (t : ℝ) := by
    simpa using Real.sqrt_le_sqrt tone
  have inverse : Real.sqrt (t : ℝ) / t = 1 / Real.sqrt (t : ℝ) := by
    apply (div_eq_div_iff (ne_of_gt ht) (ne_of_gt hs)).mpr
    nlinarith [Real.sq_sqrt ht.le]
  have shrink : c * error / Real.sqrt t ≤ c * error := by
    apply (div_le_iff₀ hs).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left sone (mul_nonneg hc he)
  calc
    _ = c * (bound + error) * (Real.sqrt t / t) + d * error := by
      field_simp
      <;> ring
    _ = c * (bound + error) / Real.sqrt t + d * error := by rw [inverse]; ring
    _ = c * bound / Real.sqrt t + c * error / Real.sqrt t + d * error := by ring
    _ ≤ c * bound / Real.sqrt t + c * error + d * error := by linarith
    _ = _ := by ring

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [∀ who info, Fintype (M.Choice who info)]

/-- The finite-iteration coefficient at a searched legal information state. -/
def cfrDSiteFiniteCoefficient (fallback : (who : ι) → M.Policy who)
    (who : ι) (site : M.InformationSite who) : ℝ :=
  4 * Real.sqrt (Fintype.card (M.Choice who site.1)) / cfrDStructuralReach M fallback who site

/-- Uniform structural reach, rather than current learned reach, fixes this coefficient. -/
theorem cfrDSiteFiniteCoefficient_nonneg (fallback : (who : ι) → M.Policy who)
    (who : ι) (site : M.InformationSite who) :
    0 ≤ cfrDSiteFiniteCoefficient M fallback who site := by
  unfold cfrDSiteFiniteCoefficient
  exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (cfrDStructuralReach_pos M fallback who site).le

/-- Both value perturbation terms are absorbed into an error-independent coefficient. -/
def cfrDSiteErrorCoefficient (fallback : (who : ι) → M.Policy who)
    (who : ι) (site : M.InformationSite who) : ℝ :=
  cfrDSiteFiniteCoefficient M fallback who site + 2 / cfrDStructuralReach M fallback who site

/-- Zero value error does not erase the finite-time regret term. -/
theorem cfrDTrunkSiteBudget_mean_le (fallback : (who : ι) → M.Policy who)
    (bound error : ℝ) (he : 0 ≤ error) (who : ι) (site : M.InformationSite who)
    (t : Nat) [NeZero t] :
    cfrDTrunkSiteBudget M fallback bound error who site t / t ≤
      cfrDSiteErrorCoefficient M fallback who site * error +
        (cfrDSiteFiniteCoefficient M fallback who site * bound) / Real.sqrt t := by
  have h := cfrD_mean_algebra (cfrDSiteFiniteCoefficient M fallback who site)
    (2 / cfrDStructuralReach M fallback who site) bound error
    (cfrDSiteFiniteCoefficient_nonneg M fallback who site) he t
  convert h using 1 <;>
    unfold cfrDTrunkSiteBudget cfrDSiteErrorCoefficient cfrDSiteFiniteCoefficient <;> ring

variable [Fintype ι] [DecidableEq ι] [Fintype E.History]
variable [∀ who, DecidableEq (M.InfoState who)]

/-- Explicit game/depth constant multiplying prediction error. -/
def cfrDDepthErrorConstant (clock : ObservationClock M)
    (fallback : (who : ι) → M.Policy who) (cut remaining : Nat) (who : ι) : ℝ :=
  ((scheduledSites M clock (cut + remaining) who).map fun site =>
    if clock.depth who site.1 < cut then cfrDSiteErrorCoefficient M fallback who site else 0).sum

/-- Explicit game/depth/payoff constant multiplying inverse square-root iterations. -/
def cfrDDepthFiniteConstant (clock : ObservationClock M)
    (fallback : (who : ι) → M.Policy who) (cut remaining : Nat) (bound : ℝ) (who : ι) : ℝ :=
  ((scheduledSites M clock (cut + remaining) who).map fun site =>
    if clock.depth who site.1 < cut then
      cfrDSiteFiniteCoefficient M fallback who site * bound else 0).sum

/-- The corrected shape has an additive finite-T term, not delta times every
term. The independent local continuation loss is displayed explicitly. -/
theorem cfrDDepthMeanBudget_le_constants (clock : ObservationClock M)
    (fallback : (who : ι) → M.Policy who) (cut remaining : Nat)
    (bound error loss : ℝ) (he : 0 ≤ error) (who : ι) (t : Nat) [NeZero t] :
    cfrDDepthMeanBudget M clock fallback cut remaining bound error loss who t ≤
      cfrDDepthErrorConstant M clock fallback cut remaining who * error +
        cfrDDepthFiniteConstant M clock fallback cut remaining bound who / Real.sqrt t + loss := by
  unfold cfrDDepthMeanBudget cfrDTrunkBudget cfrDDepthErrorConstant cfrDDepthFiniteConstant
  apply add_le_add_right
  generalize scheduledSites M clock (cut + remaining) who = sites
  induction sites with
  | nil => simp
  | cons site sites ih =>
      simp only [List.map_cons, List.sum_cons, add_div, add_mul]
      by_cases inside : clock.depth who site.1 < cut
      · simp only [if_pos inside]
        have hs := cfrDTrunkSiteBudget_mean_le M fallback bound error he who site t
        linarith
      · simp only [if_neg inside, zero_div, zero_mul, zero_add]
        exact ih

/-- The actual solver's every-deviation guarantee with explicit constants,
independent of any convergence or training claim about the oracle. -/
theorem cfrDDepth_mean_regret_le_constants (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : ι) → M.Policy who)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) (oracle : CFRDValueOracle M)
    (bound error loss : ℝ) (hbound : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 ≤ loss)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error)
    (optimal : CFRDDepthLeafOptimal M clock fallback payoff cut remaining oracle loss)
    (who : ι) (target : M.BehavioralPolicy who) (t : Nat) [NeZero t] :
    (cfrIterationLaw t).expect (fun n =>
      (M.runBehavioral (Profile.update
        (cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val) who target)
        (cut + remaining)).expect (payoff who) -
      (M.runBehavioral (cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val)
        (cut + remaining)).expect (payoff who)) ≤
      cfrDDepthErrorConstant M clock fallback cut remaining who * error +
        cfrDDepthFiniteConstant M clock fallback cut remaining bound who / Real.sqrt t + loss :=
  (cfrDDepth_mean_regret_le M clock hrecall fallback payoff cut remaining oracle
    bound error loss hbound he hl bounded accurate optimal who target t).trans
      (cfrDDepthMeanBudget_le_constants M clock fallback cut remaining bound error loss he who t)

end GameTheory.ReBeL
