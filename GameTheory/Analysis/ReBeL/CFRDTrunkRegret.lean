/-
# Finite-time regret of the constructed depth-limited trunk

Every numerical update is the real coupled value-oracle update. Exact
counterfactual regret is compared after removing action-independent offsets.
Only searched sites contribute: no off-trunk learner or local optimality
certificate is assumed. Continuation deviations are handled separately.
-/

import GameTheory.Analysis.ReBeL.CFRDPrefix

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

private theorem trunk_range_sum_expect {A : Type*} (law : FinDist A)
    (f : Nat → A → ℝ) (t : Nat) :
    (∑ n ∈ Finset.range t, law.expect (f n)) =
      law.expect (fun a => ∑ n ∈ Finset.range t, f n a) := by
  induction t with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ, ih, FinDist.expect_add]

private theorem trunk_range_sum_list {A : Type*} (sites : List A)
    (f : Nat → A → ℝ) (t : Nat) :
    (∑ n ∈ Finset.range t, (sites.map (f n)).sum) =
      (sites.map (fun site => ∑ n ∈ Finset.range t, f n site)).sum := by
  induction sites with
  | nil => simp
  | cons site sites ih => simp [Finset.sum_add_distrib, ih]

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [∀ who info, Fintype (M.Choice who info)]

/-- A positive game-dependent denominator, never the current strategy's reach. -/
def cfrDStructuralReach (fallback : (who : ι) → M.Policy who)
    (who : ι) (site : M.InformationSite who) : ℝ :=
  M.playerReachProbability (uniformLegalProfile M fallback) who site.2.choose.1.trace

/-- Positivity holds on all legally realized decision sites, even off policy. -/
theorem cfrDStructuralReach_pos (fallback : (who : ι) → M.Policy who)
    (who : ι) (site : M.InformationSite who) : 0 < cfrDStructuralReach M fallback who site :=
  uniformOwnReach_positive M fallback who _

/-- An explicit searched-site allowance: finite-time matching plus propagated
live information-value error. At zero oracle error the square-root term stays. -/
def cfrDTrunkSiteBudget (fallback : (who : ι) → M.Policy who)
    (bound error : ℝ) (who : ι) (site : M.InformationSite who) (t : Nat) : ℝ :=
  2 * (Real.sqrt (Fintype.card (M.Choice who site.1)) *
      (2 * ((bound + error) / cfrDStructuralReach M fallback who site))) * Real.sqrt t +
    (t : ℝ) * (2 * (error / cfrDStructuralReach M fallback who site))

/-- All allowances are nonnegative under numerical payoff and oracle bounds. -/
theorem cfrDTrunkSiteBudget_nonneg (fallback : (who : ι) → M.Policy who)
    {bound error : ℝ} (hbound : 0 ≤ bound) (herror : 0 ≤ error)
    (who : ι) (site : M.InformationSite who) (t : Nat) :
    0 ≤ cfrDTrunkSiteBudget M fallback bound error who site t := by
  have reach := cfrDStructuralReach_pos M fallback who site
  unfold cfrDTrunkSiteBudget
  positivity

variable [Fintype ι] [DecidableEq ι] [Fintype E.History]
variable [∀ who, DecidableEq (M.InfoState who)]

/-- A searched site's cumulative actual regret comes from the computed value
responses, with both the numerical size and approximation premises discharged. -/
theorem cfrDDepth_site_cumulative_le (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : ι) → M.Policy who)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) (oracle : CFRDValueOracle M)
    (bound error : ℝ) (hbound : 0 ≤ bound) (herror : 0 ≤ error)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error)
    (who : ι) (site : M.InformationSite who) (searched : clock.depth who site.1 < cut)
    (law : FinDist (M.Choice who site.1)) (t : Nat) :
    (∑ n ∈ Finset.range t, law.expect
      (M.counterfactualActionRegret (cfrDDepthPlay M clock fallback payoff cut remaining oracle n)
        who site (payoff who) (cut + remaining - clock.depth who site.1))) ≤
      cfrDTrunkSiteBudget M fallback bound error who site t := by
  let trunk := cfrDDepthTrunk M clock cut
  let driver := cfrDDepthOracle M clock fallback payoff cut remaining oracle
  let delta := error / cfrDStructuralReach M fallback who site
  let size := (bound + error) / cfrDStructuralReach M fallback who site
  have positive := cfrDStructuralReach_pos M fallback who site
  have hsize : 0 ≤ size := div_nonneg (add_nonneg hbound herror) (le_of_lt positive)
  have inside : trunk who site.1 = true := by
    simpa only [trunk, cfrDDepthTrunk, decide_eq_true_eq] using searched
  have hstep (n : Nat) :
      law.expect (M.counterfactualActionRegret
          (cfrDDepthPlay M clock fallback payoff cut remaining oracle n)
          who site (payoff who) (cut + remaining - clock.depth who site.1)) ≤
        law.expect (cfrDPredictedRegret M trunk fallback driver n who site) + 2 * delta := by
    rw [← FinDist.expect_const law (2 * delta), ← FinDist.expect_add]
    apply FinDist.expect_mono
    intro choice _
    exact cfrDDepth_regret_le_prediction M clock hrecall fallback payoff cut remaining oracle
      error herror accurate n who site searched choice
  have htable :
      (∑ n ∈ Finset.range t, law.expect
        (cfrDPredictedRegret M trunk fallback driver n who site)) =
        (t : ℝ) * law.expect (cfrDState M trunk fallback driver t who site).ofLp := by
    rw [trunk_range_sum_expect, ← FinDist.expect_smul]
    apply FinDist.expect_congr
    intro choice _
    exact (cfrDState_coordinate_sum M trunk fallback driver who site inside choice t).symm
  have hlocal := cfrD_local_cumulative_le M trunk fallback driver who site inside hsize
    (fun n choice => cfrDDepth_score_abs_le M clock hrecall fallback payoff cut remaining
      oracle bound error herror bounded accurate n who site searched choice) law t
  calc
    _ ≤ ∑ n ∈ Finset.range t,
        (law.expect (cfrDPredictedRegret M trunk fallback driver n who site) + 2 * delta) :=
      Finset.sum_le_sum fun n _ => hstep n
    _ = (t : ℝ) * law.expect (cfrDState M trunk fallback driver t who site).ofLp +
        (t : ℝ) * (2 * delta) := by
      rw [Finset.sum_add_distrib, htable]
      simp
    _ ≤ _ := add_le_add hlocal (le_refl _)

/-- Sum only the actual searched decision sites in the complete legal schedule. -/
def cfrDTrunkBudget (clock : ObservationClock M) (fallback : (who : ι) → M.Policy who)
    (cut remaining : Nat) (bound error : ℝ) (who : ι) (t : Nat) : ℝ :=
  ((scheduledSites M clock (cut + remaining) who).map fun site =>
    if clock.depth who site.1 < cut then
      cfrDTrunkSiteBudget M fallback bound error who site t else 0).sum

/-- The actual coupled depth-limited trace controls every fixed prefix
deviation. The decomposition, fixed own-reach factors and learner bounds are
proved, rather than packaged into an oracle or assumed as a root certificate. -/
theorem cfrDDepth_prefix_cumulative_le (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : ι) → M.Policy who)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) (oracle : CFRDValueOracle M)
    (bound error : ℝ) (hbound : 0 ≤ bound) (herror : 0 ≤ error)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error)
    (who : ι) (target : M.BehavioralPolicy who) (t : Nat) :
    (∑ n ∈ Finset.range t,
      ((M.runBehavioral (Profile.update
          (cfrDDepthPlay M clock fallback payoff cut remaining oracle n) who
          (cfrDPrefixPolicy M clock
            (cfrDDepthPlay M clock fallback payoff cut remaining oracle n) who target cut))
          (cut + remaining)).expect (payoff who) -
        (M.runBehavioral (cfrDDepthPlay M clock fallback payoff cut remaining oracle n)
          (cut + remaining)).expect (payoff who))) ≤
      cfrDTrunkBudget M clock fallback cut remaining bound error who t := by
  simp_rw [cfrDPrefix_root_gain M clock hrecall]
  rw [trunk_range_sum_list]
  have hterm (site : M.InformationSite who) :
      (∑ n ∈ Finset.range t,
        if clock.depth who site.1 < cut then
          targetRegretTerm M clock
            (cfrDDepthPlay M clock fallback payoff cut remaining oracle n)
            who target (payoff who) (cut + remaining) site else 0) ≤
        if clock.depth who site.1 < cut then
          cfrDTrunkSiteBudget M fallback bound error who site t else 0 := by
    by_cases searched : clock.depth who site.1 < cut
    · simp only [if_pos searched]
      unfold targetRegretTerm
      have hreach (n : Nat) := targetReach_independent_profile M
        (cfrDDepthPlay M clock fallback payoff cut remaining oracle n)
        (cfrDDepthPlay M clock fallback payoff cut remaining oracle 0)
        who target site.2.choose.1.trace
      simp_rw [hreach]
      rw [← Finset.mul_sum]
      have hlocal := cfrDDepth_site_cumulative_le M clock hrecall fallback payoff cut remaining
        oracle bound error hbound herror bounded accurate who site searched (target site.1) t
      have hr := playerReach_unitInterval M
        (Profile.update (cfrDDepthPlay M clock fallback payoff cut remaining oracle 0) who target)
        who site.2.choose.1.trace
      have hb := cfrDTrunkSiteBudget_nonneg M fallback hbound herror who site t
      exact le_trans (mul_le_mul_of_nonneg_left hlocal hr.1)
        (by simpa using mul_le_mul_of_nonneg_right hr.2 hb)
    · simp only [if_neg searched, Finset.sum_const_zero, le_refl]
  unfold cfrDTrunkBudget
  generalize scheduledSites M clock (cut + remaining) who = sites
  induction sites with
  | nil => simp
  | cons site sites ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (hterm site) ih

end GameTheory.ReBeL
