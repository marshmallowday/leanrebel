/-
# Full-game regret transfer for the actual trunk CFR-D sequence

Numerical action-score accuracy and local counterfactual continuation bounds
are intermediate contracts. The root decomposition, simultaneous updates,
fixed-deviation coefficients and finite-time root bound are derived here.
No caller supplies a root-regret decomposition or a bound on the solver output.
-/

import GameTheory.Analysis.ReBeL.CFRDTrace
import GameTheory.Analysis.ReBeL.RootRegretBounds

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

/-- Perturbing every action value by at most error perturbs an action's
external regret by at most twice that error, under the SAME current law. -/
theorem predicted_regret_error {A : Type*} (law : FinDist A)
    (actual prediction : A → ℝ) (error : ℝ)
    (accurate : ∀ action, |prediction action - actual action| ≤ error) (action : A) :
    actual action - law.expect actual ≤
      prediction action - law.expect prediction + 2 * error := by
  have hpoint := abs_le.mp (accurate action)
  have hmean : |law.expect prediction - law.expect actual| ≤ error := by
    rw [← FinDist.expect_sub]
    exact FinDist.abs_expect_le_of_abs_bound _ _ (fun a _ => accurate a)
  have hmean' := abs_le.mp hmean
  linarith

private theorem cfrD_range_sum_expect {A : Type*} (law : FinDist A)
    (f : Nat → A → ℝ) (t : Nat) :
    (∑ n ∈ Finset.range t, law.expect (f n)) =
      law.expect (fun a => ∑ n ∈ Finset.range t, f n a) := by
  induction t with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ, ih, FinDist.expect_add]

private theorem cfrD_range_sum_list {A : Type*} (sites : List A)
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

/-- Explicit per-site cumulative allowance: actual regret matching in the
trunk, and counterfactual continuation accuracy outside it. -/
def cfrDSiteBudget (trunk : CFRDTrunk M) (who : ι) (site : M.InformationSite who)
    (scoreBound scoreError tailError : ℝ) (t : Nat) : ℝ :=
  if trunk who site.1 = true then
    2 * (Real.sqrt (Fintype.card (M.Choice who site.1)) * (2 * scoreBound)) * Real.sqrt t +
      (t : ℝ) * (2 * scoreError)
  else (t : ℝ) * tailError

/-- Both types of site allowance are nonnegative under their explicit contracts. -/
theorem cfrDSiteBudget_nonneg (trunk : CFRDTrunk M) (who : ι)
    (site : M.InformationSite who) {scoreBound scoreError tailError : ℝ}
    (hbound : 0 ≤ scoreBound) (herror : 0 ≤ scoreError) (htail : 0 ≤ tailError)
    (t : Nat) : 0 ≤ cfrDSiteBudget M trunk who site scoreBound scoreError tailError t := by
  unfold cfrDSiteBudget
  split_ifs <;> positivity

variable [Fintype ι] [DecidableEq ι] [Fintype E.History]
variable [∀ who, DecidableEq (M.InfoState who)]

/-- Score approximation is transferred to the canonical counterfactual
regret, including histories with zero own reach. -/
theorem cfrD_actionRegret_le_prediction (trunk : CFRDTrunk M)
    (fallback : (who : ι) → M.Policy who) (oracle : CFRDOracle M)
    (hrecall : M.PerfectRecall) (n : Nat) (who : ι) (site : M.InformationSite who)
    (payoff : E.History → ℝ) (fuel : Nat) (error : ℝ)
    (accurate : ∀ choice,
      |(cfrDQuery M trunk fallback oracle n).actionValue who site choice -
        M.counterfactualActionUtility (cfrDPlay M trunk fallback oracle n)
          who site payoff fuel choice| ≤ error) (choice : M.Choice who site.1) :
    M.counterfactualActionRegret (cfrDPlay M trunk fallback oracle n)
        who site payoff fuel choice ≤
      cfrDPredictedRegret M trunk fallback oracle n who site choice + 2 * error := by
  rw [actionRegret_eq_sub_expect M (M.actsOnceWhereItMatters_of_perfectRecall hrecall)]
  exact predicted_regret_error _ _ _ error accurate choice

/-- Game payoff bounds and action-score approximation imply a score bound;
this discharges the numerical size premise of the local learner. -/
theorem cfrD_score_abs_le (trunk : CFRDTrunk M)
    (fallback : (who : ι) → M.Policy who) (oracle : CFRDOracle M)
    (n : Nat) (who : ι) (site : M.InformationSite who)
    (payoff : E.History → ℝ) (fuel : Nat) {bound error : ℝ}
    (nonneg : 0 ≤ bound) (bounded : ∀ history, |payoff history| ≤ bound)
    (accurate : ∀ choice,
      |(cfrDQuery M trunk fallback oracle n).actionValue who site choice -
        M.counterfactualActionUtility (cfrDPlay M trunk fallback oracle n)
          who site payoff fuel choice| ≤ error) (choice : M.Choice who site.1) :
    |(cfrDQuery M trunk fallback oracle n).actionValue who site choice| ≤
      (Fintype.card (M.InformationHistory who site.1) : ℝ) * bound + error := by
  let strategy := cfrDPlay M trunk fallback oracle n
  have hactual : |M.counterfactualActionUtility strategy who site payoff fuel choice| ≤
      (Fintype.card (M.InformationHistory who site.1) : ℝ) * bound :=
    counterfactualValue_abs_le M strategy who site ((strategy who).commit site.1 choice)
      payoff nonneg bounded fuel
  calc
    _ ≤ |(cfrDQuery M trunk fallback oracle n).actionValue who site choice -
        M.counterfactualActionUtility strategy who site payoff fuel choice| +
        |M.counterfactualActionUtility strategy who site payoff fuel choice| := by
      simpa only [sub_add_cancel] using abs_add_le
        ((cfrDQuery M trunk fallback oracle n).actionValue who site choice -
          M.counterfactualActionUtility strategy who site payoff fuel choice)
        (M.counterfactualActionUtility strategy who site payoff fuel choice)
    _ ≤ _ := by linarith [accurate choice]

/-- Every local target law has bounded cumulative ACTUAL counterfactual
regret. Only trunk sites use learned tables; continuation sites use their
explicit local counterfactual response contract. -/
theorem cfrD_site_cumulative_le (trunk : CFRDTrunk M)
    (fallback : (who : ι) → M.Policy who) (oracle : CFRDOracle M)
    (hrecall : M.PerfectRecall) (who : ι) (site : M.InformationSite who)
    (payoff : E.History → ℝ) (fuel : Nat) (scoreBound scoreError tailError : ℝ)
    (nonneg : 0 ≤ scoreBound)
    (bounded : trunk who site.1 = true → ∀ n choice,
      |(cfrDQuery M trunk fallback oracle n).actionValue who site choice| ≤ scoreBound)
    (accurate : trunk who site.1 = true → ∀ n choice,
      |(cfrDQuery M trunk fallback oracle n).actionValue who site choice -
        M.counterfactualActionUtility (cfrDPlay M trunk fallback oracle n)
          who site payoff fuel choice| ≤ scoreError)
    (continuation : trunk who site.1 ≠ true → ∀ n choice,
      M.counterfactualActionRegret (cfrDPlay M trunk fallback oracle n)
        who site payoff fuel choice ≤ tailError)
    (law : FinDist (M.Choice who site.1)) (t : Nat) :
    (∑ n ∈ Finset.range t, law.expect
      (M.counterfactualActionRegret (cfrDPlay M trunk fallback oracle n)
        who site payoff fuel)) ≤
      cfrDSiteBudget M trunk who site scoreBound scoreError tailError t := by
  by_cases searched : trunk who site.1 = true
  · rw [cfrDSiteBudget, if_pos searched]
    have hstep (n : Nat) :
        law.expect (M.counterfactualActionRegret (cfrDPlay M trunk fallback oracle n)
            who site payoff fuel) ≤
          law.expect (cfrDPredictedRegret M trunk fallback oracle n who site) + 2 * scoreError := by
      rw [← FinDist.expect_const law (2 * scoreError), ← FinDist.expect_add]
      apply FinDist.expect_mono
      intro choice _
      exact cfrD_actionRegret_le_prediction M trunk fallback oracle hrecall n who site
        payoff fuel scoreError (accurate searched n) choice
    have htable :
        (∑ n ∈ Finset.range t, law.expect
          (cfrDPredictedRegret M trunk fallback oracle n who site)) =
        (t : ℝ) * law.expect (cfrDState M trunk fallback oracle t who site).ofLp := by
      rw [cfrD_range_sum_expect, ← FinDist.expect_smul]
      apply FinDist.expect_congr
      intro choice _
      exact (cfrDState_coordinate_sum M trunk fallback oracle who site searched choice t).symm
    calc
      _ ≤ ∑ n ∈ Finset.range t,
          (law.expect (cfrDPredictedRegret M trunk fallback oracle n who site) + 2 * scoreError) :=
        Finset.sum_le_sum fun n _ => hstep n
      _ = (t : ℝ) * law.expect (cfrDState M trunk fallback oracle t who site).ofLp +
          (t : ℝ) * (2 * scoreError) := by
        rw [Finset.sum_add_distrib, htable]
        simp
      _ ≤ _ := add_le_add
        (cfrD_local_cumulative_le M trunk fallback oracle who site searched nonneg
          (bounded searched) law t) (le_refl _)
  · rw [cfrDSiteBudget, if_neg searched]
    calc
      _ ≤ ∑ _n ∈ Finset.range t, tailError := by
        apply Finset.sum_le_sum
        intro n _
        exact FinDist.expect_le_of_forall _ _ tailError
          (fun choice _ => continuation searched n choice)
      _ = _ := by simp

/-- The explicit root allowance is summed over the constructed complete legal
schedule, not merely information sets reached by the current policy. -/
def cfrDCumulativeBudget (clock : ObservationClock M) (trunk : CFRDTrunk M)
    (horizon : Nat) (who : ι)
    (scoreBound scoreError tailError : M.InformationSite who → ℝ) (t : Nat) : ℝ :=
  ((scheduledSites M clock horizon who).map fun site =>
    cfrDSiteBudget M trunk who site (scoreBound site) (scoreError site) (tailError site) t).sum

/-- Canonical full-game regret of the ACTUAL coupled CFR-D sequence. Local
accuracy and continuation conditions are explicit; all decomposition,
averaging and learner premises are proved from the constructed trace. -/
theorem cfrD_cumulative_root_regret_le (trunk : CFRDTrunk M)
    (fallback : (who : ι) → M.Policy who) (oracle : CFRDOracle M)
    (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (payoff : E.History → ℝ) (horizon : Nat) (who : ι)
    (scoreBound scoreError tailError : M.InformationSite who → ℝ)
    (bound_nonneg : ∀ site, 0 ≤ scoreBound site)
    (error_nonneg : ∀ site, 0 ≤ scoreError site)
    (tail_nonneg : ∀ site, 0 ≤ tailError site)
    (bounded : ∀ site, trunk who site.1 = true → ∀ n choice,
      |(cfrDQuery M trunk fallback oracle n).actionValue who site choice| ≤ scoreBound site)
    (accurate : ∀ site, trunk who site.1 = true → ∀ n choice,
      |(cfrDQuery M trunk fallback oracle n).actionValue who site choice -
        M.counterfactualActionUtility (cfrDPlay M trunk fallback oracle n)
          who site payoff (horizon - clock.depth who site.1) choice| ≤ scoreError site)
    (continuation : ∀ site, trunk who site.1 ≠ true → ∀ n choice,
      M.counterfactualActionRegret (cfrDPlay M trunk fallback oracle n)
        who site payoff (horizon - clock.depth who site.1) choice ≤ tailError site)
    (target : M.BehavioralPolicy who) (t : Nat) :
    (∑ n ∈ Finset.range t,
      ((M.runBehavioral (Profile.update (cfrDPlay M trunk fallback oracle n) who target)
          horizon).expect payoff -
        (M.runBehavioral (cfrDPlay M trunk fallback oracle n) horizon).expect payoff)) ≤
      cfrDCumulativeBudget M clock trunk horizon who scoreBound scoreError tailError t := by
  simp_rw [scheduled_root_gain M clock hrecall]
  rw [cfrD_range_sum_list]
  have hterm (site : M.InformationSite who) :
      (∑ n ∈ Finset.range t, targetRegretTerm M clock (cfrDPlay M trunk fallback oracle n)
          who target payoff horizon site) ≤
        cfrDSiteBudget M trunk who site (scoreBound site) (scoreError site) (tailError site) t := by
    unfold targetRegretTerm
    have hreach (n : Nat) := targetReach_independent_profile M
      (cfrDPlay M trunk fallback oracle n) (cfrDPlay M trunk fallback oracle 0)
      who target site.2.choose.1.trace
    simp_rw [hreach]
    rw [← Finset.mul_sum]
    have hlocal := cfrD_site_cumulative_le M trunk fallback oracle hrecall who site
      payoff (horizon - clock.depth who site.1) (scoreBound site) (scoreError site)
      (tailError site) (bound_nonneg site) (bounded site) (accurate site) (continuation site)
      (target site.1) t
    have hr := playerReach_unitInterval M
      (Profile.update (cfrDPlay M trunk fallback oracle 0) who target)
      who site.2.choose.1.trace
    have hb := cfrDSiteBudget_nonneg M trunk who site
      (bound_nonneg site) (error_nonneg site) (tail_nonneg site) t
    exact le_trans (mul_le_mul_of_nonneg_left hlocal hr.1)
      (by simpa using mul_le_mul_of_nonneg_right hr.2 hb)
  unfold cfrDCumulativeBudget
  generalize scheduledSites M clock horizon who = sites
  induction sites with
  | nil => simp
  | cons site sites ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (hterm site) ih

end GameTheory.ReBeL
