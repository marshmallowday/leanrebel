/-
# Uniform finite-time whole-policy CFR regret

The constructed schedule and root identity connect the actual simultaneous
CFR tables to every legal behavioral deviation. All payoff constants are
derived from bounded game payoffs and finite information fibers. No supplied
root decomposition or bound on the generated learner is an assumption.
-/

import GameTheory.Analysis.ReBeL.RootDecomposition
import GameTheory.Analysis.ReBeL.PayoffBounds

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability GameTheory.Math.OrthantProjection

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι] [Fintype E.History]
variable [∀ who, DecidableEq (M.InfoState who)]
variable [∀ who info, Fintype (M.Choice who info)]

/-- Fixing the deviator's policy fixes its own-reach coefficient, independently
of all opponents and of the baseline policy being replaced. -/
theorem targetReach_independent_profile
    (first second : Profile M.behavioralSignature) (who : ι)
    (target : M.BehavioralPolicy who) {state : E.State} (trace : E.Trace state) :
    M.playerReachProbability (Profile.update first who target) who trace =
      M.playerReachProbability (Profile.update second who target) who trace := by
  apply ownReach_eq_of_agree_before M _ _ who trace.length
  · intro history _ _ _
    rw [Profile.update_same, Profile.update_same]
  · exact le_rfl

/-- Finite iteration sums commute with finite-support expectation. -/
private theorem range_sum_expect {A : Type*} (law : FinDist A)
    (f : ℕ → A → ℝ) (t : ℕ) :
    (∑ n ∈ Finset.range t, law.expect (f n)) =
      law.expect (fun a => ∑ n ∈ Finset.range t, f n a) := by
  induction t with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ, ih, FinDist.expect_add]

/-- Finite iteration sums commute with the actual chronological list sum. -/
private theorem range_sum_list {A : Type*} (sites : List A)
    (f : ℕ → A → ℝ) (t : ℕ) :
    (∑ n ∈ Finset.range t, (sites.map (f n)).sum) =
      (sites.map (fun site => ∑ n ∈ Finset.range t, f n site)).sum := by
  induction sites with
  | nil => simp
  | cons site sites ih => simp [Finset.sum_add_distrib, ih]

/-- Every coordinate of a coupled table is the average of its actual
counterfactual regrets, including the empty sum at iteration zero. -/
theorem cfrState_coordinate_sum (clock : ObservationClock M)
    (fallback : (who : ι) → M.Policy who) (payoff : ι → E.History → ℝ)
    (horizon : ℕ) (who : ι) (site : M.InformationSite who) (t : ℕ)
    (choice : M.Choice who site.1) :
    (t : ℝ) * (cfrState M clock fallback payoff horizon t who site).ofLp choice =
      ∑ n ∈ Finset.range t,
        M.counterfactualActionRegret (cfrPlay M clock fallback payoff horizon n)
          who site (payoff who) (horizon - clock.depth who site.1) choice := by
  have h := congrArg (fun x : EuclideanSpace ℝ (M.Choice who site.1) => x.ofLp choice)
    (cfrState_smul_eq_sum M clock fallback payoff horizon who site t)
  simpa only [WithLp.ofLp_smul, WithLp.ofLp_sum, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, InformationModel.localCounterfactualRegretVector,
    WithLp.ofLp_toLp] using h

/-- Summing the derived root identity uses one fixed deviation's coefficients
and the actual coupled local tables. The target can be any behavioral policy. -/
theorem cfr_cumulative_root_eq_tables (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : ι) → M.Policy who)
    (payoff : ι → E.History → ℝ) (horizon : ℕ) (who : ι)
    (target : M.BehavioralPolicy who) (t : ℕ) :
    (∑ n ∈ Finset.range t,
      ((M.runBehavioral
        (Profile.update (cfrPlay M clock fallback payoff horizon n) who target)
        horizon).expect (payoff who) -
        (M.runBehavioral (cfrPlay M clock fallback payoff horizon n) horizon).expect
          (payoff who))) =
      ((scheduledSites M clock horizon who).map (fun site =>
        M.playerReachProbability
          (Profile.update (cfrPlay M clock fallback payoff horizon 0) who target)
          who site.2.choose.1.trace *
            ((t : ℝ) * (target site.1).expect
              (cfrState M clock fallback payoff horizon t who site).ofLp))).sum := by
  simp_rw [scheduled_root_gain M clock hrecall]
  rw [range_sum_list]
  apply congrArg List.sum
  apply List.map_congr_left
  intro site _
  unfold targetRegretTerm
  have hreach (n : ℕ) := targetReach_independent_profile M
    (cfrPlay M clock fallback payoff horizon n)
    (cfrPlay M clock fallback payoff horizon 0) who target site.2.choose.1.trace
  simp_rw [hreach]
  rw [← Finset.mul_sum, range_sum_expect]
  have hexpected :
      (target site.1).expect (fun choice => ∑ n ∈ Finset.range t,
        M.counterfactualActionRegret (cfrPlay M clock fallback payoff horizon n)
          who site (payoff who) (horizon - clock.depth who site.1) choice) =
      (t : ℝ) * (target site.1).expect
        (cfrState M clock fallback payoff horizon t who site).ofLp := by
    rw [← FinDist.expect_smul]
    apply FinDist.expect_congr
    intro choice _
    exact (cfrState_coordinate_sum M clock fallback payoff horizon who site t choice).symm
  rw [hexpected]

/-- The actual table bounds cumulative regret for every local target law,
with a constant derived from the game's absolute payoff range. -/
theorem cfr_local_cumulative_le (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (fallback : (who : ι) → M.Policy who) (payoff : ι → E.History → ℝ)
    (horizon : ℕ) (who : ι) (site : M.InformationSite who)
    {bound : ℝ} (hbound0 : 0 ≤ bound)
    (hbound : ∀ history, |payoff who history| ≤ bound)
    (law : FinDist (M.Choice who site.1)) (t : ℕ) :
    (t : ℝ) * law.expect (cfrState M clock fallback payoff horizon t who site).ofLp ≤
      2 * counterfactualPayoffBound M who site bound * Real.sqrt t := by
  let x := cfrState M clock fallback payoff horizon t who site
  let d := Metric.infDist x nonposOrthant
  let c := counterfactualPayoffBound M who site bound
  have hc : 0 ≤ c := counterfactualPayoffBound_nonneg M who site hbound0
  have hd : 0 ≤ d := Metric.infDist_nonneg
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hs : d ^ 2 * (t : ℝ) ≤ (2 * c) ^ 2 :=
    cfrState_sq_distance_le M clock hrecall fallback payoff horizon who site hc
      (canonical_regretPayoff_norm_le M who site (payoff who) hbound0 hbound
        (horizon - clock.depth who site.1)) t
  have he : law.expect x.ofLp ≤ d := by
    apply FinDist.expect_le_of_forall
    intro choice _
    exact le_trans (le_max_left _ _) (max_coord_le_infDist x choice)
  have hsquared : ((t : ℝ) * d) ^ 2 ≤ (2 * c * Real.sqrt t) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt ht]
    nlinarith [mul_le_mul_of_nonneg_right hs ht]
  have hlinear : (t : ℝ) * d ≤ 2 * c * Real.sqrt t := by
    have hr : 0 ≤ 2 * c * Real.sqrt t := by positivity
    nlinarith [mul_nonneg ht hd]
  exact le_trans (mul_le_mul_of_nonneg_left he ht) hlinear

/-- The explicit full-game finite-time constant, independent of the deviation. -/
def cfrCumulativeBound (clock : ObservationClock M) (horizon : ℕ) (who : ι)
    (bound : ℝ) (t : ℕ) : ℝ :=
  ((scheduledSites M clock horizon who).map (fun site =>
    2 * counterfactualPayoffBound M who site bound * Real.sqrt t)).sum

/-- Constructed full-game CFR has a uniform finite-time root-regret bound
against every legal behavioral policy. Only structural game hypotheses and a
bound on game payoffs are inputs; all scheduling, realization, local learning
and root decomposition obligations are discharged by the implementation. -/
theorem cfr_cumulative_root_regret_le (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : ι) → M.Policy who)
    (payoff : ι → E.History → ℝ) (horizon : ℕ) (who : ι)
    {bound : ℝ} (hbound0 : 0 ≤ bound)
    (hbound : ∀ history, |payoff who history| ≤ bound)
    (target : M.BehavioralPolicy who) (t : ℕ) :
    (∑ n ∈ Finset.range t,
      ((M.runBehavioral
        (Profile.update (cfrPlay M clock fallback payoff horizon n) who target)
        horizon).expect (payoff who) -
        (M.runBehavioral (cfrPlay M clock fallback payoff horizon n) horizon).expect
          (payoff who))) ≤ cfrCumulativeBound M clock horizon who bound t := by
  rw [cfr_cumulative_root_eq_tables M clock hrecall]
  have hterm (site : M.InformationSite who) :
      M.playerReachProbability
          (Profile.update (cfrPlay M clock fallback payoff horizon 0) who target)
          who site.2.choose.1.trace *
        ((t : ℝ) * (target site.1).expect
          (cfrState M clock fallback payoff horizon t who site).ofLp) ≤
      2 * counterfactualPayoffBound M who site bound * Real.sqrt t := by
    have hr := playerReach_unitInterval M
      (Profile.update (cfrPlay M clock fallback payoff horizon 0) who target)
      who site.2.choose.1.trace
    have hl := cfr_local_cumulative_le M clock hrecall fallback payoff horizon who site
      hbound0 hbound (target site.1) t
    have hc := counterfactualPayoffBound_nonneg M who site hbound0
    have hb : 0 ≤ 2 * counterfactualPayoffBound M who site bound * Real.sqrt t :=
      by positivity
    exact le_trans (mul_le_mul_of_nonneg_left hl hr.1)
      (by simpa using mul_le_mul_of_nonneg_right hr.2 hb)
  unfold cfrCumulativeBound
  generalize scheduledSites M clock horizon who = sites
  induction sites with
  | nil => simp
  | cons site sites ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (hterm site) ih

/-- Positive-iteration average regret is bounded by the explicit cumulative
constant divided by the iteration count. The cumulative theorem also covers
zero iterations, but no equilibrium claim is made for a zero-sample average. -/
theorem cfr_average_root_regret_le (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : ι) → M.Policy who)
    (payoff : ι → E.History → ℝ) (horizon : ℕ) (who : ι)
    {bound : ℝ} (hbound0 : 0 ≤ bound)
    (hbound : ∀ history, |payoff who history| ≤ bound)
    (target : M.BehavioralPolicy who) {t : ℕ} (ht : 0 < t) :
    (∑ n ∈ Finset.range t,
      ((M.runBehavioral
        (Profile.update (cfrPlay M clock fallback payoff horizon n) who target)
        horizon).expect (payoff who) -
        (M.runBehavioral (cfrPlay M clock fallback payoff horizon n) horizon).expect
          (payoff who))) / t ≤ cfrCumulativeBound M clock horizon who bound t / t :=
  div_le_div_of_nonneg_right
    (cfr_cumulative_root_regret_le M clock hrecall fallback payoff horizon who
      hbound0 hbound target t) (le_of_lt (by exact_mod_cast ht))

end GameTheory.ReBeL
