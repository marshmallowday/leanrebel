/-
# Coupled trunk-only CFR-D updates

This low-level driver accepts an oracle response containing a continuation
profile and backed-up action scores from the same query. It does not assume a
root-regret certificate. The semantic backup and continuation contracts are
separate from this numerical recurrence and must be supplied by an adapter.
-/

import GameTheory.Analysis.ReBeL.PayoffBounds

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability GameTheory.Analysis.Approachability
open GameTheory.Math.Approachability GameTheory.Math.OrthantProjection

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Whether an information state belongs to the searched trunk. A history's
hidden state cannot affect this choice within one information set. -/
abbrev CFRDTrunk := (who : ι) → M.InfoState who → Bool

/-- A single response couples a legal continuation policy with the scores
backed up from its value estimates. Consistency is a separately proved
contract, not a root-regret or equilibrium conclusion stored in this data. -/
structure CFRDResponse where
  /-- Complete legal information-local choices, also on zero-reach branches. -/
  continuation : Profile M.behavioralSignature
  /-- Backed-up scores for the canonical decision information sites. -/
  actionValue : (who : ι) → (site : M.InformationSite who) → M.Choice who site.1 → ℝ

/-- Iteration and the complete current trunk profile identify the query. -/
abbrev CFRDOracle := Nat → Profile M.behavioralSignature → CFRDResponse M

variable [∀ who info, Fintype (M.Choice who info)]

/-- Keep current regret matching in the trunk and install only the response's
continuation outside it. Every output remains a canonical behavioral profile. -/
def cfrDProfile (trunk : CFRDTrunk M) (fallback : (who : ι) → M.Policy who)
    (response : CFRDResponse M) (state : CFRState M) : Profile M.behavioralSignature :=
  fun who info => if trunk who info = true then cfrProfile M fallback state who info
    else response.continuation who info

/-- The oracle cannot overwrite a searched site's current regret matcher. -/
theorem cfrDProfile_at_trunk (trunk : CFRDTrunk M)
    (fallback : (who : ι) → M.Policy who) (response : CFRDResponse M)
    (state : CFRState M) (who : ι) (site : M.InformationSite who)
    (searched : trunk who site.1 = true) :
    cfrDProfile M trunk fallback response state who site.1 =
      regretMatchWith (fallback who site.1) (state who site) := by
  simp only [cfrDProfile, searched, if_true, cfrProfile_at_site]

/-- Outside the trunk the actual play uses the very continuation returned
with the value vector, rather than an independently selected continuation. -/
theorem cfrDProfile_outside (trunk : CFRDTrunk M)
    (fallback : (who : ι) → M.Policy who) (response : CFRDResponse M)
    (state : CFRState M) (who : ι) (info : M.InfoState who)
    (outside : trunk who info ≠ true) :
    cfrDProfile M trunk fallback response state who info = response.continuation who info := by
  simp only [cfrDProfile, if_neg outside]

/-- Simultaneous vanilla average-regret coordinates. The oracle is queried
once from the previous-round trunk; every searched site reads that response.
Unsearched tables stay zero and are never mistaken for learned subgame tables. -/
def cfrDState (trunk : CFRDTrunk M) (fallback : (who : ι) → M.Policy who)
    (oracle : CFRDOracle M) : Nat → CFRState M
  | 0 => fun _ _ => 0
  | n + 1 =>
      let previous := cfrDState trunk fallback oracle n
      let strategy := cfrProfile M fallback previous
      let response := oracle n strategy
      fun who site => if trunk who site.1 = true then
        ((n : ℝ) / ((n : ℝ) + 1)) • previous who site +
          (1 / ((n : ℝ) + 1)) • regretPayoff
            (fun choice (_ : Unit) => response.actionValue who site choice)
            (strategy who site.1) ()
      else 0

/-- The actual oracle response at round n of the coupled recurrence. -/
def cfrDQuery (trunk : CFRDTrunk M) (fallback : (who : ι) → M.Policy who)
    (oracle : CFRDOracle M) (n : Nat) : CFRDResponse M :=
  oracle n (cfrProfile M fallback (cfrDState M trunk fallback oracle n))

/-- The full abstract continuation of the depth-limited round. -/
def cfrDPlay (trunk : CFRDTrunk M) (fallback : (who : ι) → M.Policy who)
    (oracle : CFRDOracle M) (n : Nat) : Profile M.behavioralSignature :=
  cfrDProfile M trunk fallback (cfrDQuery M trunk fallback oracle n)
    (cfrDState M trunk fallback oracle n)

/-- Current play and the learner agree at every searched decision. -/
theorem cfrDPlay_at_trunk (trunk : CFRDTrunk M)
    (fallback : (who : ι) → M.Policy who) (oracle : CFRDOracle M)
    (n : Nat) (who : ι) (site : M.InformationSite who)
    (searched : trunk who site.1 = true) :
    cfrDPlay M trunk fallback oracle n who site.1 =
      regretMatchWith (fallback who site.1)
        (cfrDState M trunk fallback oracle n who site) :=
  cfrDProfile_at_trunk M trunk fallback _ _ who site searched

/-- Pointwise update equation using exactly the produced response. -/
theorem cfrDState_succ_at (trunk : CFRDTrunk M)
    (fallback : (who : ι) → M.Policy who) (oracle : CFRDOracle M)
    (n : Nat) (who : ι) (site : M.InformationSite who)
    (searched : trunk who site.1 = true) :
    cfrDState M trunk fallback oracle (n + 1) who site =
      ((n : ℝ) / ((n : ℝ) + 1)) • cfrDState M trunk fallback oracle n who site +
        (1 / ((n : ℝ) + 1)) • regretPayoff
          (fun choice (k : Nat) =>
            (cfrDQuery M trunk fallback oracle k).actionValue who site choice)
          (regretMatchWith (fallback who site.1)
            (cfrDState M trunk fallback oracle n who site)) n := by
  simp only [cfrDState, searched, if_true, cfrDQuery, cfrProfile_at_site]
  rfl

/-- No updates are performed outside the trunk, at any iteration count. -/
theorem cfrDState_outside (trunk : CFRDTrunk M)
    (fallback : (who : ι) → M.Policy who) (oracle : CFRDOracle M)
    (n : Nat) (who : ι) (site : M.InformationSite who)
    (outside : trunk who site.1 ≠ true) :
    cfrDState M trunk fallback oracle n who site = 0 := by
  cases n <;> simp only [cfrDState, if_neg outside]

/-- The produced table equals the reactive regret-matching process along its
own produced value sequence. No independent environment sequence is postulated. -/
theorem cfrDState_eq_avgVec (trunk : CFRDTrunk M)
    (fallback : (who : ι) → M.Policy who) (oracle : CFRDOracle M)
    (who : ι) (site : M.InformationSite who) (searched : trunk who site.1 = true)
    (n : Nat) :
    cfrDState M trunk fallback oracle n who site =
      avgVec (regretPayoff (fun choice (k : Nat) =>
        (cfrDQuery M trunk fallback oracle k).actionValue who site choice))
        (regretMatchWith (fallback who site.1)) (fun k => k) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [cfrDState_succ_at M trunk fallback oracle n who site searched, ih]
      rfl

/-- Bounded backed-up action scores give the actual searched table a finite-T
bound. These are numerical score bounds, not the desired root-regret theorem. -/
theorem cfrDState_sq_distance_le (trunk : CFRDTrunk M)
    (fallback : (who : ι) → M.Policy who) (oracle : CFRDOracle M)
    (who : ι) (site : M.InformationSite who) (searched : trunk who site.1 = true)
    {bound : ℝ} (nonneg : 0 ≤ bound)
    (bounded : ∀ n choice,
      |(cfrDQuery M trunk fallback oracle n).actionValue who site choice| ≤ bound)
    (t : Nat) :
    Metric.infDist (cfrDState M trunk fallback oracle t who site) nonposOrthant ^ 2 *
        (t : ℝ) ≤ (2 * (Real.sqrt (Fintype.card (M.Choice who site.1)) * (2 * bound))) ^ 2 := by
  rw [cfrDState_eq_avgVec M trunk fallback oracle who site searched]
  apply regretMatchWith_sq_infDist_avg_le
  · positivity
  · intro law n
    exact regretPayoff_norm_le_of_abs_bound _ nonneg (fun choice k => bounded k choice) law n

/-- Actual predicted regret at a searched site uses the same local law that
was played. It is not the arithmetic average of past strategies. -/
def cfrDPredictedRegret (trunk : CFRDTrunk M)
    (fallback : (who : ι) → M.Policy who) (oracle : CFRDOracle M)
    (n : Nat) (who : ι) (site : M.InformationSite who) (choice : M.Choice who site.1) : ℝ :=
  (cfrDQuery M trunk fallback oracle n).actionValue who site choice -
    (cfrDPlay M trunk fallback oracle n who site.1).expect
      ((cfrDQuery M trunk fallback oracle n).actionValue who site)

/-- Every searched table coordinate is the average of the exact sequence of
predicted regrets used in the coupled updates, including the empty sum. -/
theorem cfrDState_coordinate_sum (trunk : CFRDTrunk M)
    (fallback : (who : ι) → M.Policy who) (oracle : CFRDOracle M)
    (who : ι) (site : M.InformationSite who) (searched : trunk who site.1 = true)
    (choice : M.Choice who site.1) (t : Nat) :
    (t : ℝ) * (cfrDState M trunk fallback oracle t who site).ofLp choice =
      ∑ n ∈ Finset.range t, cfrDPredictedRegret M trunk fallback oracle n who site choice := by
  induction t with
  | zero => simp
  | succ n ih =>
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      have h1 : ((n : ℝ) + 1) * ((n : ℝ) / ((n : ℝ) + 1)) = (n : ℝ) := by field_simp
      have h2 : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by field_simp
      rw [Finset.sum_range_succ, ← ih,
        cfrDState_succ_at M trunk fallback oracle n who site searched]
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, regretPayoff_ofLp, Nat.cast_add, Nat.cast_one]
      rw [mul_add, ← mul_assoc, h1, ← mul_assoc, h2, one_mul]
      rw [cfrDPredictedRegret, cfrDPlay_at_trunk M trunk fallback oracle n who site searched]

/-- Any local comparison law has cumulative predicted regret at most the
explicit square-root bound. The solver, score sequence and averaging are all
constructed above; the only numerical premise is bounded action scores. -/
theorem cfrD_local_cumulative_le (trunk : CFRDTrunk M)
    (fallback : (who : ι) → M.Policy who) (oracle : CFRDOracle M)
    (who : ι) (site : M.InformationSite who) (searched : trunk who site.1 = true)
    {bound : ℝ} (nonneg : 0 ≤ bound)
    (bounded : ∀ n choice,
      |(cfrDQuery M trunk fallback oracle n).actionValue who site choice| ≤ bound)
    (law : FinDist (M.Choice who site.1)) (t : Nat) :
    (t : ℝ) * law.expect (cfrDState M trunk fallback oracle t who site).ofLp ≤
      2 * (Real.sqrt (Fintype.card (M.Choice who site.1)) * (2 * bound)) * Real.sqrt t := by
  let x := cfrDState M trunk fallback oracle t who site
  let d := Metric.infDist x nonposOrthant
  let c := Real.sqrt (Fintype.card (M.Choice who site.1)) * (2 * bound)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd : 0 ≤ d := Metric.infDist_nonneg
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hs : d ^ 2 * (t : ℝ) ≤ (2 * c) ^ 2 :=
    cfrDState_sq_distance_le M trunk fallback oracle who site searched nonneg bounded t
  have he : law.expect x.ofLp ≤ d := by
    apply FinDist.expect_le_of_forall
    intro choice _
    exact le_trans (le_max_left _ _) (positivePart_le_infDist x choice)
  have hsquared : ((t : ℝ) * d) ^ 2 ≤ (2 * c * Real.sqrt t) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt ht]
    nlinarith [mul_le_mul_of_nonneg_right hs ht]
  have hlinear : (t : ℝ) * d ≤ 2 * c * Real.sqrt t := by
    have hr : 0 ≤ 2 * c * Real.sqrt t := by positivity
    nlinarith [mul_nonneg ht hd]
  exact le_trans (mul_le_mul_of_nonneg_left he ht) hlinear

end GameTheory.ReBeL
