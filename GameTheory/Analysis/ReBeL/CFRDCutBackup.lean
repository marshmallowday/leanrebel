/-
# Terminal-exact, live-cut-only CFR-D action backups

The numerical score runs only the searched prefix. Its one information-value
vector is coupled to the same continuation used in the proof. Terminal and
fuel-exhausted leaves use the actual payoff, without consulting that vector.
Full scores are a proof device: their action-independent offset cancels in
regret, so they need not equal canonical counterfactual action utilities.
-/

import GameTheory.Analysis.ReBeL.CFRDProbe

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- A live cut still has fuel and is not a real terminal. The flag is used
only to evaluate stopped leaves, never to give a policy hidden information. -/
def cfrDCutLive (remaining : Nat) (history : E.History) : Bool := by
  classical
  exact decide (remaining ≠ 0 ∧ ¬ E.terminal history.state)

/-- Exhausted-fuel leaves are never oracle queries. -/
theorem cfrDCutLive_zero (history : E.History) :
    cfrDCutLive 0 history = false := by
  simp [cfrDCutLive]

/-- True terminal leaves are never oracle queries, even with unused fuel. -/
theorem cfrDCutLive_terminal (remaining : Nat) (history : E.History)
    (terminal : E.terminal history.state) : cfrDCutLive remaining history = false := by
  simp [cfrDCutLive, terminal]

variable [Fintype ι]

/-- The full continuation at a stopped leaf is exactly its current payoff. -/
theorem cfrDCutValue_stopped (base : Profile M.behavioralSignature)
    (payoff : E.History → ℝ) (remaining : Nat) (history : E.History)
    (stopped : cfrDCutLive remaining history ≠ true) :
    (M.runBehavioralFrom base remaining history).expect payoff = payoff history := by
  classical
  by_cases zero : remaining = 0
  · subst remaining
    simp [InformationModel.runBehavioralFrom]
  · have terminal : E.terminal history.state := by
      by_contra not_terminal
      apply stopped
      simp only [cfrDCutLive, decide_eq_true_eq]
      exact ⟨zero, not_terminal⟩
    rw [M.runBehavioralFrom_of_terminal base remaining terminal, FinDist.expect_pure]

/-- Only a live cut consults the information-value vector. -/
def cfrDCutLeafValue (who : ι) (payoff : E.History → ℝ) (remaining : Nat)
    (prediction : M.InfoState who → ℝ) (history : E.History) : ℝ :=
  if cfrDCutLive remaining history = true then prediction (M.infoOf who history.trace)
    else payoff history

variable [DecidableEq ι] [∀ who info, Fintype (M.Choice who info)]

/-- Accuracy is required only on live information fibers of the dominating
joint law. The continuation is the actual same-iteration legal profile. -/
def CFRDCutAccurate (base : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι) (payoff : E.History → ℝ)
    (cut remaining : Nat) (prediction : M.InfoState who → ℝ) (error : ℝ) : Prop :=
  ∀ info,
    (info, true) ∈ ((unilateralReferenceLaw M base fallback who cut).map
      (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))).support →
    |prediction info - conditionalOracleValue (unilateralReferenceLaw M base fallback who cut)
      (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))
      (fun history => (M.runBehavioralFrom base remaining history).expect payoff)
      (info, true)| ≤ error

/-- The backed-up score contains no full-game rollout. Probing changes only
strictly earlier own decisions and normalizes by positive structural reach. -/
def cfrDCutScore (clock : ObservationClock M) (base : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who) (payoff : E.History → ℝ) (cut remaining : Nat)
    (prediction : M.InfoState who → ℝ) (choice : M.Choice who site.1) : ℝ :=
  (M.runBehavioral (Profile.update base who
    ((cfrDProbePolicy M clock base fallback who (clock.depth who site.1)).commit site.1 choice))
      cut).expect (cfrDCutLeafValue M who payoff remaining prediction) /
    M.playerReachProbability (uniformLegalProfile M fallback) who site.2.choose.1.trace

/-- The single live value vector controls every backed-up action, including
zero factual own reach. Terminal rewards require no approximation contract. -/
theorem cfrDCutScore_error (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (base : Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (who : ι) [DecidableEq (M.InfoState who)] (site : M.InformationSite who)
    (payoff : E.History → ℝ) (cut remaining : Nat) (searched : clock.depth who site.1 < cut)
    (prediction : M.InfoState who → ℝ) (error : ℝ) (nonneg : 0 ≤ error)
    (accurate : CFRDCutAccurate M base fallback who payoff cut remaining prediction error)
    (choice : M.Choice who site.1) :
    |cfrDCutScore M clock base fallback who site payoff cut remaining prediction choice -
        cfrDProbeFullScore M clock base fallback who site payoff (cut + remaining) choice| ≤
      error / M.playerReachProbability (uniformLegalProfile M fallback)
        who site.2.choose.1.trace := by
  let policy := (cfrDProbePolicy M clock base fallback who
    (clock.depth who site.1)).commit site.1 choice
  let value := fun history => (M.runBehavioralFrom base remaining history).expect payoff
  have estimate := terminalExact_reweight_error
    (unilateralReferenceLaw M base fallback who cut)
    (M.runBehavioral (Profile.update base who policy) cut)
    (fun history => M.infoOf who history.trace) (cfrDCutLive (E := E) remaining)
    (unilateralDensity M base fallback who policy)
    (unilateralReference_density M hrecall base fallback who policy cut)
    value prediction error nonneg accurate
  have backup : (fun history => if cfrDCutLive remaining history = true then
        prediction (M.infoOf who history.trace) else value history) =
      cfrDCutLeafValue M who payoff remaining prediction := by
    funext history
    by_cases active : cfrDCutLive remaining history = true
    · simp only [cfrDCutLeafValue, if_pos active]
    · simp only [cfrDCutLeafValue, if_neg active]
      exact cfrDCutValue_stopped M base payoff remaining history active
  rw [backup] at estimate
  have full : (M.runBehavioral (Profile.update base who policy) (cut + remaining)).expect payoff =
      (M.runBehavioral (Profile.update base who policy) cut).expect value := by
    rw [run_unilateral_bind_at_cut M clock base who policy cut remaining
      (cfrDProbe_commit_future M clock base fallback who site choice cut searched),
      FinDist.expect_bind]
  rw [← full] at estimate
  unfold cfrDCutScore cfrDProbeFullScore
  rw [← sub_div, abs_div, abs_of_pos (uniformOwnReach_positive M fallback who _)]
  exact div_le_div_of_nonneg_right estimate (le_of_lt (uniformOwnReach_positive M fallback who _))

/-- The ideal comparison score has a bound depending only on the game's
payoff bound and the positive, game-dependent uniform own reach. -/
theorem cfrDProbeFullScore_abs_le (clock : ObservationClock M)
    (base : Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (who : ι) [DecidableEq (M.InfoState who)] (site : M.InformationSite who)
    (payoff : E.History → ℝ) (horizon : Nat) (bound : ℝ)
    (bounded : ∀ history, |payoff history| ≤ bound) (choice : M.Choice who site.1) :
    |cfrDProbeFullScore M clock base fallback who site payoff horizon choice| ≤
      bound / M.playerReachProbability (uniformLegalProfile M fallback)
        who site.2.choose.1.trace := by
  unfold cfrDProbeFullScore
  rw [abs_div, abs_of_pos (uniformOwnReach_positive M fallback who _)]
  apply div_le_div_of_nonneg_right _ (le_of_lt (uniformOwnReach_positive M fallback who _))
  exact FinDist.abs_expect_le_of_abs_bound _ _ (fun history _ => bounded history)

/-- Oracle accuracy and bounded game payoff discharge the numerical score
bound needed by the actual regret-matching recurrence. -/
theorem cfrDCutScore_abs_le (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (base : Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (who : ι) [DecidableEq (M.InfoState who)] (site : M.InformationSite who)
    (payoff : E.History → ℝ) (cut remaining : Nat) (searched : clock.depth who site.1 < cut)
    (prediction : M.InfoState who → ℝ) (bound error : ℝ) (nonneg : 0 ≤ error)
    (bounded : ∀ history, |payoff history| ≤ bound)
    (accurate : CFRDCutAccurate M base fallback who payoff cut remaining prediction error)
    (choice : M.Choice who site.1) :
    |cfrDCutScore M clock base fallback who site payoff cut remaining prediction choice| ≤
      (bound + error) / M.playerReachProbability (uniformLegalProfile M fallback)
        who site.2.choose.1.trace := by
  let score := cfrDCutScore M clock base fallback who site payoff cut remaining prediction choice
  let actual := cfrDProbeFullScore M clock base fallback who site payoff (cut + remaining) choice
  have estimate := cfrDCutScore_error M clock hrecall base fallback who site payoff cut remaining
    searched prediction error nonneg accurate choice
  have full := cfrDProbeFullScore_abs_le M clock base fallback who site payoff
    (cut + remaining) bound bounded choice
  calc
    |score| ≤ |score - actual| + |actual| := by
      simpa only [sub_add_cancel] using abs_add_le (score - actual) actual
    _ ≤ error / M.playerReachProbability (uniformLegalProfile M fallback)
          who site.2.choose.1.trace +
        bound / M.playerReachProbability (uniformLegalProfile M fallback)
          who site.2.choose.1.trace := add_le_add estimate full
    _ = _ := by rw [← add_div, add_comm error bound]

/-- Regret, rather than an incorrectly aligned raw action value, is what
transfers to the learner. The full score's common offset cancels exactly. -/
theorem cfrDCutScore_regret_le (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (base : Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (who : ι) [DecidableEq (M.InfoState who)] (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (cut remaining : Nat) (searched : clock.depth who site.1 < cut)
    (prediction : M.InfoState who → ℝ) (error : ℝ) (nonneg : 0 ≤ error)
    (accurate : CFRDCutAccurate M base fallback who payoff cut remaining prediction error)
    (choice : M.Choice who site.1) :
    M.counterfactualActionRegret base who site payoff
        (cut + remaining - clock.depth who site.1) choice ≤
      cfrDCutScore M clock base fallback who site payoff cut remaining prediction choice -
        (base who site.1).expect
          (cfrDCutScore M clock base fallback who site payoff cut remaining prediction) +
        2 * (error / M.playerReachProbability (uniformLegalProfile M fallback)
          who site.2.choose.1.trace) := by
  rw [← cfrDProbeFullScore_regret M clock hrecall base fallback who site payoff
    (cut + remaining) (by omega) choice]
  exact predicted_regret_error _ _ _ _
    (fun action => cfrDCutScore_error M clock hrecall base fallback who site payoff cut remaining
      searched prediction error nonneg accurate action) choice

/-- At full search depth, every prediction is ignored and the score is exact.
Finite-iteration regret matching is still required; this is not exact Nash. -/
theorem cfrDCutScore_zero_remaining (clock : ObservationClock M)
    (base : Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (who : ι) [DecidableEq (M.InfoState who)] (site : M.InformationSite who)
    (payoff : E.History → ℝ) (cut : Nat) (prediction : M.InfoState who → ℝ)
    (choice : M.Choice who site.1) :
    cfrDCutScore M clock base fallback who site payoff cut 0 prediction choice =
      cfrDProbeFullScore M clock base fallback who site payoff cut choice := by
  have leaf : cfrDCutLeafValue M who payoff 0 prediction = payoff := by
    funext history
    simp only [cfrDCutLeafValue, cfrDCutLive_zero, Bool.false_eq_true, if_false]
  simp only [cfrDCutScore, cfrDProbeFullScore, leaf]

end GameTheory.ReBeL
