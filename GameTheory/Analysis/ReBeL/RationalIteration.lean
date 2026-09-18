/-
# Every rational full-game CFR iteration refines the constructed real solver

The only game certificate concerns primitive rows, local observations and
complete history enumeration. Actual counterfactual evaluation supplies every
update. There is no input regret oracle, assumed iteration trace or assumed
root decomposition. All sites use the identical previous-round snapshot.
-/

import GameTheory.Analysis.ReBeL.RationalCounterfactual

noncomputable section

namespace GameTheory.ReBeL.Rational

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe ui us ua up uq uk
variable {ι : Type ui} {E : ExecutionProtocol.{ui, us, ua} ι}
variable (M : InformationModel.{ui, us, ua, up, uq, uk} E)
variable (G : HistoryTable E.History M.InfoState M.Choice)
variable [∀ who info, Fintype (M.Choice who info)]
variable [∀ who info, DecidableEq (M.Choice who info)]

/-- Agreement of regret coordinates at every genuine site implies exact
agreement of the assembled profile at all information states, including
unrealized observations and zero-positive-regret fallback branches. -/
theorem profile_realizes
    (hdecision : ∀ who info, G.decision who info = true ↔
      ∃ history : M.InformationHistory who info,
        ¬ E.terminal history.1.state ∧ ∃ action, some action ∈ M.menu who info)
    (fallback : (who : ι) → M.Policy who)
    (numeric : Profile (tableSignature E.History M.InfoState M.Choice))
    (semantic : CFRState M)
    (hstate : ∀ who (site : M.InformationSite who) choice,
      (numeric who site.1 choice : ℝ) = (semantic who site).ofLp choice) :
    Realizes M (G.profile fallback numeric) (cfrProfile M fallback semantic) := by
  classical
  intro who info choice
  by_cases h : ∃ history : M.InformationHistory who info,
      ¬ E.terminal history.1.state ∧ ∃ action, some action ∈ M.menu who info
  · rw [HistoryTable.profile, if_pos ((hdecision who info).mpr h),
      cfrProfile, dif_pos h]
    have hvector : realScore (numeric who info) = semantic who ⟨info, h⟩ := by
      ext action
      exact hstate who ⟨info, h⟩ action
    rw [← hvector]
    exact cast_matchProb (fallback who info) (numeric who info) choice
  · rw [HistoryTable.profile, if_neg (fun hp => h ((hdecision who info).mp hp)),
      cfrProfile, dif_neg h]
    exact cast_pointMass (fallback who info) choice

variable [Fintype ι] [DecidableEq ι]
variable [∀ who, DecidableEq (M.InfoState who)]

/-- The numeric recurrence exposed at one coordinate without unfolding the
dependent whole-table carrier under a rewrite. -/
theorem state_succ_at (fallback : (who : ι) → M.Policy who)
    (horizon round : ℕ) (who : ι) (info : M.InfoState who) (choice : M.Choice who info) :
    G.state fallback horizon (round + 1) who info choice =
      if G.decision who info then
        averageRegretUpdate round (G.state fallback horizon round who info choice)
          (G.instantaneousRegret (G.play fallback horizon round) who info horizon choice)
      else 0 := rfl

variable [Fintype E.History]

/-- Exact equality of every generated regret coordinate for every iteration,
proved by induction using the actual full-game rational evaluator. -/
theorem state_eq_cfrState (clock : ObservationClock M)
    (payoff : ι → E.History → ℝ) (cert : TableCertificate M G clock payoff)
    (fallback : (who : ι) → M.Policy who) (horizon round : ℕ) :
    ∀ who (site : M.InformationSite who) choice,
      (G.state fallback horizon round who site.1 choice : ℝ) =
        (cfrState M clock fallback payoff horizon round who site).ofLp choice := by
  induction round with
  | zero =>
      intro who site choice
      simp [HistoryTable.state, cfrState]
  | succ round ih =>
      have hprofile : Realizes M (G.play fallback horizon round)
          (cfrPlay M clock fallback payoff horizon round) :=
        profile_realizes M G cert.decision_correct fallback
          (G.state fallback horizon round)
          (cfrState M clock fallback payoff horizon round) ih
      intro who site choice
      rw [state_succ_at,
        if_pos ((cert.decision_correct who site.1).mpr site.2),
        cast_averageRegretUpdate,
        instantaneousRegret_eq M G clock payoff cert _ _ hprofile,
        ih who site choice, cfrState_succ_at]
      rfl

/-- The rational and real solvers generate the very same information-local
behavioral law in every round, not merely numerically close root values. -/
theorem play_realizes_cfrPlay (clock : ObservationClock M)
    (payoff : ι → E.History → ℝ) (cert : TableCertificate M G clock payoff)
    (fallback : (who : ι) → M.Policy who) (horizon round : ℕ) :
    Realizes M (G.play fallback horizon round)
      (cfrPlay M clock fallback payoff horizon round) :=
  profile_realizes M G cert.decision_correct fallback
    (G.state fallback horizon round) (cfrState M clock fallback payoff horizon round)
    (state_eq_cfrState M G clock payoff cert fallback horizon round)

end GameTheory.ReBeL.Rational
