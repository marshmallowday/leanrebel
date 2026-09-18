/-
# Rational full-game counterfactual values refine Protocol values

Every input certificate concerns primitive game data or its enumeration. No
counterfactual value, regret, solver trace, root identity or equilibrium is a
certificate field. Those policy-dependent facts are derived here and downstream.
-/

import GameTheory.Analysis.ReBeL.RationalReach
import GameTheory.Analysis.ReBeL.RationalArithmetic
import GameTheory.Analysis.ReBeL.CFRTrace

noncomputable section

namespace GameTheory.ReBeL.Rational

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Protocol.InformationModel GameTheory.Math.Probability

universe ui us ua up uq uk
variable {ι : Type ui} {E : ExecutionProtocol.{ui, us, ua} ι}
variable (M : InformationModel.{ui, us, ua, up, uq, uk} E)
variable (G : HistoryTable E.History M.InfoState M.Choice)

/-- The numeric table encodes primitive canonical game data and the local clock.
This certificate is independent of every policy and every iteration count. -/
structure TableCertificate (clock : ObservationClock M) (payoff : ι → E.History → ℝ) : Prop where
  /-- Runtime observations encode precisely the existing information map. -/
  info_correct : G.info = fun who history => M.infoOf who history.trace
  /-- Runtime terminality is the existing stopping predicate. -/
  terminal_correct : ∀ history, G.terminal history = true ↔ E.terminal history.state
  /-- One fixed legal joint's sparse chance rows encode the actual transition. -/
  chance_rows : ChanceRows M G info_correct
  /-- A history is not duplicated in the numerical enumeration. -/
  histories_nodup : G.histories.Nodup
  /-- Every legal history occurs, including off-policy histories. -/
  histories_complete : ∀ history, history ∈ G.histories
  /-- The stored own-choice records are exact serializations of legal traces. -/
  path_correct : ∀ who history, G.ownPath who history = choicePath M who history.trace
  /-- Policy-independent chance factors are the actual chance product. -/
  chance_correct : ∀ history, ((G.chanceFactors history).prod : ℝ) = chanceReach history.trace
  /-- Cumulative rational payoffs denote the supplied semantic payoff. -/
  payoff_correct : ∀ history who, (G.payoff history who : ℝ) = payoff who history
  /-- Decision rows are exactly genuine canonical information sites. -/
  decision_correct : ∀ who info, G.decision who info = true ↔
    ∃ history : M.InformationHistory who info,
      ¬ E.terminal history.1.state ∧ ∃ action, some action ∈ M.menu who info
  /-- Both evaluators use the same information-local absolute clock. -/
  depth_correct : G.depth = clock.depth

private theorem cast_map_sum {α : Type*} (xs : List α) (f : α → ℚ) :
    ((xs.map f).sum : ℝ) = (xs.map fun x => (f x : ℝ)).sum := by
  induction xs with
  | nil => simp
  | cons head tail ih => simp only [List.map_cons, List.sum_cons, Rat.cast_add, ih]

private theorem list_sum_eq_univ {α : Type*} [Fintype α] (xs : List α)
    (hnodup : xs.Nodup) (hcomplete : ∀ a, a ∈ xs) (f : α → ℝ) :
    (xs.map f).sum = ∑ a, f a := by
  classical
  have hset : xs.toFinset = Finset.univ := by
    ext a
    simp [hcomplete a]
  rw [← List.sum_toFinset f hnodup, hset]

variable [Fintype ι] [DecidableEq ι] [Fintype E.History]
variable [∀ who, DecidableEq (M.InfoState who)]
variable [∀ who info, Fintype (M.Choice who info)]

/-- Exact numerical counterfactual evaluation, derived from one-step execution,
reach factorization and complete history enumeration rather than assumed. -/
theorem counterfactualValue_eq_sum (clock : ObservationClock M)
    (payoff : ι → E.History → ℝ) (cert : TableCertificate M G clock payoff)
    (reachNumeric continueNumeric : Profile (tableSignature E.History M.InfoState M.Choice))
    (reachSemantic continueSemantic : Profile M.behavioralSignature)
    (hreach : Realizes M reachNumeric reachSemantic)
    (hcontinue : Realizes M continueNumeric continueSemantic)
    (who : ι) (info : M.InfoState who) (horizon : ℕ) :
    (G.counterfactualValue reachNumeric continueNumeric who info horizon : ℝ) =
      ∑ history : M.InformationHistory who info,
        M.counterfactualReachProbability reachSemantic who history.1.trace *
          (M.runBehavioralFrom continueSemantic (horizon - clock.depth who info)
            history.1).expect (payoff who) := by
  classical
  unfold HistoryTable.counterfactualValue
  rw [cast_map_sum, list_sum_eq_univ G.histories cert.histories_nodup cert.histories_complete]
  let f : E.History → ℝ := fun history =>
    M.counterfactualReachProbability reachSemantic who history.trace *
      (M.runBehavioralFrom continueSemantic (horizon - clock.depth who info)
        history).expect (payoff who)
  calc
    (∑ history, ((if G.info who history = info then
          G.counterfactualReach reachNumeric who history *
            G.value continueNumeric (horizon - G.depth who info) history who else 0 : ℚ) : ℝ)) =
        ∑ history, if M.infoOf who history.trace = info then f history else 0 := by
      apply Finset.sum_congr rfl
      intro history _
      rw [congrFun (congrFun cert.info_correct who) history, cert.depth_correct]
      by_cases h : M.infoOf who history.trace = info
      · rw [if_pos h, if_pos h, Rat.cast_mul,
          counterfactualReach_eq M G cert.path_correct cert.chance_correct
            reachNumeric reachSemantic hreach who history,
          value_eq_runBehavioralFrom M G cert.info_correct cert.terminal_correct
            cert.chance_rows payoff cert.payoff_correct continueNumeric continueSemantic
            hcontinue]
      · simp [h]
    _ = ∑' history : E.History,
          {history | M.infoOf who history.trace = info}.indicator f history := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro history _
      rfl
    _ = ∑' history : M.InformationHistory who info, f history.1 :=
      (tsum_subtype {history | M.infoOf who history.trace = info} f).symm
    _ = ∑ history : M.InformationHistory who info, f history.1 := tsum_fintype _

variable [∀ who info, DecidableEq (M.Choice who info)]

omit [Fintype ι] [Fintype E.History] [∀ who info, Fintype (M.Choice who info)] in
/-- A numerical information-local commitment realizes the exact canonical
behavioral commitment, including agreement at all other information states. -/
theorem commit_realizes
    (numeric : Profile (tableSignature E.History M.InfoState M.Choice))
    (semantic : Profile M.behavioralSignature) (hreal : Realizes M numeric semantic)
    (who : ι) (info : M.InfoState who) (choice : M.Choice who info) :
    Realizes M (HistoryTable.commit (H := E.History) numeric who info (pointMass choice))
      (Profile.update semantic who ((semantic who).commit info choice)) := by
  intro player observed action
  unfold HistoryTable.commit
  by_cases hp : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    by_cases hi : observed = info
    · subst observed
      rw [Profile.update_same, BehavioralPolicy.commit_self]
      exact cast_pointMass choice action
    · rw [Profile.update_of_ne _ _ hi, BehavioralPolicy.commit_of_ne _ _ _ hi]
      exact hreal who observed action
  · rw [Profile.update_of_ne _ _ hp, Profile.update_of_ne _ _ hp]
    exact hreal player observed action

/-- The full-game numeric action regret is the actual abstract CFR update.
Only primitive table correctness and representation of the current policy are
inputs; this supplies the missing evaluator-to-update refinement. -/
theorem instantaneousRegret_eq (clock : ObservationClock M)
    (payoff : ι → E.History → ℝ) (cert : TableCertificate M G clock payoff)
    (numeric : Profile (tableSignature E.History M.InfoState M.Choice))
    (semantic : Profile M.behavioralSignature) (hreal : Realizes M numeric semantic)
    (who : ι) (site : M.InformationSite who) (horizon : ℕ) (choice : M.Choice who site.1) :
    (G.instantaneousRegret numeric who site.1 horizon choice : ℝ) =
      M.counterfactualActionRegret semantic who site (payoff who)
        (horizon - clock.depth who site.1) choice := by
  unfold HistoryTable.instantaneousRegret
  rw [Rat.cast_sub,
    counterfactualValue_eq_sum M G clock payoff cert numeric _ semantic _ hreal
      (commit_realizes M numeric semantic hreal who site.1 choice),
    counterfactualValue_eq_sum M G clock payoff cert numeric numeric semantic semantic hreal hreal]
  unfold InformationModel.counterfactualActionRegret InformationModel.counterfactualRegret
    InformationModel.counterfactualContinuationValue InformationModel.behavioralContinuationValue
  rw [Profile.update_eq_self]

end GameTheory.ReBeL.Rational
