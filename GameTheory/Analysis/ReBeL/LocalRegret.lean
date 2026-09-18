/-
# Counterfactual updates at every finite-horizon decision site

The canonical information fiber may contain terminal histories. These histories
contribute a constant continuation value, not a new decision and not a missing
branch. The affine identity therefore holds for every horizon, including zero,
without the older `AllNonterminal` premise. All execution and reach operations
are the existing Protocol operations.
-/

import GameTheory.Analysis.Protocol.CounterfactualRegretMatching

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι]

/-- Installing a local law is affine even when the selected history has
already terminated or the requested continuation has zero fuel. -/
theorem continuation_withLaw_eq_expect
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : Profile M.behavioralSignature)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who) (policy : M.BehavioralPolicy who)
    (law : FinDist (M.Choice who site.1))
    (history : M.InformationHistory who site.1)
    (payoff : E.History → ℝ) (fuel : ℕ) :
    M.behavioralContinuationValue strategy who (policy.withLaw site.1 law)
        payoff fuel history.1 =
      law.expect fun choice => M.behavioralContinuationValue strategy who
        (policy.commit site.1 choice) payoff fuel history.1 := by
  cases fuel with
  | zero =>
      simp [InformationModel.behavioralContinuationValue,
        InformationModel.runBehavioralFrom]
  | succ fuel =>
      by_cases hterm : E.terminal history.1.state
      · simp [InformationModel.behavioralContinuationValue,
          M.runBehavioralFrom_of_terminal _ _ hterm]
      · exact M.behavioralContinuationValue_withLaw_eq_expect hactsOnce
          strategy who site policy law history hterm payoff fuel

/-- Summing the terminal-tolerant affine identity uses the original
counterfactual reach, including zero-reach histories, without normalization. -/
theorem counterfactual_withLaw_eq_expect
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : Profile M.behavioralSignature)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (policy : M.BehavioralPolicy who)
    (law : FinDist (M.Choice who site.1))
    (payoff : E.History → ℝ) (fuel : ℕ) :
    M.counterfactualContinuationValue strategy who site
        (policy.withLaw site.1 law) payoff fuel =
      law.expect fun choice => M.counterfactualContinuationValue strategy who site
        (policy.commit site.1 choice) payoff fuel := by
  unfold InformationModel.counterfactualContinuationValue
  simp_rw [continuation_withLaw_eq_expect M hactsOnce strategy who site
    policy law _ payoff fuel, ← FinDist.expect_smul]
  exact FinDist.expect_sum_comm law
    (fun (history : M.InformationHistory who site.1) choice =>
      M.counterfactualReachProbability strategy who history.1.trace *
        M.behavioralContinuationValue strategy who (policy.commit site.1 choice)
          payoff fuel history.1)

/-- The current continuation utility is the expectation of all pure local
commitments, at any horizon and without deleting absorbed histories. -/
theorem counterfactual_eq_expect_actionUtility
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : Profile M.behavioralSignature)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ) :
    M.counterfactualContinuationValue strategy who site (strategy who) payoff fuel =
      (strategy who site.1).expect
        (M.counterfactualActionUtility strategy who site payoff fuel) := by
  have h := counterfactual_withLaw_eq_expect M hactsOnce strategy who site
    (strategy who) (strategy who site.1) payoff fuel
  rw [BehavioralPolicy.withLaw_eq_self] at h
  exact h

/-- Each actual local CFR update is an ordinary finite-action external-regret
update. This realization identity covers both zero fuel and terminal fibers. -/
theorem actionRegret_eq_sub_expect
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : Profile M.behavioralSignature)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ)
    (choice : M.Choice who site.1) :
    M.counterfactualActionRegret strategy who site payoff fuel choice =
      M.counterfactualActionUtility strategy who site payoff fuel choice -
        (strategy who site.1).expect
          (M.counterfactualActionUtility strategy who site payoff fuel) := by
  unfold InformationModel.counterfactualActionRegret InformationModel.counterfactualRegret
  rw [counterfactual_eq_expect_actionUtility M hactsOnce strategy who site payoff fuel]
  rfl

/-- The complete local update vector realizes ordinary regret matching at
any finite cut. The environment supplies a profile, not a regret certificate. -/
theorem localVector_eq_regretPayoff
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : Profile M.behavioralSignature)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ) :
    M.localCounterfactualRegretVector strategy who site payoff fuel =
      GameTheory.Analysis.Approachability.regretPayoff
        (fun choice (_environment : Unit) =>
          M.counterfactualActionUtility strategy who site payoff fuel choice)
        (strategy who site.1) () := by
  ext choice
  rw [GameTheory.Analysis.Approachability.regretPayoff_ofLp]
  exact actionRegret_eq_sub_expect M hactsOnce strategy who site payoff fuel choice

/-- The realization equation is valid for every local law installed in
any environment profile, including zero fuel and terminal fiber members. -/
theorem localVector_withLaw_eq_regretPayoff
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : Profile M.behavioralSignature)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (law : FinDist (M.Choice who site.1))
    (payoff : E.History → ℝ) (fuel : ℕ) :
    M.localCounterfactualRegretVector (M.strategyWithLocalLaw strategy who site law)
        who site payoff fuel =
      GameTheory.Analysis.Approachability.regretPayoff
        (fun choice (_environment : Unit) =>
          M.counterfactualActionUtility strategy who site payoff fuel choice) law () := by
  ext choice
  rw [InformationModel.localCounterfactualRegretVector,
    GameTheory.Analysis.Approachability.regretPayoff_ofLp, WithLp.ofLp_toLp]
  rw [actionRegret_eq_sub_expect M hactsOnce
    (M.strategyWithLocalLaw strategy who site law) who site payoff fuel,
    InformationModel.strategyWithLocalLaw_same,
    InformationModel.counterfactualActionUtility_strategyWithLocalLaw]
  congr 1
  apply FinDist.expect_congr
  intro current _
  exact M.counterfactualActionUtility_strategyWithLocalLaw strategy who site law payoff fuel current

end GameTheory.ReBeL
