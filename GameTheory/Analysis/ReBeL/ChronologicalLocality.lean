/-
# Chronological locality for the full-game CFR decomposition

A continuation consults its current information and strictly later depths.
It cannot consult a different information state at the same depth. These
facts justify chronological unilateral replacements without discarding ties,
zero-reach branches, or terminal members of an information fiber.
-/

import GameTheory.Analysis.Protocol.CounterfactualDecomposition
import GameTheory.Analysis.ReBeL.LocalRegret
import GameTheory.ReBeL.Schedule

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- The information-local clock supplies the common-depth premise of the
canonical root-gain theorem, including every member of the history fiber. -/
theorem clock_commonDepth (clock : ObservationClock M) (who : ι)
    (site : M.InformationSite who) :
    InformationSite.CommonDepth M site (clock.depth who site.1) := by
  intro history
  have h := clock.correct who history.1
  rw [history.2] at h
  exact h.symm

/-- Agreement at the current information state and at strictly later depths
is sufficient for continuation-law equality. Distinct equal-depth sites are
not artificially ordered as if one could be reached after the other. -/
theorem runFrom_eq_of_clock_cut [Fintype ι]
    (clock : ObservationClock M)
    (first second : Profile M.behavioralSignature) (who : ι)
    (hothers : ∀ other, other ≠ who → first other = second other)
    (history : E.History)
    (hhere : first who (M.infoOf who history.trace) =
      second who (M.infoOf who history.trace))
    (hfuture : ∀ info, history.trace.length < clock.depth who info →
      first who info = second who info)
    (fuel : ℕ) :
    M.runBehavioralFrom first fuel history =
      M.runBehavioralFrom second fuel history := by
  apply M.runBehavioralFrom_congr
  intro later hreach _hterm player
  by_cases hplayer : player = who
  · subst player
    by_cases hequal : later.trace.length = history.trace.length
    · have hh : later = history := hreach.eq_of_trace_length_eq (by omega)
      subst later
      exact hhere
    · apply hfuture
      rw [clock.correct]
      have hle := hreach.trace_length_le
      omega
  · exact congrFun (hothers player hplayer) (M.infoOf player later.trace)

/-- Counterfactual continuation values ignore changes to the focal player's
past and to different same-depth sites. Opponents and chance retain their
original factors; the focal policies may be arbitrary behavioral laws. -/
theorem counterfactualValue_eq_of_clock_cut [Fintype ι] [DecidableEq ι]
    (clock : ObservationClock M)
    (first second : Profile M.behavioralSignature) (who : ι)
    (hothers : ∀ other, other ≠ who → first other = second other)
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (firstPolicy secondPolicy : M.BehavioralPolicy who)
    (hhere : firstPolicy site.1 = secondPolicy site.1)
    (hfuture : ∀ info, clock.depth who site.1 < clock.depth who info →
      firstPolicy info = secondPolicy info)
    (payoff : E.History → ℝ) (fuel : ℕ) :
    M.counterfactualContinuationValue first who site firstPolicy payoff fuel =
      M.counterfactualContinuationValue second who site secondPolicy payoff fuel := by
  unfold InformationModel.counterfactualContinuationValue
  apply Finset.sum_congr rfl
  intro history _
  rw [M.counterfactualReachProbability_eq_of_eq_off hothers history.1.trace]
  apply congrArg
    (fun value : ℝ => M.counterfactualReachProbability second who history.1.trace * value)
  unfold InformationModel.behavioralContinuationValue
  apply congrArg (fun law : FinDist E.History => law.expect payoff)
  apply runFrom_eq_of_clock_cut M clock _ _ who
  · intro other hne
    rw [Profile.update_of_ne _ _ hne, Profile.update_of_ne _ _ hne]
    exact hothers other hne
  · simpa only [Profile.update_same, history.2] using hhere
  · intro info hafter
    rw [Profile.update_same, Profile.update_same]
    apply hfuture info
    rw [← clock_commonDepth M clock who site history]
    exact hafter

/-- Every pure local regret is unchanged by modifications confined to the
past and to other information states at the same depth. -/
theorem actionRegret_eq_of_clock_cut [Fintype ι] [DecidableEq ι]
    (clock : ObservationClock M)
    (first second : Profile M.behavioralSignature) (who : ι)
    [DecidableEq (M.InfoState who)]
    (hothers : ∀ other, other ≠ who → first other = second other)
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hhere : first who site.1 = second who site.1)
    (hfuture : ∀ info, clock.depth who site.1 < clock.depth who info →
      first who info = second who info)
    (payoff : E.History → ℝ) (fuel : ℕ) (choice : M.Choice who site.1) :
    M.counterfactualActionRegret first who site payoff fuel choice =
      M.counterfactualActionRegret second who site payoff fuel choice := by
  have hcommitted := counterfactualValue_eq_of_clock_cut M clock first second who
    hothers site ((first who).commit site.1 choice) ((second who).commit site.1 choice)
    (by rw [BehavioralPolicy.commit_self, BehavioralPolicy.commit_self])
    (fun info hafter => by
      have hne : info ≠ site.1 := by
        intro heq
        rw [heq] at hafter
        exact (lt_irrefl _ hafter)
      rw [BehavioralPolicy.commit_of_ne _ _ _ hne,
        BehavioralPolicy.commit_of_ne _ _ _ hne]
      exact hfuture info hafter) payoff fuel
  unfold InformationModel.counterfactualActionRegret InformationModel.counterfactualRegret
  rw [hcommitted, counterfactualValue_eq_of_clock_cut M clock first second who
    hothers site (first who) (second who) hhere hfuture payoff fuel]

/-- Installing a law at an earlier or distinct equal-depth site cannot alter
the counterfactual action regret at the current site. The strict inequality
used in an older local theorem is not needed for distinct same-depth sites. -/
theorem actionRegret_withLaw_at_earlier_or_other [Fintype ι] [DecidableEq ι]
    (clock : ObservationClock M) (strategy : Profile M.behavioralSignature)
    (who : ι) [DecidableEq (M.InfoState who)]
    (changed site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hdepth : clock.depth who changed.1 ≤ clock.depth who site.1)
    (hne : site.1 ≠ changed.1) (law : FinDist (M.Choice who changed.1))
    (payoff : E.History → ℝ) (fuel : ℕ) (choice : M.Choice who site.1) :
    M.counterfactualActionRegret
        (Profile.update strategy who ((strategy who).withLaw changed.1 law))
        who site payoff fuel choice =
      M.counterfactualActionRegret strategy who site payoff fuel choice := by
  apply actionRegret_eq_of_clock_cut M clock _ strategy who
  · intro other hother
    exact Profile.update_of_ne _ _ hother
  · rw [Profile.update_same, BehavioralPolicy.withLaw_of_ne _ _ _ hne]
  · intro info hafter
    have hinfo : info ≠ changed.1 := by
      intro heq
      rw [heq] at hafter
      omega
    rw [Profile.update_same, BehavioralPolicy.withLaw_of_ne _ _ _ hinfo]

/-- Local-law regret is exactly the law's expectation of the canonical pure
local regrets. Zero fuel, nonpositive regrets and absorbed histories need no
exception to this identity. -/
theorem withLaw_regret_eq_expect [Fintype ι] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : Profile M.behavioralSignature) (who : ι)
    [DecidableEq (M.InfoState who)] (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (law : FinDist (M.Choice who site.1)) (payoff : E.History → ℝ) (fuel : ℕ) :
    M.counterfactualRegret strategy who site payoff fuel
        ((strategy who).withLaw site.1 law) =
      law.expect (M.counterfactualActionRegret strategy who site payoff fuel) := by
  unfold InformationModel.counterfactualRegret
  rw [counterfactual_withLaw_eq_expect M hactsOnce strategy who site
    (strategy who) law payoff fuel]
  simp only [InformationModel.counterfactualActionRegret,
    InformationModel.counterfactualRegret, FinDist.expect_sub, FinDist.expect_const]

/-- The clock and perfect recall discharge the premises of the exact
single-site root decomposition for an arbitrary replacement law. This is an
identity of actual canonical executions, not an assumed root-gain certificate. -/
theorem root_withLaw_eq_reach_mul_expect [Fintype ι] [DecidableEq ι]
    (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (strategy : Profile M.behavioralSignature) (who : ι)
    [DecidableEq (M.InfoState who)] (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (law : FinDist (M.Choice who site.1)) (payoff : E.History → ℝ) (horizon : ℕ)
    (hbefore : clock.depth who site.1 ≤ horizon) :
    (M.runBehavioral
        (Profile.update strategy who ((strategy who).withLaw site.1 law)) horizon).expect
        payoff - (M.runBehavioral strategy horizon).expect payoff =
      M.playerReachProbability strategy who site.2.choose.1.trace *
        law.expect (M.counterfactualActionRegret strategy who site payoff
          (horizon - clock.depth who site.1)) := by
  have h := M.rootGain_eq_representativeReach_mul_counterfactualRegret_of_perfectRecall
    hrecall strategy who site ((strategy who).withLaw site.1 law)
    (clock.depth who site.1) (horizon - clock.depth who site.1)
    (clock_commonDepth M clock who site)
    (fun hne => BehavioralPolicy.withLaw_of_ne (strategy who) site.1 law hne) payoff
  rw [Nat.add_sub_of_le hbefore] at h
  rw [withLaw_regret_eq_expect M (M.actsOnceWhereItMatters_of_perfectRecall hrecall)] at h
  exact h

end GameTheory.ReBeL
