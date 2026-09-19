/-
# Separating trunk deviations from continuation deviations

A unilateral target is first installed only before the public depth cut.
This partial deviation has zero counterfactual contribution after the cut.
Its remaining difference from the full target is the actual conditional
continuation gain, not an assumed root-regret decomposition or certificate.
-/

import GameTheory.Analysis.ReBeL.CFRDCutDriver

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Install the target only before the cut, retaining the original continuation. -/
def cfrDPrefixPolicy (clock : ObservationClock M)
    (base : Profile M.behavioralSignature) (who : ι) (target : M.BehavioralPolicy who)
    (cut : Nat) : M.BehavioralPolicy who :=
  fun info => if clock.depth who info < cut then target info else base who info

/-- The prefix replacement is the target at every searched information state. -/
theorem cfrDPrefixPolicy_before (clock : ObservationClock M)
    (base : Profile M.behavioralSignature) (who : ι) (target : M.BehavioralPolicy who)
    (cut : Nat) (info : M.InfoState who) (before : clock.depth who info < cut) :
    cfrDPrefixPolicy M clock base who target cut info = target info := if_pos before

/-- Outside the trunk this replacement keeps the original legal continuation. -/
theorem cfrDPrefixPolicy_after (clock : ObservationClock M)
    (base : Profile M.behavioralSignature) (who : ι) (target : M.BehavioralPolicy who)
    (cut : Nat) (info : M.InfoState who) (after : ¬ clock.depth who info < cut) :
    cfrDPrefixPolicy M clock base who target cut info = base who info := if_neg after

variable [DecidableEq ι]

/-- Earlier own reach agrees with the fixed target even on zero factual
branches. No bound on the current strategy's reach is imposed. -/
theorem cfrDPrefixPolicy_reach (clock : ObservationClock M)
    (base : Profile M.behavioralSignature) (who : ι) (target : M.BehavioralPolicy who)
    (cut : Nat) (site : M.InformationSite who) (before : clock.depth who site.1 < cut) :
    M.playerReachProbability
        (Profile.update base who (cfrDPrefixPolicy M clock base who target cut))
        who site.2.choose.1.trace =
      M.playerReachProbability (Profile.update base who target) who site.2.choose.1.trace := by
  apply ownReach_eq_of_agree_before M _ _ who (clock.depth who site.1)
  · intro history earlier _ _
    rw [Profile.update_same, Profile.update_same]
    apply cfrDPrefixPolicy_before
    rw [clock.correct]
    exact lt_trans earlier before
  · exact le_of_eq (clock_commonDepth M clock who site site.2.choose)

variable [Fintype ι]

/-- The actual stopped history laws agree; this is stronger than agreement
of rewards and does not condition away early terminal histories. -/
theorem cfrDPrefix_run_cut (clock : ObservationClock M)
    (base : Profile M.behavioralSignature) (who : ι) (target : M.BehavioralPolicy who)
    (cut : Nat) :
    M.runBehavioral (Profile.update base who (cfrDPrefixPolicy M clock base who target cut)) cut =
      M.runBehavioral (Profile.update base who target) cut := by
  unfold InformationModel.runBehavioral
  apply M.runBehavioralFrom_congr_before
  intro history _ _ before other
  by_cases same : other = who
  · subst other
    rw [Profile.update_same, Profile.update_same]
    apply cfrDPrefixPolicy_before
    rw [clock.correct]
    simpa only [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length,
      Nat.zero_add] using before
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]

/-- The prefix target uses exactly the original continuation after its cut. -/
theorem cfrDPrefix_run_bind (clock : ObservationClock M)
    (base : Profile M.behavioralSignature) (who : ι) (target : M.BehavioralPolicy who)
    (cut remaining : Nat) :
    M.runBehavioral (Profile.update base who (cfrDPrefixPolicy M clock base who target cut))
        (cut + remaining) =
      (M.runBehavioral (Profile.update base who target) cut).bind
        (M.runBehavioralFrom base remaining) := by
  rw [run_unilateral_bind_at_cut M clock base who
    (cfrDPrefixPolicy M clock base who target cut) cut remaining (by
      intro info after
      exact cfrDPrefixPolicy_after M clock base who target cut info (not_lt.mpr after)),
    cfrDPrefix_run_cut M clock base who target cut]

/-- Exact continuation-gain identity for the actual stopped law. A later
oracle contract can bound its conditional values; the identity itself has
no approximation, optimality, or positive-current-reach premise. -/
theorem cfrDPrefix_tail_gain (clock : ObservationClock M)
    (base : Profile M.behavioralSignature) (who : ι) (target : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) (cut remaining : Nat) :
    (M.runBehavioral (Profile.update base who target) (cut + remaining)).expect payoff -
        (M.runBehavioral (Profile.update base who
          (cfrDPrefixPolicy M clock base who target cut)) (cut + remaining)).expect payoff =
      (M.runBehavioral (Profile.update base who target) cut).expect (fun history =>
        (M.runBehavioralFrom (Profile.update base who target) remaining history).expect payoff -
          (M.runBehavioralFrom base remaining history).expect payoff) := by
  have full : M.runBehavioral (Profile.update base who target) (cut + remaining) =
      (M.runBehavioral (Profile.update base who target) cut).bind
        (M.runBehavioralFrom (Profile.update base who target) remaining) :=
    M.runBehavioralFrom_add _ _ _ _
  rw [full, cfrDPrefix_run_bind, FinDist.expect_bind, FinDist.expect_bind, FinDist.expect_sub]

variable [Fintype E.History]

/-- Only searched sites contribute to a prefix deviation. Contributions use
the fixed target's own-reach coefficient and the original full-play regret. -/
theorem cfrDPrefix_targetRegretTerm (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (base : Profile M.behavioralSignature) (who : ι) [DecidableEq (M.InfoState who)]
    (target : M.BehavioralPolicy who) (payoff : E.History → ℝ) (cut horizon : Nat)
    (site : M.InformationSite who) :
    targetRegretTerm M clock base who (cfrDPrefixPolicy M clock base who target cut)
        payoff horizon site =
      if clock.depth who site.1 < cut then
        targetRegretTerm M clock base who target payoff horizon site else 0 := by
  by_cases before : clock.depth who site.1 < cut
  · rw [if_pos before]
    unfold targetRegretTerm
    rw [cfrDPrefixPolicy_before M clock base who target cut site.1 before,
      cfrDPrefixPolicy_reach M clock base who target cut site before]
  · rw [if_neg before]
    unfold targetRegretTerm
    rw [cfrDPrefixPolicy_after M clock base who target cut site.1 before,
      counterfactual_actionRegret_mean_zero M hrecall, mul_zero]

/-- The complete canonical scheduler gives the trunk-only decomposition,
including sites not visited by current play. Its tail terms vanish by their
current-law zero-mean identity, not by assuming off-trunk local optimality. -/
theorem cfrDPrefix_root_gain (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (base : Profile M.behavioralSignature) (who : ι) [DecidableEq (M.InfoState who)]
    (target : M.BehavioralPolicy who) (payoff : E.History → ℝ) (cut horizon : Nat) :
    (M.runBehavioral (Profile.update base who
        (cfrDPrefixPolicy M clock base who target cut)) horizon).expect payoff -
        (M.runBehavioral base horizon).expect payoff =
      ((scheduledSites M clock horizon who).map fun site =>
        if clock.depth who site.1 < cut then
          targetRegretTerm M clock base who target payoff horizon site else 0).sum := by
  rw [scheduled_root_gain M clock hrecall]
  congr 1
  apply List.map_congr_left
  intro site _
  exact cfrDPrefix_targetRegretTerm M clock hrecall base who target payoff cut horizon site

end GameTheory.ReBeL
