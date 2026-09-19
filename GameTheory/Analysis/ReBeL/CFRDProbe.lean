/-
# Depth-limited backups and the canonical counterfactual update

A uniformly probed own prefix gives every legal decision a positive structural
reach. Backed-up root action scores may contain a common offset, but their
regret is exactly the canonical counterfactual regret. The computation stops
at the public depth cut; the full continuation appears only in the proof.
-/

import GameTheory.Analysis.ReBeL.DominatingReach
import GameTheory.Analysis.ReBeL.CFRDRegret

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [∀ who info, Fintype (M.Choice who info)]
variable [Fintype ι] [DecidableEq ι]

/-- Change only the focal player's decisions strictly before the selected
clock depth. The law at the current and all later sites remains unchanged. -/
def cfrDProbePolicy (clock : ObservationClock M) (base : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι) (depth : Nat) : M.BehavioralPolicy who :=
  fun info => if clock.depth who info < depth then uniformLegalPolicy M who (fallback who) info
    else base who info

/-- The probe is a legal unilateral profile, not hidden-state-dependent play. -/
def cfrDProbeProfile (clock : ObservationClock M) (base : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι) (depth : Nat) :
    Profile M.behavioralSignature :=
  Profile.update base who (cfrDProbePolicy M clock base fallback who depth)

/-- Strictly earlier probing does not change the counterfactual action regret
at the selected site, including histories of zero factual own reach. -/
theorem cfrDProbe_actionRegret (clock : ObservationClock M)
    (base : Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (who : ι) [DecidableEq (M.InfoState who)] (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : Nat) (choice : M.Choice who site.1) :
    M.counterfactualActionRegret
        (cfrDProbeProfile M clock base fallback who (clock.depth who site.1))
        who site payoff fuel choice =
      M.counterfactualActionRegret base who site payoff fuel choice := by
  apply actionRegret_eq_of_clock_cut M clock _ base who
  · intro other hother
    exact Profile.update_of_ne _ _ hother
  · simp only [cfrDProbeProfile, Profile.update_same, cfrDProbePolicy, lt_self_iff_false,
      if_false]
  · intro info later
    simp only [cfrDProbeProfile, Profile.update_same, cfrDProbePolicy,
      if_neg (not_lt.mpr (le_of_lt later))]

omit [Fintype ι] in
/-- The probe's reach at the selected site is independent of the current
iterate and equals the positive product of uniform legal menu probabilities. -/
theorem cfrDProbe_reach (clock : ObservationClock M)
    (base : Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (who : ι) (site : M.InformationSite who) :
    M.playerReachProbability
        (cfrDProbeProfile M clock base fallback who (clock.depth who site.1))
        who site.2.choose.1.trace =
      M.playerReachProbability (uniformLegalProfile M fallback) who site.2.choose.1.trace := by
  apply ownReach_eq_of_agree_before M _ _ who (clock.depth who site.1)
  · intro history before _ _
    have hdepth : clock.depth who (M.infoOf who history.trace) < clock.depth who site.1 := by
      rw [clock.correct]
      exact before
    simp only [cfrDProbeProfile, Profile.update_same, cfrDProbePolicy, if_pos hdepth,
      uniformLegalProfile]
  · exact le_of_eq (clock_commonDepth M clock who site site.2.choose)

omit [∀ who info, Fintype (M.Choice who info)] in
/-- A unilateral policy already equal to the base after a depth cut has that
base continuation law. Early terminal histories are absorbed, not evaluated
with a fictitious cut oracle. -/
theorem run_unilateral_bind_at_cut (clock : ObservationClock M)
    (base : Profile M.behavioralSignature) (who : ι) (policy : M.BehavioralPolicy who)
    (cut remaining : Nat)
    (future : ∀ info, cut ≤ clock.depth who info → policy info = base who info) :
    M.runBehavioral (Profile.update base who policy) (cut + remaining) =
      (M.runBehavioral (Profile.update base who policy) cut).bind
        (M.runBehavioralFrom base remaining) := by
  rw [show M.runBehavioral (Profile.update base who policy) (cut + remaining) =
      (M.runBehavioral (Profile.update base who policy) cut).bind
        (M.runBehavioralFrom (Profile.update base who policy) remaining) from
    M.runBehavioralFrom_add _ _ _ _]
  apply FinDist.bind_congr
  intro history reached
  by_cases terminal : E.terminal history.state
  · rw [M.runBehavioralFrom_of_terminal _ _ terminal,
      M.runBehavioralFrom_of_terminal _ _ terminal]
  · have depth : history.trace.length = cut := by
      rcases M.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
        (Profile.update base who policy) cut E.initHistory history reached with ht | hd
      · exact False.elim (terminal ht)
      · simpa only [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length,
          Nat.zero_add] using hd
    apply M.runBehavioralFrom_congr
    intro later reachable _ other
    by_cases same : other = who
    · subst other
      rw [Profile.update_same]
      apply future
      rw [clock.correct, ← depth]
      exact reachable.trace_length_le
    · exact congrFun (Profile.update_of_ne base policy same) _

omit [Fintype ι] [DecidableEq ι] in
/-- All pure commitments at the probed site have the same actual continuation
after the public cut, and thus use one information-value vector. -/
theorem cfrDProbe_commit_future (clock : ObservationClock M)
    (base : Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (who : ι) [DecidableEq (M.InfoState who)] (site : M.InformationSite who)
    (choice : M.Choice who site.1) (cut : Nat) (searched : clock.depth who site.1 < cut)
    (info : M.InfoState who) (after : cut ≤ clock.depth who info) :
    (cfrDProbePolicy M clock base fallback who (clock.depth who site.1)).commit
        site.1 choice info = base who info := by
  have distinct : info ≠ site.1 := by intro same; rw [same] at after; omega
  rw [BehavioralPolicy.commit_of_ne _ _ _ distinct]
  have not_before : ¬ clock.depth who info < clock.depth who site.1 := by omega
  rw [cfrDProbePolicy, if_neg not_before]

/-- The full payoff used only in the proof of a single backed-up action. -/
def cfrDProbeFullScore (clock : ObservationClock M) (base : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who) (payoff : E.History → ℝ) (horizon : Nat)
    (choice : M.Choice who site.1) : ℝ :=
  (M.runBehavioral (Profile.update base who
    ((cfrDProbePolicy M clock base fallback who (clock.depth who site.1)).commit site.1 choice))
      horizon).expect payoff /
    M.playerReachProbability (uniformLegalProfile M fallback) who site.2.choose.1.trace

/-- The numerical action score uses only the stopped prefix and one vector.
There is no invocation of a full-game rollout in the numerical update. -/
def cfrDProbeScore (clock : ObservationClock M) (base : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who) (cut : Nat) (prediction : M.InfoState who → ℝ)
    (choice : M.Choice who site.1) : ℝ :=
  ((M.runBehavioral (Profile.update base who
    ((cfrDProbePolicy M clock base fallback who (clock.depth who site.1)).commit site.1 choice))
      cut).map (fun history => M.infoOf who history.trace)).expect prediction /
    M.playerReachProbability (uniformLegalProfile M fallback) who site.2.choose.1.trace

omit [∀ who info, Fintype (M.Choice who info)] in
/-- The canonical counterfactual regret averages to zero under the law used
at that same information state. This is an exact affine identity. -/
theorem counterfactual_actionRegret_mean_zero (hrecall : M.PerfectRecall)
    (base : Profile M.behavioralSignature) (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who) [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) (fuel : Nat) :
    (base who site.1).expect (M.counterfactualActionRegret base who site payoff fuel) = 0 := by
  have identity : M.counterfactualActionRegret base who site payoff fuel =
      fun choice => M.counterfactualActionUtility base who site payoff fuel choice -
        (base who site.1).expect (M.counterfactualActionUtility base who site payoff fuel) :=
    funext fun choice => actionRegret_eq_sub_expect M
      (M.actsOnceWhereItMatters_of_perfectRecall hrecall) base who site payoff fuel choice
  rw [identity, FinDist.expect_sub, FinDist.expect_const, sub_self]

/-- The probed full-game score differs from the canonical counterfactual
regret by a single action-independent offset. -/
theorem cfrDProbeFullScore_offset (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (base : Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (who : ι) [DecidableEq (M.InfoState who)] (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)] (payoff : E.History → ℝ) (horizon : Nat)
    (before : clock.depth who site.1 ≤ horizon) (choice : M.Choice who site.1) :
    cfrDProbeFullScore M clock base fallback who site payoff horizon choice -
        (M.runBehavioral
          (cfrDProbeProfile M clock base fallback who (clock.depth who site.1)) horizon).expect
          payoff / M.playerReachProbability (uniformLegalProfile M fallback)
            who site.2.choose.1.trace =
      M.counterfactualActionRegret base who site payoff
        (horizon - clock.depth who site.1) choice := by
  have root := root_withLaw_eq_reach_mul_expect M clock hrecall
    (cfrDProbeProfile M clock base fallback who (clock.depth who site.1)) who site
    (FinDist.pure choice) payoff horizon before
  rw [FinDist.expect_pure, cfrDProbe_reach, cfrDProbe_actionRegret] at root
  unfold cfrDProbeFullScore
  rw [← sub_div]
  apply (div_eq_iff (ne_of_gt (uniformOwnReach_positive M fallback who
    site.2.choose.1.trace))).mpr
  simpa only [cfrDProbeProfile, Profile.update_same, Profile.update_idem,
    BehavioralPolicy.withLaw, BehavioralPolicy.commit, mul_comm] using root

/-- Consequently the backed-up full-game scores induce exactly the canonical
CFR regrets. The offset is canceled by the actual current local law, not an
arithmetic mean of past policies. -/
theorem cfrDProbeFullScore_regret (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (base : Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (who : ι) [DecidableEq (M.InfoState who)] (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)] (payoff : E.History → ℝ) (horizon : Nat)
    (before : clock.depth who site.1 ≤ horizon) (choice : M.Choice who site.1) :
    cfrDProbeFullScore M clock base fallback who site payoff horizon choice -
        (base who site.1).expect
          (cfrDProbeFullScore M clock base fallback who site payoff horizon) =
      M.counterfactualActionRegret base who site payoff
        (horizon - clock.depth who site.1) choice := by
  let offset := (M.runBehavioral
    (cfrDProbeProfile M clock base fallback who (clock.depth who site.1)) horizon).expect payoff /
      M.playerReachProbability (uniformLegalProfile M fallback) who site.2.choose.1.trace
  have point (action : M.Choice who site.1) :
      cfrDProbeFullScore M clock base fallback who site payoff horizon action =
        M.counterfactualActionRegret base who site payoff
          (horizon - clock.depth who site.1) action + offset :=
    (sub_eq_iff_eq_add).mp
      (cfrDProbeFullScore_offset M clock hrecall base fallback who site payoff horizon
        before action)
  have identity : cfrDProbeFullScore M clock base fallback who site payoff horizon =
      fun action => M.counterfactualActionRegret base who site payoff
        (horizon - clock.depth who site.1) action + offset := funext point
  rw [point, identity, FinDist.expect_add, FinDist.expect_const,
    counterfactual_actionRegret_mean_zero M hrecall, zero_add, add_sub_cancel_right]

/-- One delta-accurate reference vector, coupled to the actual continuation,
controls every probed action score by delta divided by positive uniform reach.
Only the depth-limited prefix is evaluated by the numerical score. -/
theorem cfrDProbeScore_error (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (base : Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (who : ι) [DecidableEq (M.InfoState who)] (site : M.InformationSite who)
    (payoff : E.History → ℝ) (cut remaining : Nat) (searched : clock.depth who site.1 < cut)
    (prediction : M.InfoState who → ℝ) (error : ℝ)
    (accurate : ∀ info ∈ ((unilateralReferenceLaw M base fallback who cut).map
        (fun history => M.infoOf who history.trace)).support,
      |prediction info - conditionalOracleValue (unilateralReferenceLaw M base fallback who cut)
        (fun history => M.infoOf who history.trace)
        (fun history => (M.runBehavioralFrom base remaining history).expect payoff) info| ≤ error)
    (choice : M.Choice who site.1) :
    |cfrDProbeScore M clock base fallback who site cut prediction choice -
        cfrDProbeFullScore M clock base fallback who site payoff (cut + remaining) choice| ≤
      error / M.playerReachProbability (uniformLegalProfile M fallback)
        who site.2.choose.1.trace := by
  let policy := (cfrDProbePolicy M clock base fallback who
    (clock.depth who site.1)).commit site.1 choice
  have estimate := unilateralReference_oracle_error M hrecall base fallback who cut
    (fun history => (M.runBehavioralFrom base remaining history).expect payoff)
    prediction error accurate policy
  have split := run_unilateral_bind_at_cut M clock base who policy cut remaining
    (cfrDProbe_commit_future M clock base fallback who site choice cut searched)
  have full : (M.runBehavioral (Profile.update base who policy) (cut + remaining)).expect payoff =
      (M.runBehavioral (Profile.update base who policy) cut).expect
        (fun history => (M.runBehavioralFrom base remaining history).expect payoff) := by
    rw [split, FinDist.expect_bind]
  rw [← full] at estimate
  unfold cfrDProbeScore cfrDProbeFullScore
  rw [← sub_div, abs_div, abs_of_pos (uniformOwnReach_positive M fallback who _)]
  exact div_le_div_of_nonneg_right estimate (le_of_lt (uniformOwnReach_positive M fallback who _))

end GameTheory.ReBeL
