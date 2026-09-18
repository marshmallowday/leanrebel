/-
# Information-local chronological policy patches

Partial profiles replace only the focal player's laws at an explicit finite
set of information states. Actual own reach is determined by earlier decisions,
and a patch covering every decision before a cut realizes the full deviation.
-/

import GameTheory.Analysis.ReBeL.ChronologicalLocality

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- An information-local partial replacement, with no hidden-state argument. -/
def partialPolicy (who : ι) [DecidableEq (M.InfoState who)]
    (base target : M.BehavioralPolicy who) (done : Finset (M.InfoState who)) :
    M.BehavioralPolicy who :=
  fun info => if info ∈ done then target info else base info

/-- Replace just one player with the current information-local partial policy. -/
def partialProfile [DecidableEq ι] (strategy : Profile M.behavioralSignature)
    (who : ι) [DecidableEq (M.InfoState who)] (target : M.BehavioralPolicy who)
    (done : Finset (M.InfoState who)) : Profile M.behavioralSignature :=
  Profile.update strategy who (partialPolicy M who (strategy who) target done)

/-- The empty patch leaves the focal policy unchanged. -/
@[simp]
theorem partialPolicy_empty (who : ι) [DecidableEq (M.InfoState who)]
    (base target : M.BehavioralPolicy who) : partialPolicy M who base target ∅ = base := by
  funext info
  simp [partialPolicy]

/-- The empty patch leaves the complete profile unchanged. -/
@[simp]
theorem partialProfile_empty [DecidableEq ι] (strategy : Profile M.behavioralSignature)
    (who : ι) [DecidableEq (M.InfoState who)] (target : M.BehavioralPolicy who) :
    partialProfile M strategy who target ∅ = strategy := by
  simp [partialProfile]

/-- Inserting one information state is the existing local-law installation,
not a different update operation. Repeated insertion is harmless. -/
theorem partialPolicy_insert (who : ι) [DecidableEq (M.InfoState who)]
    (base target : M.BehavioralPolicy who) (done : Finset (M.InfoState who))
    (info : M.InfoState who) :
    partialPolicy M who base target (insert info done) =
      (partialPolicy M who base target done).withLaw info (target info) := by
  funext other
  by_cases hsame : other = info
  · subst other
    simp [partialPolicy]
  · rw [BehavioralPolicy.withLaw_of_ne _ _ _ hsame]
    simp [partialPolicy, hsame]

/-- Successive partial profiles differ by exactly one canonical unilateral
local-law replacement. -/
theorem partialProfile_insert [DecidableEq ι] (strategy : Profile M.behavioralSignature)
    (who : ι) [DecidableEq (M.InfoState who)] (target : M.BehavioralPolicy who)
    (done : Finset (M.InfoState who)) (info : M.InfoState who) :
    partialProfile M strategy who target (insert info done) =
      Profile.update (partialProfile M strategy who target done) who
        ((partialProfile M strategy who target done who).withLaw info (target info)) := by
  funext other
  by_cases hsame : other = who
  · subst other
    simp only [partialProfile, Profile.update_same]
    exact partialPolicy_insert M who (strategy who) target done info
  · simp [partialProfile, hsame]

/-- A partial policy agreeing with the target at every active nonterminal
decision before the horizon has exactly the target's outcome law. Inactive
menus are singletons; early terminal histories remain absorbed. -/
theorem run_partialProfile_eq_target [Fintype ι] [DecidableEq ι]
    (strategy : Profile M.behavioralSignature) (who : ι)
    [DecidableEq (M.InfoState who)] (target : M.BehavioralPolicy who)
    (done : Finset (M.InfoState who)) (horizon : ℕ)
    (hcover : ∀ history : E.History, history.trace.length < horizon →
      ¬ E.terminal history.state → E.active history.state who →
      M.infoOf who history.trace ∈ done) :
    M.runBehavioral (partialProfile M strategy who target done) horizon =
      M.runBehavioral (Profile.update strategy who target) horizon := by
  unfold InformationModel.runBehavioral
  apply M.runBehavioralFrom_congr_before
  intro later _hreach hterm hbefore other
  by_cases hsame : other = who
  · subst other
    by_cases hactive : E.active later.state who
    · have hmem := hcover later (by
        simpa only [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length,
          Nat.zero_add] using hbefore) hterm hactive
      simp [partialProfile, partialPolicy, hmem]
    · simp only [partialProfile, Profile.update_same]
      exact M.behavioral_eq_of_not_active _ _ later.trace hactive
  · simp [partialProfile, hsame]

/-- Own reach on an actual trace depends only on earlier active decisions.
No assumptions about the opponents, the current profile's positive support,
or a history's chance probability are needed. -/
theorem ownReach_eq_of_agree_before
    (first second : Profile M.behavioralSignature) (who : ι) (depth : ℕ)
    (hagree : ∀ history : E.History, history.trace.length < depth →
      ¬ E.terminal history.state → E.active history.state who →
      first who (M.infoOf who history.trace) = second who (M.infoOf who history.trace)) :
    ∀ {state : E.State} (trace : E.Trace state), trace.length ≤ depth →
      M.playerReachProbability first who trace = M.playerReachProbability second who trace := by
  intro state trace
  induction trace with
  | start => intro _; rfl
  | @extend source reached prior joint isLegal realized ih =>
    intro hbound
    have hprior : prior.length < depth := by
      simp only [ExecutionProtocol.Trace.length] at hbound
      omega
    have hlaw : first who (M.infoOf who prior) = second who (M.infoOf who prior) := by
      by_cases hactive : E.active source who
      · exact hagree ⟨source, prior⟩ hprior isLegal.1 hactive
      · exact M.behavioral_eq_of_not_active _ _ prior hactive
    rw [InformationModel.playerReachProbability, InformationModel.playerReachProbability,
      ih (Nat.le_of_lt hprior)]
    unfold InformationModel.playerStepProb
    rw [hlaw]

/-- Once all earlier decisions have been patched, the coefficient at the
current site is the fixed target policy's own reach, independent of the
original strategy. This is the coefficient needed across CFR iterations. -/
theorem partialProfile_ownReach_eq_target [DecidableEq ι]
    (clock : ObservationClock M) (strategy : Profile M.behavioralSignature) (who : ι)
    [DecidableEq (M.InfoState who)] (target : M.BehavioralPolicy who)
    (done : Finset (M.InfoState who)) (site : M.InformationSite who)
    (hcover : ∀ history : E.History, history.trace.length < clock.depth who site.1 →
      ¬ E.terminal history.state → E.active history.state who →
      M.infoOf who history.trace ∈ done) :
    M.playerReachProbability (partialProfile M strategy who target done) who
        site.2.choose.1.trace =
      M.playerReachProbability (Profile.update strategy who target) who
        site.2.choose.1.trace := by
  apply ownReach_eq_of_agree_before M _ _ who (clock.depth who site.1)
  · intro history hbefore hterm hactive
    simp [partialProfile, partialPolicy, hcover history hbefore hterm hactive]
  · exact le_of_eq (clock_commonDepth M clock who site site.2.choose)

/-- A chronological partial patch leaves all current pure counterfactual
regrets equal to those of the original profile. Equal-depth sites remain
separate; only the current information state must not have been patched yet. -/
theorem partialProfile_actionRegret [Fintype ι] [DecidableEq ι]
    (clock : ObservationClock M) (strategy : Profile M.behavioralSignature) (who : ι)
    [DecidableEq (M.InfoState who)] (target : M.BehavioralPolicy who)
    (done : Finset (M.InfoState who)) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (hnot : site.1 ∉ done)
    (hpast : ∀ info ∈ done, clock.depth who info ≤ clock.depth who site.1)
    (payoff : E.History → ℝ) (fuel : ℕ) (choice : M.Choice who site.1) :
    M.counterfactualActionRegret (partialProfile M strategy who target done)
        who site payoff fuel choice =
      M.counterfactualActionRegret strategy who site payoff fuel choice := by
  apply actionRegret_eq_of_clock_cut M clock _ strategy who
  · intro other hother
    simp [partialProfile, hother]
  · simp [partialProfile, partialPolicy, hnot]
  · intro info hafter
    have hmem : info ∉ done := by
      intro hin
      have hle := hpast info hin
      omega
    simp [partialProfile, partialPolicy, hmem]

end GameTheory.ReBeL
