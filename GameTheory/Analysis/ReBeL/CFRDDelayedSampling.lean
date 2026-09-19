/-
# Delaying a child solver's private draw until the public cut

All child profiles share the searched prefix. Sampling their private index
at the cut has exactly the outcome law of the own-reach averaged child
profile, against every fixed unknown opponent. The proof compares laws,
not values of arbitrary equilibrium replacements. No Nash, local no-loss,
or positive factual reach assumption is used.
-/

import GameTheory.Analysis.ReBeL.CFRDPrefix
import GameTheory.Analysis.ReBeL.UnilateralAverage

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι]

/-- Agreement strictly before the clock cut preserves the entire stopped
unilateral law, including early terminals and zero-probability branches. -/
theorem cfrD_run_cut_congr (clock : ObservationClock M)
    (unknown : Profile M.behavioralSignature) (who : ι)
    (first second : M.BehavioralPolicy who) (cut : Nat)
    (agree : ∀ info, clock.depth who info < cut → first info = second info) :
    M.runBehavioral (Profile.update unknown who first) cut =
      M.runBehavioral (Profile.update unknown who second) cut := by
  unfold InformationModel.runBehavioral
  apply M.runBehavioralFrom_congr_before
  intro history _ _ before other
  by_cases same : other = who
  · subst other
    rw [Profile.update_same, Profile.update_same]
    apply agree
    rw [clock.correct]
    simpa only [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length,
      Nat.zero_add] using before
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]

variable {K : Type*} [Fintype K]

/-- An independent child index may be drawn after the common prefix. The
fixed unknown opponent remains outside the draw; this is not shared-seed play. -/
theorem cfrD_delayed_private_sampling (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (seed : FinDist K)
    (plays : K → Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (prefix unknown : Profile M.behavioralSignature) (who : ι) (cut remaining : Nat)
    (agree : ∀ k ∈ seed.support, ∀ info, clock.depth who info < cut →
      plays k who info = prefix who info) :
    (M.runBehavioral (Profile.update unknown who (prefix who)) cut).bind
        (fun history => seed.bind fun k =>
          M.runBehavioralFrom (Profile.update unknown who (plays k who)) remaining history) =
      M.runBehavioral (Profile.update unknown who
        (ownReachAverageProfile M (fun _ => seed) plays fallback who)) (cut + remaining) := by
  rw [FinDist.bind_comm]
  calc
    _ = seed.bind (fun k =>
        (M.runBehavioral (Profile.update unknown who (plays k who)) cut).bind
          (M.runBehavioralFrom (Profile.update unknown who (plays k who)) remaining)) := by
      apply FinDist.bind_congr
      intro k sampled
      rw [cfrD_run_cut_congr M clock unknown who (plays k who) (prefix who) cut
        (agree k sampled)]
    _ = seed.bind (fun k =>
        M.runBehavioral (Profile.update unknown who (plays k who)) (cut + remaining)) := by
      apply FinDist.bind_congr
      intro k _
      exact (M.runBehavioralFrom_add _ cut remaining E.initHistory).symm
    _ = _ := (run_unilateral_average M hrecall (fun _ => seed) plays fallback
      unknown who (cut + remaining)).symm

/-- Complete child policies are clamped to the parent's already selected
trunk. They remain legal information-local profiles. -/
def cfrDChildProfiles (clock : ObservationClock M) (cut : Nat)
    (trunk : Profile M.behavioralSignature) (children : K → Profile M.behavioralSignature) :
    K → Profile M.behavioralSignature :=
  fun k => cfrDDepthProfile M clock cut trunk (children k)

/-- Every child has exactly the same searched prefix by construction. -/
theorem cfrDChildProfiles_before (clock : ObservationClock M) (cut : Nat)
    (trunk : Profile M.behavioralSignature) (children : K → Profile M.behavioralSignature)
    (k : K) (who : ι) (info : M.InfoState who) (before : clock.depth who info < cut) :
    cfrDChildProfiles M clock cut trunk children k who info = trunk who info := by
  simp only [cfrDChildProfiles, cfrDDepthProfile, cfrDDepthTrunk, decide_eq_true_eq,
    if_pos before]

/-- The continuation witness is built from these very child policies using
independent own-reach averaging, never an arbitrary equilibrium selection. -/
def cfrDChildAverage (clock : ObservationClock M) (cut : Nat)
    (seed : FinDist K) (trunk : Profile M.behavioralSignature)
    (children : K → Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who) :
    Profile M.behavioralSignature :=
  ownReachAverageProfile M (fun _ => seed) (cfrDChildProfiles M clock cut trunk children) fallback

/-- Averaging the clamped child policies preserves the parent's entire
prefix law against arbitrary opponents, without assuming nonzero own reach. -/
theorem cfrDChildAverage_prefix (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (cut : Nat) (seed : FinDist K) (trunk : Profile M.behavioralSignature)
    (children : K → Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (unknown : Profile M.behavioralSignature) (who : ι) :
    M.runBehavioral (Profile.update unknown who
        (cfrDChildAverage M clock cut seed trunk children fallback who)) cut =
      M.runBehavioral (Profile.update unknown who (trunk who)) cut := by
  rw [cfrDChildAverage, run_unilateral_average M hrecall]
  calc
    _ = seed.bind (fun _ =>
        M.runBehavioral (Profile.update unknown who (trunk who)) cut) := by
      apply FinDist.bind_congr
      intro k _
      exact cfrD_run_cut_congr M clock unknown who _ _ cut
        (fun info before => cfrDChildProfiles_before M clock cut trunk children k who info before)
    _ = _ := FinDist.bind_const _ _

omit [Fintype K] in
/-- The canonical depth-profile executes its trunk and then its continuation.
This identity retains terminal absorption and the exact remaining fuel. -/
theorem cfrDDepthProfile_unilateral_bind (clock : ObservationClock M)
    (trunk continuation unknown : Profile M.behavioralSignature)
    (who : ι) (cut remaining : Nat) :
    M.runBehavioral (Profile.update unknown who
        (cfrDDepthProfile M clock cut trunk continuation who)) (cut + remaining) =
      (M.runBehavioral (Profile.update unknown who (trunk who)) cut).bind
        (M.runBehavioralFrom (Profile.update unknown who (continuation who)) remaining) := by
  have split := cfrDPrefix_run_bind M clock
    (Profile.update unknown who (continuation who)) who (trunk who) cut remaining
  simpa only [cfrDPrefixPolicy, cfrDDepthProfile, cfrDDepthTrunk, decide_eq_true_eq,
    Profile.update_same, Profile.update_idem] using split

/-- A constructed child draw is exactly the parent's virtual averaged
continuation. Unlike a generic replacement inequality this needs no
fixed-opponent no-loss premise and holds for every history observable. -/
theorem cfrDChild_sampling_eq (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (cut remaining : Nat) (seed : FinDist K) (trunk : Profile M.behavioralSignature)
    (children : K → Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (unknown : Profile M.behavioralSignature) (who : ι) :
    (M.runBehavioral (Profile.update unknown who (trunk who)) cut).bind
        (fun history => seed.bind fun k => M.runBehavioralFrom
          (Profile.update unknown who (cfrDChildProfiles M clock cut trunk children k who))
          remaining history) =
      M.runBehavioral (Profile.update unknown who (cfrDDepthProfile M clock cut trunk
        (cfrDChildAverage M clock cut seed trunk children fallback) who)) (cut + remaining) := by
  let average := cfrDChildAverage M clock cut seed trunk children fallback
  calc
    _ = M.runBehavioral (Profile.update unknown who (average who)) (cut + remaining) :=
      cfrD_delayed_private_sampling M clock hrecall seed
        (cfrDChildProfiles M clock cut trunk children) fallback trunk unknown who cut remaining
        (fun k _ info before => cfrDChildProfiles_before M clock cut trunk children k who info before)
    _ = (M.runBehavioral (Profile.update unknown who (average who)) cut).bind
        (M.runBehavioralFrom (Profile.update unknown who (average who)) remaining) :=
      M.runBehavioralFrom_add _ cut remaining E.initHistory
    _ = (M.runBehavioral (Profile.update unknown who (trunk who)) cut).bind
        (M.runBehavioralFrom (Profile.update unknown who (average who)) remaining) := by
      rw [cfrDChildAverage_prefix M clock hrecall cut seed trunk children fallback unknown who]
    _ = _ := (cfrDDepthProfile_unilateral_bind M clock trunk average unknown
      who cut remaining).symm

end GameTheory.ReBeL
