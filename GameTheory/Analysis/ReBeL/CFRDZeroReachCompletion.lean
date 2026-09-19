/-
# Completing zero-own-reach policies without changing actual execution

A counterfactual completion may replace a player's policy only where that
player's original own reach is zero. Perfect recall makes this a legal
information-local operation. The complete own-reach function, all unilateral
outcome laws, and the canonical Nash predicate are preserved. These identities
do not claim that an arbitrary completion is counterfactually optimal.
-/

import GameTheory.Analysis.ReBeL.CFRDDelayedSampling

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Complete only zero OWN reach, never zero joint or opponent reach.
The replacement policy still depends exclusively on the player's information. -/
def cfrDCompleteZeroReach (base completion : Profile M.behavioralSignature) :
    Profile M.behavioralSignature := fun who info => by
  classical
  exact if informationOwnReach M base who info = 0 then completion who info else base who info

/-- A genuinely zero-own-reach information state uses the supplied completion. -/
theorem cfrDCompleteZeroReach_of_zero (base completion : Profile M.behavioralSignature)
    (who : ι) (info : M.InfoState who) (zero : informationOwnReach M base who info = 0) :
    cfrDCompleteZeroReach M base completion who info = completion who info := by
  simp only [cfrDCompleteZeroReach, if_pos zero]

/-- Positive-own-reach information states retain exactly the original policy. -/
theorem cfrDCompleteZeroReach_of_ne (base completion : Profile M.behavioralSignature)
    (who : ι) (info : M.InfoState who) (nonzero : informationOwnReach M base who info ≠ 0) :
    cfrDCompleteZeroReach M base completion who info = base who info := by
  simp only [cfrDCompleteZeroReach, if_neg nonzero]

/-- Completing unreachable decisions preserves every legal trace's own reach.
No positive factual reach assumption or hidden-history policy is required. -/
theorem cfrDCompleteZeroReach_playerReach (hrecall : M.PerfectRecall)
    (base completion : Profile M.behavioralSignature) (who : ι)
    {state : E.State} (trace : E.Trace state) :
    M.playerReachProbability (cfrDCompleteZeroReach M base completion) who trace =
      M.playerReachProbability base who trace := by
  classical
  induction trace with
  | start => rfl
  | @extend source target prior joint legal realized ih =>
      calc
        _ = M.playerReachProbability (cfrDCompleteZeroReach M base completion) who prior *
            (cfrDCompleteZeroReach M base completion who (M.infoOf who prior)).prob
              (M.choicesOfLegal prior ⟨joint, legal⟩ who) := rfl
        _ = M.playerReachProbability base who prior *
            (cfrDCompleteZeroReach M base completion who (M.infoOf who prior)).prob
              (M.choicesOfLegal prior ⟨joint, legal⟩ who) := by rw [ih]
        _ = M.playerReachProbability base who (prior.extend joint legal realized) := by
          by_cases zero : informationOwnReach M base who (M.infoOf who prior) = 0
          · have reach_zero : M.playerReachProbability base who prior = 0 := by
              simpa only [informationOwnReach_eq_player M hrecall base who
                (⟨source, prior⟩ : E.History)] using zero
            simp only [InformationModel.playerReachProbability, reach_zero, zero_mul]
          · rw [cfrDCompleteZeroReach_of_ne M base completion who _ zero]
            rfl

variable [Fintype ι]

/-- Simultaneous completion of all players preserves the full canonical law. -/
theorem cfrDCompleteZeroReach_run (hrecall : M.PerfectRecall)
    (base completion : Profile M.behavioralSignature) (horizon : Nat) :
    M.runBehavioral (cfrDCompleteZeroReach M base completion) horizon =
      M.runBehavioral base horizon := by
  apply FinDist.ext_of_prob
  intro history
  rw [run_probability_factorization M, run_probability_factorization M]
  simp_rw [cfrDCompleteZeroReach_playerReach M hrecall]

variable [DecidableEq ι]

/-- A completed focal policy has its original outcome law against EVERY
fixed opponent. This is stronger than equality of the on-policy return. -/
theorem cfrDCompleteZeroReach_unilateral_run (hrecall : M.PerfectRecall)
    (base completion unknown : Profile M.behavioralSignature) (who : ι) (horizon : Nat) :
    M.runBehavioral (Profile.update unknown who
        (cfrDCompleteZeroReach M base completion who)) horizon =
      M.runBehavioral (Profile.update unknown who (base who)) horizon := by
  apply FinDist.ext_of_prob
  intro history
  rw [unilateral_probability_factorization M, unilateral_probability_factorization M]
  have first := ownReach_eq_of_policy_eq M
    (Profile.update unknown who (cfrDCompleteZeroReach M base completion who))
    (cfrDCompleteZeroReach M base completion) who (Profile.update_same _ _ _) history.trace
  have second := ownReach_eq_of_policy_eq M
    (Profile.update unknown who (base who)) base who (Profile.update_same _ _ _) history.trace
  rw [first, second, cfrDCompleteZeroReach_playerReach M hrecall]

/-- Every deviation against the completed opponents has its original law too.
Changing several off-path policies together does not create a new deviation. -/
theorem cfrDCompleteZeroReach_deviation_run (hrecall : M.PerfectRecall)
    (base completion : Profile M.behavioralSignature) (who : ι)
    (replacement : M.BehavioralPolicy who) (horizon : Nat) :
    M.runBehavioral
        (Profile.update (cfrDCompleteZeroReach M base completion) who replacement) horizon =
      M.runBehavioral (Profile.update base who replacement) horizon := by
  apply FinDist.ext_of_prob
  intro history
  rw [unilateral_probability_factorization M, unilateral_probability_factorization M]
  simp_rw [cfrDCompleteZeroReach_playerReach M hrecall]
  have focal := ownReach_eq_of_policy_eq M
    (Profile.update (cfrDCompleteZeroReach M base completion) who replacement)
    (Profile.update base who replacement) who (by simp only [Profile.update_same]) history.trace
  rw [focal]

/-- Nash is preserved by a legal zero-own-reach completion. This does NOT
assert that an arbitrary supplied completion satisfies counterfactual optimality. -/
theorem cfrDCompleteZeroReach_isNash (hrecall : M.PerfectRecall)
    (base completion : Profile M.behavioralSignature) (horizon : Nat)
    (payoff : E.History → ι → ℝ)
    (equilibrium : IsNash (M.toBehavioralGameForm horizon) (euPreference payoff) base) :
    IsNash (M.toBehavioralGameForm horizon) (euPreference payoff)
      (cfrDCompleteZeroReach M base completion) := by
  rw [isNash_iff] at equilibrium ⊢
  intro who replacement
  simpa only [InformationModel.toBehavioralGameForm,
    cfrDCompleteZeroReach_run M hrecall, cfrDCompleteZeroReach_deviation_run M hrecall]
    using equilibrium who replacement

variable {K : Type*} [Fintype K]

/-- Child averaging with a separate, information-local zero-reach completion.
This does not alter positive-reach averaging weights or the actual child draw. -/
def cfrDCompletedChildAverage (clock : ObservationClock M) (cut : Nat)
    (seed : FinDist K) (trunk : Profile M.behavioralSignature)
    (children : K → Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (completion : Profile M.behavioralSignature) : Profile M.behavioralSignature :=
  cfrDCompleteZeroReach M (cfrDChildAverage M clock cut seed trunk children fallback) completion

/-- The completed child average still has exactly the selected parent prefix. -/
theorem cfrDCompletedChildAverage_prefix (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (cut : Nat) (seed : FinDist K)
    (trunk : Profile M.behavioralSignature) (children : K → Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (completion unknown : Profile M.behavioralSignature)
    (who : ι) :
    M.runBehavioral (Profile.update unknown who
        (cfrDCompletedChildAverage M clock cut seed trunk children fallback completion who)) cut =
      M.runBehavioral (Profile.update unknown who (trunk who)) cut := by
  rw [cfrDCompletedChildAverage, cfrDCompleteZeroReach_unilateral_run M hrecall,
    cfrDChildAverage_prefix M clock hrecall]

/-- Counterfactual completion is compatible with delayed private child
sampling. The exact original-game law is unchanged against arbitrary opponents. -/
theorem cfrDCompletedChild_sampling_eq (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (cut remaining : Nat) (seed : FinDist K)
    (trunk : Profile M.behavioralSignature) (children : K → Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (completion unknown : Profile M.behavioralSignature)
    (who : ι) :
    (M.runBehavioral (Profile.update unknown who (trunk who)) cut).bind
        (fun history => seed.bind fun k => M.runBehavioralFrom
          (Profile.update unknown who (cfrDChildProfiles M clock cut trunk children k who))
          remaining history) =
      M.runBehavioral (Profile.update unknown who (cfrDDepthProfile M clock cut trunk
        (cfrDCompletedChildAverage M clock cut seed trunk children fallback completion) who))
        (cut + remaining) := by
  let average := cfrDChildAverage M clock cut seed trunk children fallback
  let completed := cfrDCompletedChildAverage M clock cut seed trunk children fallback completion
  calc
    _ = M.runBehavioral (Profile.update unknown who (average who)) (cut + remaining) :=
      cfrD_delayed_private_sampling M clock hrecall seed
        (cfrDChildProfiles M clock cut trunk children) fallback trunk unknown who cut remaining
        (fun k _ info before =>
          cfrDChildProfiles_before M clock cut trunk children k who info before)
    _ = M.runBehavioral (Profile.update unknown who (completed who)) (cut + remaining) :=
      (cfrDCompleteZeroReach_unilateral_run M hrecall average completion unknown
        who (cut + remaining)).symm
    _ = (M.runBehavioral (Profile.update unknown who (completed who)) cut).bind
        (M.runBehavioralFrom (Profile.update unknown who (completed who)) remaining) :=
      M.runBehavioralFrom_add _ cut remaining E.initHistory
    _ = (M.runBehavioral (Profile.update unknown who (trunk who)) cut).bind
        (M.runBehavioralFrom (Profile.update unknown who (completed who)) remaining) := by
      rw [cfrDCompletedChildAverage_prefix M clock hrecall cut seed trunk children
        fallback completion unknown who]
    _ = _ := (cfrDDepthProfile_unilateral_bind M clock trunk completed unknown
      who cut remaining).symm

end GameTheory.ReBeL
