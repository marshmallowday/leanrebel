/-
# Fixed-T information-set CFR at an original public belief

The reverse information-local policy map transfers the native rooted CFR
bound to the ORIGINAL behavioral continuation game with the same error.
The resulting profile is computed from information-set regret matching, not
from a complete-plan normal-form learner or an assumed child Nash certificate.
Conditional guarantees keep the actual type probability explicit.
-/

import GameTheory.Analysis.ReBeL.PBSRootDecode
import GameTheory.Analysis.ReBeL.PBSRootCFR
import GameTheory.Analysis.ReBeL.PBSApproximateOptimality

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk ut
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {observations : List M.PublicSignal}

/-- Arbitrary rooted approximate equilibria transfer without inflating the
error. Every original behavioral deviation has a matching legal rooted lift. -/
theorem pbsRootDecodeProfile_isNash
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (payoff : Fin 2 → E.History → ℝ) (fuel : Nat)
    (profile : Profile (pbsRootFullInformation M belief.law).behavioralSignature)
    (error : ℝ)
    (equilibrium : IsNash ((pbsRootFullInformation M belief.law).toBehavioralGameForm (fuel + 1))
      (euPreferenceWithin error (fun history who => pbsRootPayoff belief.law payoff who history))
      profile) :
    IsNash (behavioralBeliefForm (fullInformation M) belief fuel)
      (euPreferenceWithin error (fun history who => payoff who history))
      (pbsRootDecodeProfile M belief.law (observations.length - 1) profile) := by
  rw [isNash_iff] at equilibrium ⊢
  intro who replacement
  have bound := equilibrium who (pbsRootBehavioralFullPolicy M belief.law who replacement)
  rw [euPreferenceWithin_apply] at bound ⊢
  change ((pbsRootFullInformation M belief.law).runBehavioral
      (Profile.update profile who (pbsRootBehavioralFullPolicy M belief.law who replacement))
      (fuel + 1)).expect (fun history => history.state.elim 0 (payoff who)) ≤
    ((pbsRootFullInformation M belief.law).runBehavioral profile (fuel + 1)).expect
      (fun history => history.state.elim 0 (payoff who)) + error at bound
  rw [pbsRootDecodeProfile_unilateral_expect M belief.law (observations.length - 1)
      (pbsRoot_publicBelief_depth M belief),
    pbsRootDecodeProfile_expect M belief.law (observations.length - 1)
      (pbsRoot_publicBelief_depth M belief)] at bound
  exact bound

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- The actual fixed-positive-T child output, usable directly in the original
game through its own local AOH. The public cut is derived from the belief. -/
def pbsInformationCFR
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t] : Profile (fullInformation M).behavioralSignature :=
  pbsRootDecodeProfile M belief.law (observations.length - 1)
    (pbsRootCFR M belief.law fallback payoff fuel t)

/-- The original-PBS Nash bound is derived from the actual information-set
recurrence. No child optimality, positive mass floor or regret proof is an input. -/
theorem pbsInformationCFR_isNash
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (bound : Fin 2 → ℝ) (hbound0 : ∀ who, 0 ≤ bound who)
    (hbound : ∀ who history, |payoff who history| ≤ bound who)
    (fuel t : Nat) [NeZero t] :
    IsNash (behavioralBeliefForm (fullInformation M) belief fuel)
      (euPreferenceWithin (pbsRootCFRBound M belief.law bound fuel t)
        (fun history who => payoff who history))
      (pbsInformationCFR M belief fallback payoff fuel t) :=
  pbsRootDecodeProfile_isNash M belief payoff fuel _ _
    (pbsRootCFR_isNash M belief.law fallback payoff hzero bound hbound0 hbound fuel t)

variable {who : Fin 2} {T : Type ut}

/-- The same computed child controls the probability-weighted infostate gap,
including zero-mass types without a false off-path optimality claim. -/
theorem pbsInformationCFR_weighted_infoGap
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : (player : Fin 2) → M.Policy player) (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history player => payoff player history))
    (bound : Fin 2 → ℝ) (hbound0 : ∀ player, 0 ≤ bound player)
    (hbound : ∀ player history, |payoff player history| ≤ bound player)
    (fuel t : Nat) [NeZero t] (type : T) :
    let profile := pbsInformationCFR M (slice.mixture own) fallback payoff fuel t
    own.prob type *
      (slice.infoValue (fun player => liftPolicy M player (fallback player)) fuel (payoff who)
          profile type -
        slice.conditionalPayoff profile fuel (payoff who) (profile who) type) ≤
      pbsRootCFRBound M (slice.mixture own).law bound fuel t := by
  exact slice.weighted_infoGap_le_of_approxNash (fullSignals_perfectRecall M.toInfoSignals)
    (fun player => liftPolicy M player (fallback player)) fuel (fun history player =>
      payoff player history) own _ _
    (pbsInformationCFR_isNash M (slice.mixture own) fallback payoff hzero bound hbound0 hbound
      fuel t) type

/-- A supported infostate's actual behavioral deviation gain has the explicit
finite-T residual divided by its own probability. There is no hidden mass floor. -/
theorem pbsInformationCFR_conditional_gain
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : (player : Fin 2) → M.Policy player) (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history player => payoff player history))
    (bound : Fin 2 → ℝ) (hbound0 : ∀ player, 0 ≤ bound player)
    (hbound : ∀ player history, |payoff player history| ≤ bound player)
    (fuel t : Nat) [NeZero t] (type : T) (supported : type ∈ own.support)
    (replacement : (fullInformation M).BehavioralPolicy who) :
    let profile := pbsInformationCFR M (slice.mixture own) fallback payoff fuel t
    slice.conditionalPayoff profile fuel (payoff who) replacement type -
      slice.conditionalPayoff profile fuel (payoff who) (profile who) type ≤
      pbsRootCFRBound M (slice.mixture own).law bound fuel t / own.prob type := by
  exact slice.conditional_gain_le_of_approxNash (fullSignals_perfectRecall M.toInfoSignals)
    (fun player => liftPolicy M player (fallback player)) fuel (fun history player =>
      payoff player history) own _ _
    (pbsInformationCFR_isNash M (slice.mixture own) fallback payoff hzero bound hbound0 hbound
      fuel t) type supported replacement

end GameTheory.ReBeL
