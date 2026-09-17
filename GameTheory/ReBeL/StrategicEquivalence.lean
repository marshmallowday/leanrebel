/-
# Strategic correspondence for public-history prescriptions

The public game below runs actual Bayesian referee updates. Its admissible
strategies are precisely public-history-indexed legal prescriptions. Outcome
preservation is proved first, then expected rewards and unilateral deviations,
and only then Nash preservation. No best-response or equilibrium oracle occurs.

This is not a claim about unrestricted strategies that react to extra public
announcements of other players' complete plans. See docs/rebel/M03.md.
-/

import GameTheory.ReBeL.Prescription
import GameTheory.ReBeL.BeliefExecution

noncomputable section

namespace GameTheory.ReBeL.Prescription

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable [Fintype ι] (M : InformationModel E)

/-- The original full-memory game, starting at a fixed joint PBS. -/
abbrev originalGame (belief : PublicBelief.State (fullInformation M)) (fuel : Nat) :
    GameForm ι where
  sig := (fullInformation M).behavioralSignature
  play profile := PublicBelief.continuationLaw (fullInformation M) profile fuel belief.2

/-- The referee game uses public prescriptions and actual posterior transitions. -/
abbrev beliefGame (fallback : Profile (fullInformation M).behavioralSignature)
    (belief : PublicBelief.State (fullInformation M)) (fuel : Nat) : GameForm ι where
  sig := signature M
  play profile :=
    (PublicBelief.run (fullInformation M) (decodeProfile M fallback profile) fuel belief).bind
      (fun next => next.2.law)

/-- Decoding preserves the outcome law because Bayesian updating commutes with execution. -/
theorem outcome_decode (fallback : Profile (fullInformation M).behavioralSignature)
    (belief : PublicBelief.State (fullInformation M)) (fuel : Nat)
    (profile : Profile (signature M)) :
    (beliefGame M fallback belief fuel).play profile =
      (originalGame M belief fuel).play (decodeProfile M fallback profile) :=
  PublicBelief.run_law (fullInformation M) (decodeProfile M fallback profile) fuel belief

/-- Encoding preserves every canonical history outcome, not just a chosen payoff. -/
theorem outcome_encode (fallback : Profile (fullInformation M).behavioralSignature)
    (belief : PublicBelief.State (fullInformation M)) (fuel : Nat)
    (profile : Profile (fullInformation M).behavioralSignature) :
    (beliefGame M fallback belief fuel).play (encodeProfile M profile) =
      (originalGame M belief fuel).play profile := by
  rw [outcome_decode]
  exact FinDist.bind_congr fun root _ => run_decode_encode M fallback profile fuel root

/-- The expected value of any history observable is preserved after the law proof. -/
theorem expected_reward_encode (fallback : Profile (fullInformation M).behavioralSignature)
    (belief : PublicBelief.State (fullInformation M)) (fuel : Nat)
    (profile : Profile (fullInformation M).behavioralSignature) (utility : E.History → ι → ℝ)
    (i : ι) :
    expectedUtility utility i
        ((beliefGame M fallback belief fuel).play (encodeProfile M profile)) =
      expectedUtility utility i ((originalGame M belief fuel).play profile) := by
  rw [outcome_encode]

/-- Every original unilateral deviation has a matching public prescription deviation. -/
theorem outcome_original_deviation [DecidableEq ι]
    (fallback : Profile (fullInformation M).behavioralSignature)
    (belief : PublicBelief.State (fullInformation M)) (fuel : Nat)
    (profile : Profile (fullInformation M).behavioralSignature) (i : ι)
    (replacement : (fullInformation M).BehavioralPolicy i) :
    (beliefGame M fallback belief fuel).play
        (Profile.update (encodeProfile M profile) i (encode M i replacement)) =
      (originalGame M belief fuel).play (Profile.update profile i replacement) := by
  rw [← encodeProfile_update, outcome_encode]

/-- Conversely, every public deviation has a legal original deviation with opponents fixed. -/
theorem outcome_public_deviation [DecidableEq ι]
    (fallback : Profile (fullInformation M).behavioralSignature)
    (belief : PublicBelief.State (fullInformation M)) (fuel : Nat)
    (profile : Profile (fullInformation M).behavioralSignature) (i : ι)
    (replacement : Policy M i) :
    (beliefGame M fallback belief fuel).play
        (Profile.update (encodeProfile M profile) i replacement) =
      (originalGame M belief fuel).play
        (Profile.update profile i (decode M i (fallback i) replacement)) := by
  have h := outcome_original_deviation M fallback belief fuel profile i
    (decode M i (fallback i) replacement)
  simpa only [encode_decode] using h

/-- Nash preservation follows from the two deviation directions; fixed-profile law equality
alone would not suffice. The theorem is for the stated prescription strategy domain. -/
theorem isNash_encode_iff [DecidableEq ι]
    (fallback : Profile (fullInformation M).behavioralSignature)
    (belief : PublicBelief.State (fullInformation M)) (fuel : Nat)
    (profile : Profile (fullInformation M).behavioralSignature) (utility : E.History → ι → ℝ) :
    IsNash (originalGame M belief fuel) (euPreference utility) profile ↔
      IsNash (beliefGame M fallback belief fuel) (euPreference utility) (encodeProfile M profile) := by
  rw [isNash_iff, isNash_iff]
  constructor
  · intro hnash i replacement
    rw [outcome_public_deviation, outcome_encode]
    exact hnash i (decode M i (fallback i) replacement)
  · intro hnash i replacement
    have h := hnash i (encode M i replacement)
    rw [outcome_original_deviation, outcome_encode] at h
    exact h

/-- The reverse strategy map preserves Nash as well, not just the image of a chosen profile. -/
theorem isNash_decode_iff [DecidableEq ι]
    (fallback : Profile (fullInformation M).behavioralSignature)
    (belief : PublicBelief.State (fullInformation M)) (fuel : Nat)
    (profile : Profile (signature M)) (utility : E.History → ι → ℝ) :
    IsNash (originalGame M belief fuel) (euPreference utility) (decodeProfile M fallback profile) ↔
      IsNash (beliefGame M fallback belief fuel) (euPreference utility) profile := by
  simpa only [encodeProfile_decodeProfile] using
    isNash_encode_iff M fallback belief fuel (decodeProfile M fallback profile) utility

end GameTheory.ReBeL.Prescription
