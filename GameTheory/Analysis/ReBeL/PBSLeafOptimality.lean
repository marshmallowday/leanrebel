/-
# Leaf equilibrium implies conditional continuation optimality

A canonical PBS equilibrium attains every conditional best response whose
own type has positive mass. This uses one legal remembered-type splice, not
separate hidden-state decisions. Zero-mass types are deliberately excluded:
ordinary on-path Nash alone is not an off-path continuation certificate.
-/

import GameTheory.Analysis.ReBeL.PBSInfoValue
import GameTheory.Analysis.ReBeL.BeliefExistence

noncomputable section

namespace GameTheory.ReBeL.TypeBeliefSlice

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk ut
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable {M : InformationModel.{uι, us, ua, up, uq, uk} E}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype E.History] [∀ i, Fintype (E.Action i)]
variable {observations : List M.PublicSignal} {who : ι} {T : Type ut}
variable (slice : TypeBeliefSlice M observations who T)

/-- A joint PBS equilibrium realizes the infostate best-response value at
EVERY supported own type. The statement does not divide by the type's mass. -/
theorem conditional_value_eq_of_nash (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (own : FinDist T)
    (profile : Profile M.behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreference utility) profile) (type : T) (supported : type ∈ own.support) :
    slice.conditionalPayoff profile fuel (fun history => utility history who)
        (profile who) type =
      slice.infoValue fallback fuel (fun history => utility history who) profile type := by
  let value := slice.infoValue fallback fuel (fun history => utility history who) profile
  let actual := slice.conditionalPayoff profile fuel (fun history => utility history who)
    (profile who)
  have point (t : T) : actual t ≤ value t :=
    slice.conditionalPayoff_le_infoValue hrecall fallback fuel
      (fun history => utility history who) profile t (profile who)
  have attained := slice.branch_attained fallback fuel (fun history => utility history who)
    own profile
  have equilibrium_bound :
      (PublicBelief.continuationLaw M (Profile.update profile who
        (slice.simultaneousResponse fallback fuel (fun history => utility history who)
          profile).toBehavioral) fuel (slice.mixture own)).expect
        (fun history => utility history who) ≤
      (PublicBelief.continuationLaw M profile fuel (slice.mixture own)).expect
        (fun history => utility history who) :=
    (isNash_iff (F := behavioralBeliefForm M (slice.mixture own) fuel)
      (weaklyPrefers := euPreference utility) profile).mp equilibrium who _
  have mean : own.expect value ≤ own.expect actual := by
    calc
      _ = (PublicBelief.continuationLaw M (Profile.update profile who
          (slice.simultaneousResponse fallback fuel (fun history => utility history who)
            profile).toBehavioral) fuel (slice.mixture own)).expect
            (fun history => utility history who) := attained.symm
      _ ≤ (PublicBelief.continuationLaw M profile fuel (slice.mixture own)).expect
          (fun history => utility history who) := equilibrium_bound
      _ = own.expect actual := by
        unfold actual conditionalPayoff
        rw [Profile.update_eq_self, slice.mixture_payoff]
  have zero : own.expect (fun t => actual t - value t) = 0 := by
    rw [FinDist.expect_sub]
    have other : own.expect actual ≤ own.expect value := FinDist.expect_mono fun t _ => point t
    linarith
  have equal := FinDist.eq_of_expect_eq_of_le own (fun t => actual t - value t) 0
    (fun t _ => sub_nonpos.mpr (point t)) zero supported
  exact sub_eq_zero.mp equal

/-- The continuation inequality against every complete information-local
policy follows from Nash and remembered-type attainment, not from a supplied
root-regret or safety conclusion. -/
theorem conditional_bestResponse_of_nash (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (own : FinDist T)
    (profile : Profile M.behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreference utility) profile) (type : T) (supported : type ∈ own.support)
    (target : M.BehavioralPolicy who) :
    slice.conditionalPayoff profile fuel (fun history => utility history who) target type ≤
      slice.conditionalPayoff profile fuel (fun history => utility history who)
        (profile who) type := by
  rw [slice.conditional_value_eq_of_nash hrecall fallback fuel utility own profile
    equilibrium type supported]
  exact slice.conditionalPayoff_le_infoValue hrecall fallback fuel
    (fun history => utility history who) profile type target

end GameTheory.ReBeL.TypeBeliefSlice
