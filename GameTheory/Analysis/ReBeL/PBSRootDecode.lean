/-
# Information-local decoding of arbitrary rooted behavioral policies

The decoder reads only the player's own original full AOH and the public cut.
It preserves all legal local option laws, all original unilateral replacements,
and the full canonical execution law. A root-depth condition is proved from
an actual PublicBelief by PBSRootLocalHistory, not assumed as a policy oracle.
-/

import GameTheory.Analysis.ReBeL.PBSRootLocalHistory
import GameTheory.Analysis.ReBeL.PBSRootBehavioral

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable (roots : FinDist E.History) (cut : Nat)

/-- Decode any new rooted policy through its information-local reconstruction.
The dependent menu proof changes no action or probability. -/
def pbsRootDecodePolicy (who : ι)
    (policy : (fullInformation
      (pbsRootInformation (fullInformation M) roots)).BehavioralPolicy who) :
    (fullInformation M).BehavioralPolicy who := fun info =>
  (policy (info.rootedAt cut)).map fun choice => ⟨choice.val, by
    have legal := choice.property
    change choice.val ∈ (pbsRootInformation (fullInformation M) roots).menu who
      (reduceAOH (pbsRootInformation (fullInformation M) roots).toInfoSignals who
        (info.rootedAt cut)) at legal
    rw [pbsRootLocalHistory_read] at legal
    exact legal⟩

/-- Forgetting legality certificates exposes exactly the same option law. -/
theorem pbsRootDecodePolicy_actions (who : ι)
    (policy : (fullInformation (pbsRootInformation (fullInformation M) roots)).BehavioralPolicy who)
    (info : (fullInformation M).InfoState who) :
    (pbsRootDecodePolicy M roots cut who policy info).map Subtype.val =
      (policy (info.rootedAt cut)).map Subtype.val := by
  rw [pbsRootDecodePolicy, FinDist.map_comp]
  rfl

/-- Decoding an original lifted policy is the identity at every local AOH,
including inputs which are not reached by the current belief or strategy. -/
theorem pbsRootDecodePolicy_lift (who : ι) (policy : (fullInformation M).BehavioralPolicy who) :
    pbsRootDecodePolicy M roots cut who (pbsRootBehavioralFullPolicy M roots who policy) =
      policy := by
  funext info
  apply FinDist.map_injective Subtype.val_injective
  rw [pbsRootDecodePolicy_actions]
  unfold pbsRootBehavioralFullPolicy
  rw [pbsRootLocalHistory_read]
  rfl

/-- The reverse map remains coordinatewise; other players' policies are not inputs. -/
def pbsRootDecodeProfile
    (profile : Profile (fullInformation
      (pbsRootInformation (fullInformation M) roots)).behavioralSignature) :
    Profile (fullInformation M).behavioralSignature :=
  fun who => pbsRootDecodePolicy M roots cut who (profile who)

/-- The round trip on original profiles is exact, not merely payoff equivalent. -/
theorem pbsRootDecodeProfile_lift (profile : Profile (fullInformation M).behavioralSignature) :
    pbsRootDecodeProfile M roots cut (pbsRootBehavioralFullProfile M roots profile) = profile := by
  funext who
  exact pbsRootDecodePolicy_lift M roots cut who (profile who)

/-- Lifting the decoded policy recovers the original rooted choice law at
EVERY legal rooted trace. Synthetic rooted local sequences need not agree. -/
theorem pbsRootDecodePolicy_agrees
    (rootDepth : ∀ history ∈ roots.support, history.trace.length = cut) (who : ι)
    (policy : (fullInformation (pbsRootInformation (fullInformation M) roots)).BehavioralPolicy who)
    {state : (pbsRootProtocol roots).State} (trace : (pbsRootProtocol roots).Trace state) :
    pbsRootBehavioralFullPolicy M roots who (pbsRootDecodePolicy M roots cut who policy)
        ((fullInformation (pbsRootInformation (fullInformation M) roots)).infoOf who trace) =
      policy ((fullInformation (pbsRootInformation (fullInformation M) roots)).infoOf
        who trace) := by
  cases state with
  | none =>
      exact InformationModel.behavioral_eq_of_not_active
        (fullInformation (pbsRootInformation (fullInformation M) roots)) _ _ trace not_false
  | some original =>
      apply FinDist.map_injective Subtype.val_injective
      rw [(pbsRootLocalHistory_trace M roots cut rootDepth who trace).2]
      unfold pbsRootBehavioralFullPolicy
      rw [pbsRootLocalHistory_read]
      exact pbsRootDecodePolicy_actions M roots cut who policy _

section Execution

variable [Fintype ι]

/-- The complete rooted-history law is unchanged by decode followed by lift. -/
theorem pbsRootDecodeProfile_run
    (rootDepth : ∀ history ∈ roots.support, history.trace.length = cut)
    (profile : Profile (fullInformation
      (pbsRootInformation (fullInformation M) roots)).behavioralSignature) (fuel : Nat) :
    (fullInformation (pbsRootInformation (fullInformation M) roots)).runBehavioral profile fuel =
      (fullInformation (pbsRootInformation (fullInformation M) roots)).runBehavioral
        (pbsRootBehavioralFullProfile M roots (pbsRootDecodeProfile M roots cut profile)) fuel := by
  apply (fullInformation (pbsRootInformation (fullInformation M) roots)).runBehavioralFrom_congr
  intro later _ _ who
  exact (pbsRootDecodePolicy_agrees M roots cut rootDepth who (profile who) later.trace).symm

/-- Arbitrary rooted output decodes to the exact original continuation law,
with one administrative chance step and no numerical or switching penalty. -/
theorem pbsRootDecodeProfile_law
    (rootDepth : ∀ history ∈ roots.support, history.trace.length = cut)
    (profile : Profile (fullInformation
      (pbsRootInformation (fullInformation M) roots)).behavioralSignature) (fuel : Nat) :
    ((fullInformation (pbsRootInformation (fullInformation M) roots)).runBehavioral
      profile (fuel + 1)).map History.state =
        (roots.bind ((fullInformation M).runBehavioralFrom
          (pbsRootDecodeProfile M roots cut profile) fuel)).map some := by
  rw [pbsRootDecodeProfile_run M roots cut rootDepth profile (fuel + 1)]
  exact pbsRoot_behavioralFull_law M roots (pbsRootDecodeProfile M roots cut profile) fuel

/-- Every history observable has the same expectation under the two laws. -/
theorem pbsRootDecodeProfile_expect
    (rootDepth : ∀ history ∈ roots.support, history.trace.length = cut)
    (profile : Profile (fullInformation
      (pbsRootInformation (fullInformation M) roots)).behavioralSignature)
    (fuel : Nat) (value : E.History → ℝ) :
    ((fullInformation (pbsRootInformation (fullInformation M) roots)).runBehavioral
      profile (fuel + 1)).expect (fun history => history.state.elim 0 value) =
        (roots.bind ((fullInformation M).runBehavioralFrom
          (pbsRootDecodeProfile M roots cut profile) fuel)).expect value := by
  have equal := congrArg (fun law : FinDist (Option E.History) =>
    law.expect (fun state => state.elim 0 value))
      (pbsRootDecodeProfile_law M roots cut rootDepth profile fuel)
  simpa only [FinDist.expect_map] using equal

end Execution

variable [DecidableEq ι]

/-- Every rooted unilateral replacement decodes without changing its opponents. -/
theorem pbsRootDecodeProfile_update
    (profile : Profile (fullInformation
      (pbsRootInformation (fullInformation M) roots)).behavioralSignature) (who : ι)
    (replacement : (fullInformation
      (pbsRootInformation (fullInformation M) roots)).BehavioralPolicy who) :
    pbsRootDecodeProfile M roots cut (Profile.update profile who replacement) =
      Profile.update (pbsRootDecodeProfile M roots cut profile) who
        (pbsRootDecodePolicy M roots cut who replacement) := by
  funext player
  by_cases same : player = who
  · subst player
    simp only [pbsRootDecodeProfile, Profile.update_same]
  · simp only [pbsRootDecodeProfile, Profile.update_of_ne _ _ same]

/-- Every ORIGINAL deviation against newly computed rooted opponents has a
matching rooted deviation, with equality of complete original-history laws. -/
theorem pbsRootDecodeProfile_unilateral_law [Fintype ι]
    (rootDepth : ∀ history ∈ roots.support, history.trace.length = cut)
    (profile : Profile (fullInformation
      (pbsRootInformation (fullInformation M) roots)).behavioralSignature) (who : ι)
    (replacement : (fullInformation M).BehavioralPolicy who) (fuel : Nat) :
    ((fullInformation (pbsRootInformation (fullInformation M) roots)).runBehavioral
      (Profile.update profile who (pbsRootBehavioralFullPolicy M roots who replacement))
      (fuel + 1)).map History.state =
        (roots.bind ((fullInformation M).runBehavioralFrom
          (Profile.update (pbsRootDecodeProfile M roots cut profile) who replacement) fuel)).map
            some := by
  rw [pbsRootDecodeProfile_law M roots cut rootDepth,
    pbsRootDecodeProfile_update, pbsRootDecodePolicy_lift]

/-- Unilateral expected payoffs agree against arbitrary newly computed opponents. -/
theorem pbsRootDecodeProfile_unilateral_expect [Fintype ι]
    (rootDepth : ∀ history ∈ roots.support, history.trace.length = cut)
    (profile : Profile (fullInformation
      (pbsRootInformation (fullInformation M) roots)).behavioralSignature) (who : ι)
    (replacement : (fullInformation M).BehavioralPolicy who) (fuel : Nat)
    (value : E.History → ℝ) :
    ((fullInformation (pbsRootInformation (fullInformation M) roots)).runBehavioral
      (Profile.update profile who (pbsRootBehavioralFullPolicy M roots who replacement))
      (fuel + 1)).expect (fun history => history.state.elim 0 value) =
        (roots.bind ((fullInformation M).runBehavioralFrom
          (Profile.update (pbsRootDecodeProfile M roots cut profile) who replacement)
          fuel)).expect value := by
  rw [pbsRootDecodeProfile_expect M roots cut rootDepth,
    pbsRootDecodeProfile_update, pbsRootDecodePolicy_lift]

end GameTheory.ReBeL
