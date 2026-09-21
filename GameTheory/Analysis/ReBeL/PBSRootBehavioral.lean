/-
# Information-local behavioral laws through the joint-PBS root

The analyst's chooser refinement is connected to actual independent local
policies. Both the snapshot and complete-local-history interfaces preserve
complete execution laws. Canonical unilateral updates commute with the lift.
This direction does not assert that an arbitrary new rooted strategy has
already been decoded to an original strategy.
-/

import GameTheory.Analysis.ReBeL.PBSRootInformation
import GameTheory.Analysis.ReBeL.PBSRootExecution

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable (roots : FinDist E.History)

/-- Lift each player's law independently, without a shared hidden seed. -/
def pbsRootBehavioralProfile (profile : Profile M.behavioralSignature) :
    Profile (pbsRootInformation M roots).behavioralSignature :=
  fun who => pbsRootBehavioralPolicy M roots who (profile who)

variable [Fintype ι]

/-- The canonical behavioral chooser is exactly the previously refined chooser. -/
theorem pbsRoot_behavioralChooser (profile : Profile M.behavioralSignature) :
    (pbsRootInformation M roots).randomizedChooser (pbsRootBehavioralProfile M roots profile) =
      pbsRootChooser roots (M.randomizedChooser profile) := by
  funext history nonterminal
  rcases history with ⟨state, trace⟩
  cases trace with
  | start =>
      exact (pbsRootInformation M roots).behavioralJoint_eq_pure_of_no_active
        (pbsRootBehavioralProfile M roots profile) .start nonterminal (fun _ => not_false)
  | @extend source target prior joint legal realized =>
      cases target with
      | none =>
          exact (pbsRootInformation M roots).behavioralJoint_eq_pure_of_no_active
            (pbsRootBehavioralProfile M roots profile)
            (.extend prior joint legal realized) nonterminal (fun _ => not_false)
      | some original => rfl

/-- At a retained original history the entire legal joint-action law agrees. -/
theorem pbsRoot_behavioralJoint_some (profile : Profile M.behavioralSignature)
    (original : E.History) (trace : (pbsRootProtocol roots).Trace (some original))
    (nonterminal : ¬ E.terminal original.state) :
    (pbsRootInformation M roots).behavioralJoint (pbsRootBehavioralProfile M roots profile)
      trace nonterminal = M.behavioralJoint profile original.trace nonterminal :=
  congrFun (congrFun (pbsRoot_behavioralChooser M roots profile) ⟨some original, trace⟩)
    nonterminal

/-- Every original behavioral profile has exactly the original continuation law
under actual local execution in the newly rooted game. -/
theorem pbsRoot_behavioral_law (profile : Profile M.behavioralSignature) (fuel : Nat) :
    ((pbsRootInformation M roots).runBehavioral (pbsRootBehavioralProfile M roots profile)
      (fuel + 1)).map History.state =
      (roots.bind (M.runBehavioralFrom profile fuel)).map some := by
  simp only [runBehavioral, runBehavioralFrom, pbsRoot_behavioralChooser]
  exact pbsRoot_run_initial roots (M.randomizedChooser profile) fuel

/-- Retain the complete subsequent local history while reading only its own
original AOH snapshot. Every syntactic information state still has a legal law. -/
def pbsRootBehavioralFullPolicy (who : ι) (policy : (fullInformation M).BehavioralPolicy who) :
    (fullInformation (pbsRootInformation (fullInformation M) roots)).BehavioralPolicy who :=
  fun info => pbsRootBehavioralPolicy (fullInformation M) roots who policy
    (reduceAOH (pbsRootInformation (fullInformation M) roots).toInfoSignals who info)

/-- The full-interface lift is coordinatewise, including off-policy choices. -/
def pbsRootBehavioralFullProfile (profile : Profile (fullInformation M).behavioralSignature) :
    Profile (fullInformation (pbsRootInformation (fullInformation M) roots)).behavioralSignature :=
  fun who => pbsRootBehavioralFullPolicy M roots who (profile who)

/-- Refining local memory does not alter the independent action product. -/
theorem pbsRoot_behavioralFullChooser
    (profile : Profile (fullInformation M).behavioralSignature) :
    (fullInformation (pbsRootInformation (fullInformation M) roots)).randomizedChooser
        (pbsRootBehavioralFullProfile M roots profile) =
      (pbsRootInformation (fullInformation M) roots).randomizedChooser
        (pbsRootBehavioralProfile (fullInformation M) roots profile) := by
  funext history nonterminal
  rcases history with ⟨state, trace⟩
  cases trace <;> rfl

/-- All original full-AOH behavioral laws, not a restricted plan family, embed
in the full interface used by the information-set CFR construction. -/
theorem pbsRoot_behavioralFull_law
    (profile : Profile (fullInformation M).behavioralSignature) (fuel : Nat) :
    ((fullInformation (pbsRootInformation (fullInformation M) roots)).runBehavioral
      (pbsRootBehavioralFullProfile M roots profile) (fuel + 1)).map History.state =
      (roots.bind ((fullInformation M).runBehavioralFrom profile fuel)).map some := by
  simp only [runBehavioral, runBehavioralFrom, pbsRoot_behavioralFullChooser,
    pbsRoot_behavioralChooser]
  exact pbsRoot_run_initial roots ((fullInformation M).randomizedChooser profile) fuel

variable [DecidableEq ι]

omit [Fintype ι] in
/-- Canonical unilateral replacement changes exactly the corresponding local
rooted policy; it does not resample or modify the other player's strategy. -/
theorem pbsRootBehavioralFullProfile_update
    (profile : Profile (fullInformation M).behavioralSignature) (who : ι)
    (deviation : (fullInformation M).BehavioralPolicy who) :
    pbsRootBehavioralFullProfile M roots (Profile.update profile who deviation) =
      Profile.update (pbsRootBehavioralFullProfile M roots profile) who
        (pbsRootBehavioralFullPolicy M roots who deviation) := by
  funext player
  by_cases same : player = who
  · subst player
    simp only [pbsRootBehavioralFullProfile, Profile.update_same]
  · simp only [pbsRootBehavioralFullProfile, Profile.update_of_ne _ _ same]

/-- The exact execution identity also holds after every unilateral behavioral
replacement, with the same original joint PBS and fuel. -/
theorem pbsRoot_behavioralFull_unilateral_law
    (profile : Profile (fullInformation M).behavioralSignature) (who : ι)
    (deviation : (fullInformation M).BehavioralPolicy who) (fuel : Nat) :
    ((fullInformation (pbsRootInformation (fullInformation M) roots)).runBehavioral
      (Profile.update (pbsRootBehavioralFullProfile M roots profile) who
        (pbsRootBehavioralFullPolicy M roots who deviation)) (fuel + 1)).map History.state =
      (roots.bind ((fullInformation M).runBehavioralFrom
        (Profile.update profile who deviation) fuel)).map some := by
  rw [← pbsRootBehavioralFullProfile_update]
  exact pbsRoot_behavioralFull_law M roots (Profile.update profile who deviation) fuel

end GameTheory.ReBeL
