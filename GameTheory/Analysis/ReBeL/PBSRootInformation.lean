/-
# Information-local play in a PBS-rooted protocol

A sampled hidden root is not a policy argument. Each player receives only the
original public trace and its own information state. Applying this constructor
to the full-AOH model exposes its own complete AOH, not the joint hidden history.
The optional administrative state has the singleton no-op menu.
-/

import GameTheory.Analysis.ReBeL.PBSRootProtocol
import GameTheory.ReBeL.Adapter

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Original local snapshots; the hidden root is absent from every signal type. -/
def pbsRootSignals (roots : FinDist E.History) : InfoSignals (pbsRootProtocol roots) where
  PublicSignal := Option (List M.PublicSignal)
  PrivateSignal who := Option (M.InfoState who)
  initialPublic := none
  initialPrivate _ := none
  publicSignal event := event.target.map (fun h => publicTrace M.toInfoSignals h.trace)
  privateSignal who event := event.target.map (fun h => M.infoOf who h.trace)
  InfoState who := Option (M.InfoState who)
  initInfo _ _ _ := none
  pushInfo _ _ _ privateObservation _ := privateObservation

/-- At every rooted legal trace the snapshot is the original player's own view. -/
theorem pbsRootSignals_infoOf (roots : FinDist E.History) (who : ι)
    {state : (pbsRootProtocol roots).State} (trace : (pbsRootProtocol roots).Trace state) :
    (pbsRootSignals M roots).infoOf who trace =
      state.map (fun h => M.infoOf who h.trace) := by
  cases trace <;> rfl

/-- Reuse the original information-local menus without receiving a hidden state. -/
def pbsRootInformation (roots : FinDist E.History) :
    InformationModel (pbsRootProtocol roots) where
  toInfoSignals := pbsRootSignals M roots
  menu who info := match info with
    | none => {none}
    | some original => M.menu who original
  menu_adequate := by
    intro who state trace choice
    rw [pbsRootSignals_infoOf]
    cases state with
    | none => cases choice <;> simp [LegalOption, pbsRootProtocol]
    | some history => exact M.menu_adequate who history.trace choice

/-- No policy needs a world-state argument to continue from its original view. -/
def pbsRootPolicy (roots : FinDist E.History) (who : ι) (policy : M.Policy who) :
    (pbsRootInformation M roots).Policy who
  | none => ⟨none, rfl⟩
  | some info => policy info

/-- The same adapter preserves independent behavioral randomization. -/
def pbsRootBehavioralPolicy (roots : FinDist E.History) (who : ι)
    (policy : M.BehavioralPolicy who) : (pbsRootInformation M roots).BehavioralPolicy who
  | none => FinDist.pure ⟨none, rfl⟩
  | some info => policy info

/-- At a sampled root, the legal choice law is exactly the original local law. -/
theorem pbsRootBehavioralPolicy_some (roots : FinDist E.History) (who : ι)
    (policy : M.BehavioralPolicy who) (info : M.InfoState who) :
    pbsRootBehavioralPolicy M roots who policy (some info) = policy info := rfl

/-- Roots that the original player cannot distinguish remain indistinguishable
under the snapshot interface, including original off-policy histories. -/
theorem pbsRootSignals_equal_of_original_equal (roots : FinDist E.History) (who : ι)
    (first second : E.History) (hinfo : M.infoOf who first.trace = M.infoOf who second.trace)
    (firstTrace : (pbsRootProtocol roots).Trace (some first))
    (secondTrace : (pbsRootProtocol roots).Trace (some second)) :
    (pbsRootSignals M roots).infoOf who firstTrace =
      (pbsRootSignals M roots).infoOf who secondTrace := by
  rw [pbsRootSignals_infoOf, pbsRootSignals_infoOf]
  exact congrArg some hinfo

end GameTheory.ReBeL
