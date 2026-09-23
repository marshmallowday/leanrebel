/-
# Noisy depth-limited carried-root controls

The new PBS starts before both strategic rounds of the canonical hidden-type
game. One round is searched in the trunk and one remains in the computed child.
Prediction bias is 1/8, child tolerance is 1/4, and outer counts remain finite.
-/

import GameTheory.Analysis.ReBeL.PBSCarriedDepth
import GameTheory.Analysis.ReBeL.Examples.PBSCarriedSampling

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Reuse the canonical exhaustive history enumeration. -/
local instance depthControlHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- A four-outcome joint PBS before either strategic round. Every outcome
retains its original legal history and shares the same public observation. -/
def depthControlBelief : PublicBelief (model fullPrior).toInfoSignals
    (publicTrace (model fullPrior).toInfoSignals (fullDraw (false, false)).trace) where
  law := (cfrIterationLaw 4).map fun n =>
    fullDraw (decide (n.val % 2 = 1), decide (n.val / 2 = 1))
  supported := by
    intro history member
    rw [FinDist.support_map] at member
    obtain ⟨n, _, rfl⟩ := member
    fin_cases n <;> rfl

/-- Nonzero perturbation at every modeled rooted information query. -/
def depthControlNoise : PBSCarriedDepthNoise (reducedModel fullPrior) :=
  fun _ _ _ _ _ => 1 / 8

/-- A real first-round input retains the modeled joint root, not a hidden-state oracle. -/
def depthControlState : PrivateIterationState (model fullPrior) Unit where
  iteration := ()
  history := fullDraw (false, false)
  belief := some depthControlBelief

/-- The execution root is live, with both strategic rounds still ahead. -/
theorem rootedDepth_live_root : cfrDCutLive 1 depthControlState.history = true := by
  classical
  rw [cfrDCutLive, decide_eq_true_eq]
  exact ⟨by decide, fun impossible => impossible⟩

/-- The finite solver tolerances used by the controls are genuinely positive. -/
theorem rootedDepth_positive_errors : (0 : ℝ) < 1 / 8 ∧ (0 : ℝ) < 1 / 4 := by norm_num

/-- This is the constructed two-stage game's all-deviation guarantee, not an
input equilibrium certificate. The error budget is kept instead of rounded away. -/
theorem rootedDepth_two_stage_nash (t : Nat) [NeZero t] :
    IsNash (behavioralBeliefForm (model fullPrior) depthControlBelief 2)
      (euPreferenceWithin
        (pbsRootDepthBudget (reducedModel fullPrior) depthControlBelief.law
          pbsRootControlFallback 1 1 2 (1 / 8) (1 / 4) t)
        (fun history who => cfrPayoff who history))
      (pbsInformationDepthCFR (reducedModel fullPrior) depthControlBelief
        pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
        (depthControlNoise depthControlBelief.law) t) := by
  apply pbsInformationDepthCFR_isNash (reducedModel fullPrior) depthControlBelief
    pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior) 1 1 2 (1 / 8) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) cfrPayoff_abs_le_two
  intro n trunk who info
  norm_num [depthControlNoise]

/-- Computed iterates remain local: player zero cannot read the other hidden
bit even though the joint PBS contains histories with both of its values. -/
theorem rootedDepth_iterate_no_hidden_leak (round : Nat) :
    pbsInformationDepthCFRIterate (reducedModel fullPrior) depthControlBelief
        pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
        (depthControlNoise depthControlBelief.law) round 0
        ((model fullPrior).infoOf 0 (fullDraw (false, false)).trace) =
      pbsInformationDepthCFRIterate (reducedModel fullPrior) depthControlBelief
        pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
        (depthControlNoise depthControlBelief.law) round 0
        ((model fullPrior).infoOf 0 (fullDraw (false, true)).trace) := rfl

/-- Arbitrary seed-blind opponents receive the same complete modeled history
law from actual noisy parent-iteration sampling and own-reach averaging. -/
theorem rootedDepth_sampled_law
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (t : Nat) [NeZero t] :
    (cfrIterationLaw t).bind (fun n => depthControlBelief.law.bind
      ((model fullPrior).runBehavioralFrom (Profile.update unknown who
        (pbsInformationDepthCFRIterate (reducedModel fullPrior) depthControlBelief
          pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
          (depthControlNoise depthControlBelief.law) n.val who)) 2)) =
      depthControlBelief.law.bind ((model fullPrior).runBehavioralFrom
        (Profile.update unknown who (pbsInformationDepthCFR (reducedModel fullPrior)
          depthControlBelief pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
          (depthControlNoise depthControlBelief.law) t who)) 2) :=
  pbsInformationDepthCFR_sampling_law (reducedModel fullPrior) depthControlBelief
    pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4) (depthControlNoise depthControlBelief.law)
    t unknown who 2

/-- A fresh solve uses its incoming joint belief, irrespective of the previous
selected policy, while preserving the same numerical perturbation family. -/
theorem rootedDepth_uses_incoming_belief :
    pbsCarriedDepthResolver (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
        1 1 2 (1 / 4) depthControlNoise 2 (fun _ : Unit => carriedBitProfile false)
        () _ (some depthControlBelief) =
      pbsCarriedDepthResolver (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
        1 1 2 (1 / 4) depthControlNoise 2 (fun _ : Unit => carriedBitProfile true)
        () _ (some depthControlBelief) := rfl

/-- Actual first-round execution retains each chosen depth-limited iterate
paired with the PBS propagated through it. The posterior is not reset to average. -/
theorem rootedDepth_joint_step
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    carriedResolvedStep (model fullPrior) (fun _ : Unit => carriedBitProfile false)
      (pbsCarriedDepthResolver (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
        1 1 2 (1 / 4) depthControlNoise 2 (fun _ : Unit => carriedBitProfile false))
      unknown who 1 depthControlState =
      (cfrIterationLaw 2).bind (fun n =>
        ((model fullPrior).runBehavioralFrom (Profile.update unknown who
          (pbsInformationDepthCFRIterate (reducedModel fullPrior) depthControlBelief
            pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
            (depthControlNoise depthControlBelief.law) n.val who))
          1 depthControlState.history).map (resolvedNextState (model fullPrior) depthControlState
            (pbsInformationDepthCFRIterate (reducedModel fullPrior) depthControlBelief
              pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
              (depthControlNoise depthControlBelief.law) n.val) 1)) :=
  pbsCarriedDepthResolver_step_some (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
    1 1 2 (1 / 4) depthControlNoise 2 (fun _ : Unit => carriedBitProfile false)
    unknown who 1 depthControlState depthControlBelief rfl rootedDepth_live_root

/-- A missing posterior retains the old continuation, with no fabricated root. -/
theorem rootedDepth_missing_belief :
    pbsCarriedDepthResolver (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
        1 1 2 (1 / 4) depthControlNoise 2 (fun _ : Unit => carriedBitProfile false) ()
        (publicTrace (model fullPrior).toInfoSignals depthControlState.history.trace) none =
      FinDist.pure (carriedBitProfile false) := rfl

/-- Zero allowed transitions bypass the solver even at this live two-stage root. -/
theorem rootedDepth_zero_fuel
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    carriedResolvedTail (model fullPrior)
        (pbsCarriedDepthResolver (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
          1 1 2 (1 / 4) depthControlNoise 2 (fun _ : Unit => carriedBitProfile false))
        unknown who 0 depthControlState = FinDist.pure depthControlState.history := by
  simp only [carriedResolvedTail, cfrDCutLive_zero, Bool.false_eq_true, if_false]

/-- Successive solves use different outer counts and local search cuts; both
execute through the existing retained-memory runner rather than resetting state. -/
def depthControlStages : List (CarriedResolveStage (model fullPrior) Unit) :=
  [pbsCarriedDepthStage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
      1 1 1 2 (1 / 4) depthControlNoise 2 (fun _ : Unit => carriedBitProfile false),
    pbsCarriedDepthStage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
      0 1 1 2 (1 / 4) depthControlNoise 3 (fun _ : Unit => carriedBitProfile false)]

/-- Administrative root draws and training horizons do not inflate execution fuel. -/
theorem rootedDepth_schedule_fuel :
    carriedResolveFuel (model fullPrior) 0 depthControlStages = 2 := rfl

end GameTheory.ReBeL.Examples.HiddenTypes
