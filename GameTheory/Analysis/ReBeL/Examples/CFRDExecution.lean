/-
# Actual depth-limited finite-iteration controls

The control uses the established two-stage hidden-type protocol and the actual
coupled CFR-D driver. Its declared pure zero-regret fallback is not relabeled
as the paper's uniform initialization. Zero leaf error does not remove the
finite-iteration term even for this completely specified accepted variant.
-/

import GameTheory.Analysis.ReBeL.CFRDCarriedPlay
import GameTheory.Analysis.ReBeL.Examples.CFRNash

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

local instance : Fintype (protocol fullPrior).History := historyFintype fullPrior
local instance (who : Player) : DecidableEq ((model fullPrior).InfoState who) :=
  Classical.decEq _
local instance (who : Player) (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- The complete baseline profile fixes the canonical behavioral signature. -/
def cfrDControlBaseline : Profile (model fullPrior).behavioralSignature :=
  fun who => (cfrFallback who).toBehavioral

/-- The exact reference oracle with the established baseline continuation. -/
def cfrDControlOracle : CFRDValueOracle (model fullPrior) :=
  cfrDExactValueOracle (model fullPrior) decisionClock cfrFallback cfrPayoff 3 0
    (fun _ _ who => (cfrFallback who).toBehavioral)

/-- The numerical accuracy premise is proved at zero error, not postulated. -/
theorem cfrDControl_exact :
    CFRDDepthAccurate (model fullPrior) decisionClock cfrFallback cfrPayoff 3 0
      cfrDControlOracle 0 :=
  cfrDExactValueOracle_accurate (model fullPrior) decisionClock cfrFallback cfrPayoff 3 0 _

/-- No continuation remains at this full-search boundary. -/
theorem cfrDControl_leaf_optimal :
    CFRDDepthLeafOptimal (model fullPrior) decisionClock cfrFallback cfrPayoff 3 0
      cfrDControlOracle 0 := by
  intro n who
  exact cfrDLeafOptimal_zero_remaining (model fullPrior) _ cfrFallback who (cfrPayoff who) 3

/-- The actual first round is the declared zero-regret fallback profile. -/
theorem cfrDControl_initial :
    cfrDDepthPlay (model fullPrior) decisionClock cfrFallback cfrPayoff 3 0
      cfrDControlOracle 0 = fun who => (cfrFallback who).toBehavioral := by
  have zero : cfrProfile (model fullPrior) cfrFallback (fun _ _ => 0) =
      fun who => (cfrFallback who).toBehavioral := by
    funext who info
    unfold cfrProfile
    split <;> simp [Policy.toBehavioral]
  unfold cfrDDepthPlay cfrDPlay cfrDProfile cfrDQuery cfrDState cfrDDepthOracle
  simp only [zero, cfrDControlOracle, cfrDExactValueOracle]
  funext who info
  split <;> rfl

/-- Averaging one completed round cannot manufacture a different strategy. -/
theorem cfrDControl_average_one :
    cfrDDepthAveragedProfile (model fullPrior) decisionClock cfrFallback cfrPayoff 3 0
      cfrDControlOracle 1 = fun who => (cfrFallback who).toBehavioral := by
  have same (n : Fin 1) :
      cfrDDepthPlay (model fullPrior) decisionClock cfrFallback cfrPayoff 3 0
        cfrDControlOracle n.val = fun who => (cfrFallback who).toBehavioral := by
    have hn : n.val = 0 := by omega
    rw [hn, cfrDControl_initial]
  funext who info
  unfold cfrDDepthAveragedProfile ownReachAverageProfile ownReachAveragePolicy
  simp_rw [same]
  unfold ReachWeights.average
  split <;> simp only [FinDist.bind_const, Policy.toBehavioral]

/-- Player one changes its first simultaneous decision, without reading the
other player's type or action. Its second-stage choices remain unchanged. -/
def cfrDControlDeviation : Plan where
  first _ := true
  second _ _ := true

/-- The deviation is an actual complete information-local behavioral policy. -/
def cfrDControlAlternative : (model fullPrior).BehavioralPolicy 1 :=
  (fullPlanPolicy fullPrior 1 cfrDControlDeviation).toBehavioral

/-- The changed profile is exactly the canonical unilateral profile update. -/
theorem cfrDControl_profile_update :
    Profile.update cfrDControlBaseline 1 cfrDControlAlternative =
      fun who => (fullPlanPolicy fullPrior who
        (if who = 1 then cfrDControlDeviation else baselinePlans who)).toBehavioral := by
  funext who
  rcases (by decide : ∀ player : Fin 2, player = 0 ∨ player = 1) who with rfl | rfl
  · simp [cfrDControlBaseline, cfrFallback]
  · simp [cfrDControlAlternative]

/-- A profitable deviation is calculated in the original game, not in a
separate payoff table. The hidden chance distribution cancels pointwise. -/
theorem cfrDControl_gain_two :
    ((model fullPrior).runBehavioral
        (Profile.update cfrDControlBaseline
          1 cfrDControlAlternative) 3).expect (cfrPayoff 1) -
      ((model fullPrior).runBehavioral
        (fun who => (cfrFallback who).toBehavioral) 3).expect (cfrPayoff 1) = 2 := by
  rw [cfrDControl_profile_update]
  have first := rootValue_formula fullPrior
    (fun who => if who = 1 then cfrDControlDeviation else baselinePlans who) 1
  have base := rootValue_formula fullPrior baselinePlans 1
  dsimp only [rootValue, policyValue, expectedUtility, InformationModel.toBehavioralGameForm]
    at first base
  rw [show ((model fullPrior).runBehavioral
      (fun who => (fullPlanPolicy fullPrior who
        (if who = 1 then cfrDControlDeviation else baselinePlans who)).toBehavioral) 3).expect
        (cfrPayoff 1) = _ from first,
    show ((model fullPrior).runBehavioral (fun who => (cfrFallback who).toBehavioral) 3).expect
        (cfrPayoff 1) = _ from base]
  rw [← FinDist.expect_sub]
  calc
    _ = fullPrior.expect (fun _ => (2 : ℝ)) := by
      apply FinDist.expect_congr
      rintro ⟨a, b⟩ _
      cases a <;> cases b <;> norm_num [potential, signed, firstResult, finalResult,
        firstJoint, secondJoint, action, baselinePlans, correlationPlans,
        cfrDControlDeviation, ownType, winValue]
    _ = 2 := FinDist.expect_const _ _

/-- A machine-checked finite-T obstruction for the actual declared solver:
exact leaf evaluation and no continuation loss do not imply exact Nash at T=1. -/
theorem cfrDControl_one_not_nash :
    ¬ IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreference (fun history who => cfrPayoff who history))
      (cfrDDepthAveragedProfile (model fullPrior) decisionClock cfrFallback cfrPayoff 3 0
        cfrDControlOracle 1) := by
  rw [cfrDControl_average_one]
  intro hnash
  have h : ((model fullPrior).runBehavioral
      (Profile.update cfrDControlBaseline 1 cfrDControlAlternative)
        3).expect (cfrPayoff 1) ≤
      ((model fullPrior).runBehavioral (fun who => (cfrFallback who).toBehavioral) 3).expect
        (cfrPayoff 1) :=
    (isNash_iff (F := (model fullPrior).toBehavioralGameForm 3)
      (weaklyPrefers := euPreference (fun history who => cfrPayoff who history)) _).mp
        hnash 1 cfrDControlAlternative
  linarith [cfrDControl_gain_two]

/-- Positive control: the actual solver still satisfies its proved nonzero
finite-time bound at every positive iteration count. -/
theorem cfrDControl_finite_bound (t : Nat) [NeZero t] :
    IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreferenceWithin
        (cfrDDepthMeanBudget (model fullPrior) decisionClock cfrFallback 3 0 2 0 0 0 t +
          cfrDDepthMeanBudget (model fullPrior) decisionClock cfrFallback 3 0 2 0 0 1 t)
        (fun history who => cfrPayoff who history))
      (cfrDDepthAveragedProfile (model fullPrior) decisionClock cfrFallback cfrPayoff 3 0
        cfrDControlOracle t) := by
  exact cfrDDepth_fullSearch_isNash (model fullPrior) decisionClock
    (perfectRecall fullPrior) cfrFallback cfrPayoff (cumulative_zeroSum fullPrior) 3 2
    (by norm_num) cfrPayoff_abs_le_two _ t

end GameTheory.ReBeL.Examples.HiddenTypes
