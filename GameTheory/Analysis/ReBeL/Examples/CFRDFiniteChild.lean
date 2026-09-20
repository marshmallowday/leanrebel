/-
# Finite child, off-path and perturbed-driver controls

The live child is the new finite-budget construction, not the exact Nash
reference. Nonfactual and terminal public observations do not acquire factual
posteriors. The positive child tolerance and numerical bias are kept distinct.
-/

import GameTheory.Analysis.ReBeL.CFRDFiniteDriver
import GameTheory.Analysis.ReBeL.Examples.PBSFinitePlanSolver

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Actual canonical finite history enumeration. -/
local instance finiteChildHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Legal local choices, including inactive singleton menus. -/
local instance finiteChildChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Information equality for the actual coupled outer recurrence. -/
local instance finiteChildInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- Finite child policies cannot change the observed first-round joint law. -/
theorem finiteChildControl_prefix (loss : ℝ) :
    (model fullPrior).runBehavioral
        (cfrDFiniteChildProfile (reducedModel fullPrior) (carriedBitProfile false)
          cfrFallback 2 1 (fun h who => cfrPayoff who h) 2 loss) 2 =
      (model fullPrior).runBehavioral (carriedBitProfile false) 2 :=
  cfrDFiniteChildProfile_prefixLaw (reducedModel fullPrior) (carriedBitProfile false)
    cfrFallback 2 1 (fun h who => cfrPayoff who h) 2 loss

/-- A counterfactual-only public root is not sent to a fabricated factual solve. -/
theorem finiteChildControl_unvisited (loss : ℝ) :
    cfrDFiniteChildTable (reducedModel fullPrior) (carriedBitProfile false) cfrFallback 2 1
        (fun h who => cfrPayoff who h) 2 loss
        (publicTrace (model fullPrior).toInfoSignals zeroControlHistory.trace) =
      (fun who => (cfrFallback who).toBehavioral) := by
  simp only [cfrDFiniteChildTable, dif_neg factualChild_unvisited_absent]

/-- No zero-remaining-fuel leaf is wrongly reclassified as a live child game. -/
theorem finiteChildControl_zero_remaining (loss : ℝ) (obs : List Phase) :
    cfrDFiniteChildTable (reducedModel fullPrior) (carriedBitProfile false) cfrFallback 2 0
        (fun h who => cfrPayoff who h) 2 loss obs =
      (fun who => (cfrFallback who).toBehavioral) := by
  simp only [cfrDFiniteChildTable,
    dif_neg (cfrDFactualChildPossible_zero (reducedModel fullPrior) _ 2 obs)]

/-- The actual live finite child and off-path completion meet the all-query
contract with any positive tolerance; no child equilibrium is assumed. -/
theorem finiteChildControl_leafOptimal (loss : ℝ) (positive : 0 < loss) (who : Player) :
    CFRDLeafOptimal (model fullPrior)
      (cfrDFiniteContinuation (reducedModel fullPrior) (carriedBitProfile false)
        cfrFallback 2 1 (fun h player => cfrPayoff player h) 2 loss)
      cfrFallback who (cfrPayoff who) 2 1 loss :=
  cfrDFiniteContinuation_leafOptimal (reducedModel fullPrior) (carriedBitProfile false)
    cfrFallback 2 1 (fun h player => cfrPayoff player h) (cumulative_zeroSum fullPrior)
    2 loss (by norm_num) positive (fun h player => cfrPayoff_abs_le_two player h) who

/-- Every actual parent iterate uses its finite children with the requested loss. -/
theorem finiteChildControl_driver_leafOptimal (loss : ℝ) (positive : 0 < loss)
    (noise : CFRDPredictionNoise (reducedModel fullPrior)) :
    CFRDDepthLeafOptimal (model fullPrior) decisionClock cfrFallback cfrPayoff 2 1
      (cfrDConstructedFiniteOracle (reducedModel fullPrior) cfrFallback cfrPayoff 2 1
        2 loss noise) loss :=
  cfrDConstructedFiniteOracle_leafOptimal (reducedModel fullPrior) cfrFallback cfrPayoff
    (cumulative_zeroSum fullPrior) 2 1 2 loss (by norm_num) positive
    (fun player h => cfrPayoff_abs_le_two player h) noise

/-- A nonzero numerical bias is separate from the finite child tolerance. -/
theorem finiteChildControl_biased_accuracy :
    CFRDDepthAccurate (model fullPrior) decisionClock cfrFallback cfrPayoff 2 1
      (cfrDConstructedFiniteOracle (reducedModel fullPrior) cfrFallback cfrPayoff 2 1
        2 (1 / 4) (fun _ _ _ _ => 1 / 8)) (1 / 8) := by
  apply cfrDConstructedFiniteOracle_accurate
  intro n trunk who info
  norm_num

/-- Full-game approximate Nash for the perturbed finite-child driver; its
outer finite-T term and positive child tolerance have not been dropped. -/
theorem finiteChildControl_driver_isNash (t : Nat) [NeZero t] :
    IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreferenceWithin
        (cfrDDepthMeanBudget (model fullPrior) decisionClock cfrFallback 2 1 2 (1 / 8) (1 / 4) 0 t +
          cfrDDepthMeanBudget (model fullPrior) decisionClock cfrFallback 2 1 2 (1 / 8) (1 / 4) 1 t)
        (fun h who => cfrPayoff who h))
      (cfrDDepthAveragedProfile (model fullPrior) decisionClock cfrFallback cfrPayoff 2 1
        (cfrDConstructedFiniteOracle (reducedModel fullPrior) cfrFallback cfrPayoff 2 1
          2 (1 / 4) (fun _ _ _ _ => 1 / 8)) t) := by
  apply cfrDConstructedFiniteOracle_isNash (reducedModel fullPrior) cfrFallback cfrPayoff
    (cumulative_zeroSum fullPrior) 2 1 2 (1 / 8) (1 / 4) (by norm_num) (by norm_num)
    (by norm_num) (fun player h => cfrPayoff_abs_le_two player h)
  intro n trunk who info
  norm_num

end GameTheory.ReBeL.Examples.HiddenTypes
