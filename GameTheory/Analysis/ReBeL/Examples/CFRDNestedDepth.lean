/-
# Constructed nested-child and parent controls

The canonical hidden-type game has a live factual child after its first action.
The first control searches an actual parent decision and an actual child decision,
with a terminal child suffix. The second places the parent cut after chance and
retains one real child decision plus one real continuation decision. Together
these test both cut configurations without inventing a third decision in this game.
Nonzero outer bias, strictly positive child bias, finite outer counts, impossible
queries, randomized deviations and zero-own-reach completion remain explicit.
-/

import GameTheory.Analysis.ReBeL.CFRDNestedDepthDriver
import GameTheory.Analysis.ReBeL.Examples.CFRDInformationChild

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Enumerate all legal histories, including those outside factual support. -/
local instance nestedChildHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Retain the original finite menu at every local information state. -/
local instance nestedChildChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Classical equality belongs only to the real-valued reference computation. -/
local instance nestedChildInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- The child receives its own positive joint-root-dependent prediction bias. -/
def nestedChildNoise (loss : ℝ) : PBSDepthNoiseFamily (reducedModel fullPrior) :=
  pbsDepthChildHalfNoise (reducedModel fullPrior) pbsRootControlFallback 1 0 loss

/-- The child predictor is not replaced by zero to obtain the theorem. -/
theorem nestedChildNoise_positive (loss : ℝ) (positive : 0 < loss) :
    ∀ roots n trunk who info, 0 < nestedChildNoise loss roots n trunk who info :=
  pbsDepthChildHalfNoise_pos (reducedModel fullPrior) pbsRootControlFallback 1 0 loss positive

/-- Its full numerical contract is proved, not assumed in the concrete controls. -/
theorem nestedChildNoise_bounded (loss : ℝ) (positive : 0 < loss) :
    PBSDepthChildNoiseBound (reducedModel fullPrior) pbsRootControlFallback 1 0 loss
      (nestedChildNoise loss) :=
  pbsDepthChildHalfNoise_bounded (reducedModel fullPrior) pbsRootControlFallback 1 0 loss positive

/-- The actual live table calls the allocated depth solver, not the old full-root child. -/
theorem nestedChild_live_table (loss : ℝ) :
    cfrDDepthChildTable (reducedModel fullPrior) (carriedBitProfile false)
      pbsRootControlFallback 2 1 0 (fun h who => cfrPayoff who h) 2 loss (nestedChildNoise loss)
      (publicTrace (model fullPrior).toInfoSignals factualChildHistory.trace) =
    pbsInformationConditionalDepthProfile (reducedModel fullPrior) finiteBudgetControlBelief
      pbsRootControlFallback cfrPayoff 1 0 2 loss
      (nestedChildNoise loss finiteBudgetControlBelief.law) := by
  simp only [cfrDDepthChildTable, dif_pos factualChild_possible, finiteBudgetControlBelief]

/-- The parent retains its complete correlated cut law after installing the child. -/
theorem nestedChild_prefix (loss : ℝ) :
    (model fullPrior).runBehavioral
      (cfrDDepthChildProfile (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 0 (fun h who => cfrPayoff who h) 2 loss
        (nestedChildNoise loss)) 2 =
    (model fullPrior).runBehavioral (carriedBitProfile false) 2 :=
  cfrDDepthChildProfile_prefixLaw (reducedModel fullPrior) (carriedBitProfile false)
    pbsRootControlFallback 2 1 0 (fun h who => cfrPayoff who h) 2 loss (nestedChildNoise loss)

/-- A genuinely randomized replacement sees the same entire child continuation. -/
theorem nestedChild_randomized_deviation (loss : ℝ) :
    PublicBelief.continuationLaw (model fullPrior)
      (Profile.update
        (cfrDDepthChildProfile (reducedModel fullPrior) (carriedBitProfile false)
          pbsRootControlFallback 2 1 0 (fun h who => cfrPayoff who h) 2 loss
          (nestedChildNoise loss)) 0 freshBitPolicy) 1 finiteBudgetControlBelief =
    PublicBelief.continuationLaw (model fullPrior)
      (Profile.update
        (cfrDDepthChildTable (reducedModel fullPrior) (carriedBitProfile false)
          pbsRootControlFallback 2 1 0 (fun h who => cfrPayoff who h) 2 loss
          (nestedChildNoise loss)
          (publicTrace (model fullPrior).toInfoSignals factualChildHistory.trace))
        0 freshBitPolicy) 1 finiteBudgetControlBelief :=
  cfrDDepthChildProfile_deviationLaw (reducedModel fullPrior) (carriedBitProfile false)
    pbsRootControlFallback 2 1 0 (fun h who => cfrPayoff who h) 2 loss (nestedChildNoise loss)
    finiteBudgetControlBelief
    (cfrDFactualChildBelief_atCut (reducedModel fullPrior) (carriedBitProfile false)
      2 1 _ factualChild_possible) 1 0 freshBitPolicy

/-- Impossible public roots still use the explicit fallback, not a fabricated PBS. -/
theorem nestedChild_unvisited (loss : ℝ) :
    cfrDDepthChildTable (reducedModel fullPrior) (carriedBitProfile false)
      pbsRootControlFallback 2 1 0 (fun h who => cfrPayoff who h) 2 loss (nestedChildNoise loss)
      (publicTrace (model fullPrior).toInfoSignals zeroControlHistory.trace) =
    (fun who => (informationControlFullFallback who).toBehavioral) := by
  simp only [cfrDDepthChildTable, dif_neg factualChild_unvisited_absent,
    informationControlFullFallback]

/-- Exhausted fuel excludes every live child query before any solve is requested. -/
theorem nestedChild_zero_remaining (loss : ℝ) (obs : List Phase) :
    cfrDDepthChildTable (reducedModel fullPrior) (carriedBitProfile false)
      pbsRootControlFallback 2 0 0 (fun h who => cfrPayoff who h) 2 loss
      (nestedChildNoise loss) obs =
    (fun who => (informationControlFullFallback who).toBehavioral) := by
  simp only [cfrDDepthChildTable,
    dif_neg (cfrDFactualChildPossible_zero (reducedModel fullPrior) _ 2 obs),
    informationControlFullFallback]

/-- Supported and zero-own-reach reference queries share the derived loss bound. -/
theorem nestedChild_leafOptimal (loss : ℝ) (positive : 0 < loss) (who : Player) :
    CFRDLeafOptimal (model fullPrior)
      (cfrDDepthChildContinuation (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 0 (fun h player => cfrPayoff player h) 2 loss
        (nestedChildNoise loss))
      informationControlFullFallback who (cfrPayoff who) 2 1 loss :=
  cfrDDepthChildContinuation_leafOptimal (reducedModel fullPrior) (carriedBitProfile false)
    pbsRootControlFallback 2 1 0 (fun h player => cfrPayoff player h)
    (cumulative_zeroSum fullPrior) 2 loss (by norm_num) positive
    (fun h player => cfrPayoff_abs_le_two player h) (nestedChildNoise loss)
    (nestedChildNoise_bounded loss positive) who

/-- The parent's separate prediction error is the original nonzero one eighth. -/
theorem nestedChild_biased_accuracy :
    CFRDDepthAccurate (model fullPrior) decisionClock informationControlFullFallback
      cfrPayoff 2 1
      (cfrDNestedDepthOracle (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff 2 1 0 2 (1 / 4) (nestedChildNoise (1 / 4))
        (fun _ _ _ _ => 1 / 8)) (1 / 8) := by
  apply cfrDNestedDepthOracle_accurate
  intro n trunk who info
  norm_num

/-- The complete finite parent recurrence with its constructed nested children
satisfies all behavioral deviations, not merely the child belief's baseline value. -/
theorem nestedChild_driver_isNash (t : Nat) [NeZero t] :
    IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreferenceWithin
        (cfrDDepthMeanBudget (model fullPrior) decisionClock informationControlFullFallback
            2 1 2 (1 / 8) (1 / 4) 0 t +
          cfrDDepthMeanBudget (model fullPrior) decisionClock informationControlFullFallback
            2 1 2 (1 / 8) (1 / 4) 1 t)
        (fun h who => cfrPayoff who h))
      (cfrDDepthAveragedProfile (model fullPrior) decisionClock informationControlFullFallback
        cfrPayoff 2 1
        (cfrDNestedDepthOracle (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 2 1 0 2 (1 / 4) (nestedChildNoise (1 / 4))
          (fun _ _ _ _ => 1 / 8)) t) := by
  apply cfrDNestedDepthOracle_isNash (reducedModel fullPrior)
    pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior) 2 1 0
    2 (1 / 8) (1 / 4) (by norm_num) (by norm_num) (by norm_num)
    (fun player h => cfrPayoff_abs_le_two player h)
  · exact nestedChildNoise_bounded (1 / 4) (by norm_num)
  · intro n trunk who info
    norm_num

/-- A second predictor belongs to the genuinely nonempty child suffix configuration. -/
def nestedSuffixNoise (loss : ℝ) : PBSDepthNoiseFamily (reducedModel fullPrior) :=
  pbsDepthChildHalfNoise (reducedModel fullPrior) pbsRootControlFallback 1 1 loss

/-- Its nonzero prediction perturbation is preserved at every modeled root. -/
theorem nestedSuffixNoise_positive (loss : ℝ) (positive : 0 < loss) :
    ∀ roots n trunk who info, 0 < nestedSuffixNoise loss roots n trunk who info :=
  pbsDepthChildHalfNoise_pos (reducedModel fullPrior) pbsRootControlFallback 1 1 loss positive

/-- With the parent cut after chance, the child and its suffix each retain one
real decision. This complements, rather than replaces, the earlier parent-decision control. -/
theorem nestedSuffix_leafOptimal (loss : ℝ) (positive : 0 < loss) (who : Player) :
    CFRDLeafOptimal (model fullPrior)
      (cfrDDepthChildContinuation (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 1 1 1 (fun h player => cfrPayoff player h) 2 loss
        (nestedSuffixNoise loss))
      informationControlFullFallback who (cfrPayoff who) 1 2 loss :=
  cfrDDepthChildContinuation_leafOptimal (reducedModel fullPrior) (carriedBitProfile false)
    pbsRootControlFallback 1 1 1 (fun h player => cfrPayoff player h)
    (cumulative_zeroSum fullPrior) 2 loss (by norm_num) positive
    (fun h player => cfrPayoff_abs_le_two player h) (nestedSuffixNoise loss)
    (pbsDepthChildHalfNoise_bounded (reducedModel fullPrior)
      pbsRootControlFallback 1 1 loss positive) who

/-- Nonempty child continuation, distinct positive errors and finite parent rounds
also satisfy all full-game behavioral deviations through the actual coupled oracle. -/
theorem nestedSuffix_driver_isNash (t : Nat) [NeZero t] :
    IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreferenceWithin
        (cfrDDepthMeanBudget (model fullPrior) decisionClock informationControlFullFallback
            1 2 2 (1 / 8) (1 / 4) 0 t +
          cfrDDepthMeanBudget (model fullPrior) decisionClock informationControlFullFallback
            1 2 2 (1 / 8) (1 / 4) 1 t)
        (fun h who => cfrPayoff who h))
      (cfrDDepthAveragedProfile (model fullPrior) decisionClock informationControlFullFallback
        cfrPayoff 1 2
        (cfrDNestedDepthOracle (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 1 1 1 2 (1 / 4) (nestedSuffixNoise (1 / 4))
          (fun _ _ _ _ => 1 / 8)) t) := by
  apply cfrDNestedDepthOracle_isNash (reducedModel fullPrior)
    pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior) 1 1 1
    2 (1 / 8) (1 / 4) (by norm_num) (by norm_num) (by norm_num)
    (fun player h => cfrPayoff_abs_le_two player h)
  · exact pbsDepthChildHalfNoise_bounded (reducedModel fullPrior)
      pbsRootControlFallback 1 1 (1 / 4) (by norm_num)
  · intro n trunk who info
    norm_num

end GameTheory.ReBeL.Examples.HiddenTypes
