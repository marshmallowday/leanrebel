/-
# Information-set child, counterfactual and noisy-parent controls

A live canonical hidden-type PBS exercises the actual information-set backend.
Controls cover positive budgets, complete joint laws, a randomized unilateral
replacement, impossible queries, zero remaining fuel and a biased parent trace.
-/

import GameTheory.Analysis.ReBeL.CFRDInformationDriver
import GameTheory.Analysis.ReBeL.Examples.PBSRootDecode

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Use all canonical legal histories, not just one selected policy's support. -/
local instance informationChildHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Include every finite local menu, including inactive singleton choices. -/
local instance informationChildChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Equality is confined to the abstract real-valued reference learner. -/
local instance informationChildInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- The original local fallback is explicitly lifted to the full-AOH interface. -/
def informationControlFullFallback : Profile (model fullPrior).strategicSignature :=
  cfrDInformationFallback (reducedModel fullPrior) pbsRootControlFallback

/-- The derived count is positive even outside the positive-error guarantee. -/
theorem informationChildControl_rounds_positive (error : ℝ) :
    0 < pbsInformationBudgetRounds (reducedModel fullPrior)
      finiteBudgetControlBelief.law (fun _ => 2) 1 error :=
  Nat.pos_of_ne_zero (NeZero.ne _)

/-- A prescribed positive error is met by an actual information-set solve at
this live posterior, without receiving an equilibrium certificate. -/
theorem informationChildControl_live_budget (error : ℝ) (positive : 0 < error) :
    IsNash (behavioralBeliefForm (model fullPrior) finiteBudgetControlBelief 1)
      (euPreferenceWithin error (fun h who => cfrPayoff who h))
      (pbsInformationBudgetProfile (reducedModel fullPrior) finiteBudgetControlBelief
        pbsRootControlFallback 1 (fun h who => cfrPayoff who h) 2 error) :=
  pbsInformationBudgetProfile_isNash (reducedModel fullPrior) finiteBudgetControlBelief
    pbsRootControlFallback 1 (fun h who => cfrPayoff who h) (cumulative_zeroSum fullPrior)
    2 (by norm_num) (fun h who => cfrPayoff_abs_le_two who h) error positive

/-- The live table really calls the information-set solver at the factual PBS. -/
theorem informationChildControl_live_table (loss : ℝ) :
    cfrDInformationChildTable (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 (fun h who => cfrPayoff who h) 2 loss
        (publicTrace (model fullPrior).toInfoSignals factualChildHistory.trace) =
      pbsInformationConditionalProfile (reducedModel fullPrior) finiteBudgetControlBelief
        pbsRootControlFallback 1 (fun h who => cfrPayoff who h) 2 loss := by
  simp only [cfrDInformationChildTable, dif_pos factualChild_possible,
    finiteBudgetControlBelief]

/-- The new child preserves the observed first-round joint law. -/
theorem informationChildControl_prefix (loss : ℝ) :
    (model fullPrior).runBehavioral
        (cfrDInformationChildProfile (reducedModel fullPrior) (carriedBitProfile false)
          pbsRootControlFallback 2 1 (fun h who => cfrPayoff who h) 2 loss) 2 =
      (model fullPrior).runBehavioral (carriedBitProfile false) 2 :=
  cfrDInformationChildProfile_prefixLaw (reducedModel fullPrior) (carriedBitProfile false)
    pbsRootControlFallback 2 1 (fun h who => cfrPayoff who h) 2 loss

/-- A randomized unilateral replacement preserves the entire actual child law,
not just the baseline's expected payoff. -/
theorem informationChildControl_randomized_deviation (loss : ℝ) :
    PublicBelief.continuationLaw (model fullPrior)
      (Profile.update
        (cfrDInformationChildProfile (reducedModel fullPrior) (carriedBitProfile false)
          pbsRootControlFallback 2 1 (fun h who => cfrPayoff who h) 2 loss)
        0 freshBitPolicy) 1 finiteBudgetControlBelief =
      PublicBelief.continuationLaw (model fullPrior)
        (Profile.update
          (cfrDInformationChildTable (reducedModel fullPrior) (carriedBitProfile false)
            pbsRootControlFallback 2 1 (fun h who => cfrPayoff who h) 2 loss
            (publicTrace (model fullPrior).toInfoSignals factualChildHistory.trace))
          0 freshBitPolicy) 1 finiteBudgetControlBelief :=
  cfrDInformationChildProfile_deviationLaw (reducedModel fullPrior) (carriedBitProfile false)
    pbsRootControlFallback 2 1 (fun h who => cfrPayoff who h) 2 loss finiteBudgetControlBelief
    (cfrDFactualChildBelief_atCut (reducedModel fullPrior) (carriedBitProfile false)
      2 1 _ factualChild_possible) 1 0 freshBitPolicy

/-- An unvisited public observation does not acquire a fabricated posterior. -/
theorem informationChildControl_unvisited (loss : ℝ) :
    cfrDInformationChildTable (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 (fun h who => cfrPayoff who h) 2 loss
        (publicTrace (model fullPrior).toInfoSignals zeroControlHistory.trace) =
      (fun who => (informationControlFullFallback who).toBehavioral) := by
  simp only [cfrDInformationChildTable, dif_neg factualChild_unvisited_absent,
    informationControlFullFallback]

/-- Zero remaining fuel never queries a fictitious live child. -/
theorem informationChildControl_zero_remaining (loss : ℝ) (obs : List Phase) :
    cfrDInformationChildTable (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 0 (fun h who => cfrPayoff who h) 2 loss obs =
      (fun who => (informationControlFullFallback who).toBehavioral) := by
  simp only [cfrDInformationChildTable,
    dif_neg (cfrDFactualChildPossible_zero (reducedModel fullPrior) _ 2 obs),
    informationControlFullFallback]

/-- Live and zero-own-reach queries both receive the actual constructed contract. -/
theorem informationChildControl_leafOptimal (loss : ℝ) (positive : 0 < loss)
    (who : Player) :
    CFRDLeafOptimal (model fullPrior)
      (cfrDInformationContinuation (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 (fun h player => cfrPayoff player h) 2 loss)
      informationControlFullFallback who (cfrPayoff who) 2 1 loss :=
  cfrDInformationContinuation_leafOptimal (reducedModel fullPrior) (carriedBitProfile false)
    pbsRootControlFallback 2 1 (fun h player => cfrPayoff player h)
    (cumulative_zeroSum fullPrior) 2 loss (by norm_num) positive
    (fun h player => cfrPayoff_abs_le_two player h) who

/-- Every noisy parent iterate uses those same information-set child contracts. -/
theorem informationChildControl_driver_leafOptimal (loss : ℝ) (positive : 0 < loss)
    (noise : CFRDPredictionNoise (reducedModel fullPrior)) :
    CFRDDepthLeafOptimal (model fullPrior) decisionClock informationControlFullFallback
      cfrPayoff 2 1
      (cfrDConstructedInformationOracle (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff 2 1 2 loss noise) loss :=
  cfrDConstructedInformationOracle_leafOptimal (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff (cumulative_zeroSum fullPrior) 2 1 2 loss (by norm_num) positive
    (fun player h => cfrPayoff_abs_le_two player h) noise

/-- Nonzero value-prediction bias is distinct from the positive child tolerance. -/
theorem informationChildControl_biased_accuracy :
    CFRDDepthAccurate (model fullPrior) decisionClock informationControlFullFallback
      cfrPayoff 2 1
      (cfrDConstructedInformationOracle (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff 2 1 2 (1 / 4) (fun _ _ _ _ => 1 / 8)) (1 / 8) := by
  apply cfrDConstructedInformationOracle_accurate
  intro n trunk who info
  norm_num

/-- Full-game approximate Nash for the biased information-set child driver.
The finite outer-T term and the positive child loss are both retained. -/
theorem informationChildControl_driver_isNash (t : Nat) [NeZero t] :
    IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreferenceWithin
        (cfrDDepthMeanBudget (model fullPrior) decisionClock informationControlFullFallback
            2 1 2 (1 / 8) (1 / 4) 0 t +
          cfrDDepthMeanBudget (model fullPrior) decisionClock informationControlFullFallback
            2 1 2 (1 / 8) (1 / 4) 1 t)
        (fun h who => cfrPayoff who h))
      (cfrDDepthAveragedProfile (model fullPrior) decisionClock informationControlFullFallback
        cfrPayoff 2 1
        (cfrDConstructedInformationOracle (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 2 1 2 (1 / 4) (fun _ _ _ _ => 1 / 8)) t) := by
  apply cfrDConstructedInformationOracle_isNash (reducedModel fullPrior)
    pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior) 2 1
    2 (1 / 8) (1 / 4) (by norm_num) (by norm_num) (by norm_num)
    (fun player h => cfrPayoff_abs_le_two player h)
  intro n trunk who info
  norm_num

end GameTheory.ReBeL.Examples.HiddenTypes
