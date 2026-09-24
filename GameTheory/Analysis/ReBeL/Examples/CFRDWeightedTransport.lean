/-
# Weighted-error controls: rare queries, private correlation and actual solves

The finite-law guards distinguish actual visitation from a maximum and from
independent resampling. They are not counterexamples to source Theorem 3.
The game consumer retains two actual child computations and arbitrary opponents.
-/

import GameTheory.Analysis.ReBeL.CFRDWeightedTransport
import GameTheory.Analysis.ReBeL.Examples.CFRDReferenceReweight

noncomputable section

namespace GameTheory.ReBeL.Examples.WeightedTransport

open GameTheory.Math.Probability

/-- A genuinely rare actual query has mass one hundredth. -/
def rareQuery : FinDist Bool :=
  FinDist.mix (1 / 100) (by norm_num) (by norm_num) (FinDist.pure true) (FinDist.pure false)

/-- At the rare query the hidden conditional flips maximally; elsewhere it agrees. -/
def rareCost (tag : Bool) : ℝ :=
  FinDist.conditionalTransportDefect (FinDist.pure false)
    (if tag then FinDist.pure true else FinDist.pure false) (fun _ => ()) ()

/-- Costs really arise from the transport defect, not from arbitrary test constants. -/
theorem rareCost_values : rareCost true = 2 ∧ rareCost false = 0 := by
  constructor
  · exact ReferenceReweight.hidden_flip_transport_two
  · apply FinDist.conditionalTransportDefect_eq_zero
    · exact fun sampled => sampled
    · exact fun _ => rfl

/-- The weighted cost is one fiftieth, despite a worst-case cost of two. -/
theorem rareQuery_mean : rareQuery.expect rareCost = 1 / 50 := by
  norm_num [rareQuery, FinDist.expect_mix, FinDist.expect_pure, rareCost_values.1,
    rareCost_values.2]

/-- Keeping only the uniform bound would lose this strict improvement. -/
theorem rareQuery_mean_lt_max : rareQuery.expect rareCost < rareCost true := by
  rw [rareQuery_mean, rareCost_values.1]
  norm_num

/-- Correlation between the private seed and its reached query is retained. -/
def coupledSeedQuery : FinDist (Bool × Bool) := rareQuery.map (fun bit => (bit, bit))

/-- A cost can depend jointly on the seed and query. -/
def disagreementCost (pair : Bool × Bool) : ℝ := if pair.1 = pair.2 then 0 else 2

/-- The actual coupled law never reaches a seed/query disagreement. -/
theorem coupled_cost_zero : coupledSeedQuery.expect disagreementCost = 0 := by
  simp [coupledSeedQuery, FinDist.expect_map, disagreementCost, FinDist.expect_const]

/-- Replacing actual coupling by independent marginals creates a false charge. -/
theorem independent_cost_positive :
    0 < (FinDist.product rareQuery rareQuery).expect disagreementCost := by
  norm_num [FinDist.expect_product, rareQuery, FinDist.expect_mix, FinDist.expect_pure,
    disagreementCost]

end GameTheory.ReBeL.Examples.WeightedTransport

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- All legal histories, including counterfactual ones, remain available. -/
local instance weightedControlHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Inactive menus are not removed from the strategy carrier. -/
local instance weightedControlChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Two actual fresh solves supply the local quality needed by the weighted
opponent-prefix bound. The unknown opponent is arbitrary and remains seed-blind. -/
theorem freshChainControl_weighted_prefix
    (unknown : Profile (model fullPrior).behavioralSignature) :
    (privateCarriedResolve (model fullPrior) (FinDist.pure ()) freshControlModels
      freshChainControlResolver unknown 0 2 1).expect (cfrPayoff 1) -
      (FinDist.pure ()).expect (fun n => ((model fullPrior).runBehavioral
        (Profile.update (freshControlModels n) 1 (cfrDPrefixPolicy (model fullPrior)
          (fullObservationClock (reducedModel fullPrior)) (freshControlModels n) 1
          (unknown 1) 2)) 3).expect (cfrPayoff 1)) ≤
      cfrDWeightedEnvelopeLoss (model fullPrior) (FinDist.pure ()) freshControlModels
        unknown 0 1 2 1 (cfrDFreshTransportCharge (model fullPrior) freshControlModels
          (freshChainControlProfiles 2) informationControlFullFallback 1 (cfrPayoff 1)
          2 1 2 (freshChainControlLoss 1)) := by
  apply privateCarriedResolve_weighted_envelope_le_prefix (model fullPrior)
    (fullObservationClock (reducedModel fullPrior)) (perfectRecall fullPrior)
    (FinDist.pure ()) freshControlModels freshChainControlResolver
    informationControlFullFallback unknown 0 1 (by decide) 2 1 (cfrPayoff 1)
  exact cfrDFreshCoherentResolver_query_bound (model fullPrior) (perfectRecall fullPrior)
    freshControlModels (freshChainControlProfiles 2) informationControlFullFallback
    unknown 0 1 (by decide) 2 1 (cfrPayoff 1) 2 (freshChainControlLoss 1)
    (le_of_lt (freshChainControlLoss_pos 1)) (fun h => cfrPayoff_abs_le_two 1 h) (by
      intro n
      cases n
      exact freshChainControl_leafOptimal 1)

/-- Zero continuation fuel has no charged live query, even at a missing belief. -/
theorem freshChainControl_weighted_zero_fuel
    (unknown : Profile (model fullPrior).behavioralSignature) :
    cfrDWeightedEnvelopeLoss (model fullPrior) (FinDist.pure ()) freshControlModels
      unknown 0 1 2 0 (cfrDFreshTransportCharge (model fullPrior) freshControlModels
        (freshChainControlProfiles 2) informationControlFullFallback 1 (cfrPayoff 1)
        2 0 2 (freshChainControlLoss 1)) = 0 := by
  simp only [cfrDWeightedEnvelopeLoss, cfrDCutLive_zero, cfrDFreshTransportCharge,
    Bool.false_eq_true, if_false, FinDist.expect_const]

end GameTheory.ReBeL.Examples.HiddenTypes
