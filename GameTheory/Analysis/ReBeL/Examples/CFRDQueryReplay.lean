/-
# Same-setting replay: finite noisy parent and hostile query controls

The live off-path query and changed-joint-law guard prevent replacing the
reference law by factual support or its public marginal. The actual parent
has bias 1/8, child loss 1/4 and a finite number of outer iterations.
-/

import GameTheory.Analysis.ReBeL.CFRDQueryReplaySafety
import GameTheory.Analysis.ReBeL.Examples.CFRDSourceRates

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Keep every legal hidden history, not only the actual parent's support. -/
local instance queryReplayHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- The real-valued reference includes all legal and off-path menus. -/
local instance queryReplayChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Information equality remains on the noncomputable proof side. -/
local instance queryReplayInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- Native retained-query sampling is unchanged by an arbitrary restored
tail, including the positively sampled but factually absent hidden query. -/
theorem queryReplayControl_off_path_sample
    (unknown : Profile (model fullPrior).behavioralSignature) :
    cfrDInformationQuerySample (reducedModel fullPrior)
        (cfrDDepthProfile (model fullPrior) decisionClock 2
          (carriedBitProfile false) (carriedBitProfile true))
        pbsRootControlFallback 2 1 (fun h who => cfrPayoff who h) 2 (1 / 4)
        0 ((model fullPrior).infoOf 0 zeroControlHistory.trace) unknown 1 =
      cfrDInformationQuerySample (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 (fun h who => cfrPayoff who h) 2 (1 / 4)
        0 ((model fullPrior).infoOf 0 zeroControlHistory.trace) unknown 1 :=
  cfrDInformationQuerySample_clamp (reducedModel fullPrior) (carriedBitProfile false)
    (carriedBitProfile true) pbsRootControlFallback 2 1 (fun h who => cfrPayoff who h)
    2 (1 / 4) 0 _ informationSamplingControl_zero_query_sampled unknown 1

/-- This tested query genuinely cannot be justified by factual-query support. -/
theorem queryReplayControl_off_path_not_factual :
    ¬ CFRDInformationQueryFactual (reducedModel fullPrior) (carriedBitProfile false)
      2 1 0 ((model fullPrior).infoOf 0 zeroControlHistory.trace) :=
  informationSamplingControl_zero_query_not_factual

/-- Both players and EVERY finite noisy parent round have zero computed
replay drift. The tolerance is not changed from 1/4 to a new value. -/
theorem queryReplayControl_parent_drift_zero (t : Nat) (n : Fin t) (who : Player) :
    cfrDFreshValueDrift (model fullPrior) (freshControlParentPlays t n)
      (cfrDInformationContinuation (reducedModel fullPrior) (freshControlParentPlays t n)
        pbsRootControlFallback 2 1 (fun h player => cfrPayoff player h) 2 (1 / 4))
      informationControlFullFallback who (cfrPayoff who) 2 1 = 0 :=
  cfrDInformationReplay_drift_zero (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff 2 1 2 (1 / 4) (fun _ _ _ _ => 1 / 8) n.val who

/-- The actual seed/history law is preserved for arbitrary parent weights,
unknown opposing policies, both players and off-model public observations. -/
theorem queryReplayControl_actual_law (t : Nat) (seed : FinDist (Fin t))
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    privateCarriedResolve (model fullPrior) seed (freshControlParentPlays t)
        (cfrDFreshChainResolver (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 2 1 2 (fun _ => 1 / 4) (freshControlParentPlays t) 1)
        unknown who 2 1 =
      privateCarriedContinue (model fullPrior) seed (freshControlParentPlays t) unknown who 2 1 :=
  cfrDInformationReplay_resolve_law (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff 2 1 2 (1 / 4) (fun _ _ _ _ => 1 / 8) t seed unknown who

/-- The numeric bias, finite-T rate and TWO child-loss contributions survive;
only the independently proved zero replay drift has disappeared. -/
def queryReplayControlBudget (t : Nat) : ℝ :=
  (cfrDDepthErrorConstant (model fullPrior) decisionClock informationControlFullFallback 2 1 0 +
      cfrDDepthErrorConstant (model fullPrior) decisionClock informationControlFullFallback 2 1 1) *
      (1 / 8) +
    (cfrDDepthFiniteConstant (model fullPrior) decisionClock informationControlFullFallback
        2 1 2 0 +
      cfrDDepthFiniteConstant (model fullPrior) decisionClock informationControlFullFallback
        2 1 2 1) / Real.sqrt t + 2 * (1 / 4)

/-- A complete security consumer recomputes the real child. No scalar-Nash-
to-vector-stability premise or root-security certificate is supplied. -/
theorem queryReplayControl_biased_security
    (reference : Profile (model fullPrior).behavioralSignature)
    (equilibrium : IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreference (fun h who => cfrPayoff who h)) reference)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (t : Nat) [NeZero t] :
    ((model fullPrior).runBehavioral reference 3).expect (cfrPayoff who) -
        queryReplayControlBudget t ≤
      (privateCarriedResolve (model fullPrior) (cfrIterationLaw t) (freshControlParentPlays t)
        (cfrDFreshChainResolver (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 2 1 2 (fun _ => 1 / 4) (freshControlParentPlays t) 1)
        unknown who 2 1).expect (cfrPayoff who) := by
  apply cfrDInformationReplay_security (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff (cumulative_zeroSum fullPrior) 2 1 2 (1 / 8) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num)
    (fun player h => cfrPayoff_abs_le_two player h) (fun _ _ _ _ => 1 / 8) _
    reference equilibrium unknown who t
  intro n trunk player info
  norm_num

/-- Exhausted execution never invents a live query or draws a new plan. -/
theorem queryReplayControl_zero_fuel (t : Nat)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (state : PrivateIterationState (model fullPrior) (Fin t)) :
    carriedResolvedTail (model fullPrior)
        (cfrDFreshChainResolver (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 2 0 2 (fun _ => 1 / 4) (freshControlParentPlays t) 1)
        unknown who 0 state = FinDist.pure state.history := by
  simp only [carriedResolvedTail, cfrDCutLive_zero, Bool.false_eq_true, if_false]

end GameTheory.ReBeL.Examples.HiddenTypes

namespace GameTheory.ReBeL.Examples.SourceRates

open GameTheory.Math.Probability

/-- Both observation laws are nondegenerate and exactly equal, but a supported
conditional value changes by ONE. Replay cannot use mere marginal equality
instead of the joint prefix-law hypothesis; this is not a solver counterexample. -/
theorem queryReplayControl_joint_law_required :
    oldJoint.map Prod.fst = newJoint.map Prod.fst ∧
      conditionalOracleValue newJoint Prod.fst (fun p => if p.2 then (1 : ℝ) else 0) true -
        conditionalOracleValue oldJoint Prod.fst
          (fun p => if p.2 then (1 : ℝ) else 0) true = 1 := by
  constructor
  · apply FinDist.ext_of_prob
    intro tag
    rw [oldJoint_mass, newJoint_mass]
  · simp only [conditionalOracleValue, oldJoint_conditional, newJoint_conditional,
      FinDist.expect_pure, if_true, if_false, sub_zero]

end GameTheory.ReBeL.Examples.SourceRates
