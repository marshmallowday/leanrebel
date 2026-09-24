/-
# Recomputed-chain and changed-reference controls

The canonical hidden-type game is solved twice with distinct positive losses.
The original zero-factual-reach query remains covered. The probability-law
negative guard has the same observation law but different hidden conditionals;
it is not a counterexample to the source's game-level Theorem 3.
-/

import GameTheory.Analysis.ReBeL.CFRDFreshChain
import GameTheory.Analysis.ReBeL.Examples.CFRDFreshResolve

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- The control includes all legal histories, not merely factual play. -/
local instance freshChainHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Off-path and inactive menus remain part of the legal strategy domain. -/
local instance freshChainChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- The second solve is recomputed at a different, strictly positive tolerance. -/
def freshChainControlLoss (n : Nat) : ℝ := if n = 0 then 1 / 4 else 1 / 8

/-- Both the first and subsequent tolerances satisfy the actual solver premise. -/
theorem freshChainControlLoss_pos (n : Nat) : 0 < freshChainControlLoss n := by
  unfold freshChainControlLoss
  split_ifs <;> norm_num

/-- Each stage is the actual constructed child of the preceding stage. -/
def freshChainControlProfiles (stages : Nat) :
    Unit → Profile (model fullPrior).behavioralSignature :=
  fun k => cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff 2 1 2 freshChainControlLoss (freshControlModels k) stages

/-- The empty chain retains the incumbent on every legal menu. -/
theorem freshChainControl_empty : freshChainControlProfiles 0 = freshControlModels := rfl

/-- Two genuine refreshes retain the old reference law without an input certificate. -/
theorem freshChainControl_reference (who : Player) :
    unilateralReferenceLaw (model fullPrior) (freshChainControlProfiles 2 ())
      informationControlFullFallback who 2 =
      unilateralReferenceLaw (model fullPrior) (carriedBitProfile false)
        informationControlFullFallback who 2 :=
  cfrDFreshInformationChain_referenceLaw (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff 2 1 2 freshChainControlLoss (carriedBitProfile false) who 2

/-- Counterfactual quality is derived from the final computed child, not supplied. -/
theorem freshChainControl_leafOptimal (who : Player) :
    CFRDLeafOptimal (model fullPrior) (freshChainControlProfiles 2 ())
      informationControlFullFallback who (cfrPayoff who) 2 1 (freshChainControlLoss 1) :=
  cfrDFreshInformationChain_leafOptimal (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff (cumulative_zeroSum fullPrior) 2 1 2 freshChainControlLoss (by norm_num)
    (fun player h => cfrPayoff_abs_le_two player h) (carriedBitProfile false) who 1
    (freshChainControlLoss_pos 1)

/-- The factually absent but reference-supported hidden-type query is still charged. -/
theorem freshChainControl_zero_query_counted :
    cfrDFreshValueChange (model fullPrior) (carriedBitProfile false)
        (freshChainControlProfiles 2 ()) informationControlFullFallback 0 (cfrPayoff 0) 2 1
        ((model fullPrior).infoOf 0 zeroControlHistory.trace) ≤
      cfrDFreshValueDrift (model fullPrior) (carriedBitProfile false)
        (freshChainControlProfiles 2 ()) informationControlFullFallback 0 (cfrPayoff 0) 2 1 :=
  cfrDFreshValueChange_le_drift (model fullPrior) _ _ informationControlFullFallback
    0 (cfrPayoff 0) 2 1 _ informationSamplingControl_zero_query_sampled

/-- The finite final draw realizes the twice-recomputed child average. -/
def freshChainControlResolver : CarriedPublicResolver (model fullPrior) Unit :=
  cfrDFreshChainResolver (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff 2 1 2 freshChainControlLoss freshControlModels 2

/-- The complete law holds at a live state without inventing a missing posterior. -/
theorem freshChainControl_none_tail
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    carriedResolvedTail (model fullPrior) freshChainControlResolver unknown who 1
        { iteration := (), history := zeroControlHistory, belief := none } =
      (model fullPrior).runBehavioralFrom
        (Profile.update unknown who (freshChainControlProfiles 2 () who)) 1 zeroControlHistory :=
  cfrDFreshChainResolver_tail (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff 2 1 2 freshChainControlLoss freshControlModels 2 unknown who _

/-- Both inter-solve drifts survive in the unknown-opponent envelope. -/
theorem freshChainControl_envelope
    (unknown : Profile (model fullPrior).behavioralSignature) :
    CFRDResolverEnvelope (model fullPrior) freshControlModels freshChainControlResolver
      informationControlFullFallback unknown 0 1 2 1 (cfrPayoff 1)
      (freshChainControlLoss 1 + ∑ n ∈ Finset.range 2,
        cfrDFreshUniformDrift (model fullPrior) (freshChainControlProfiles n)
          (freshChainControlProfiles (n + 1)) informationControlFullFallback 1 (cfrPayoff 1) 2 1) :=
  cfrDFreshChainResolver_envelope (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
    (cumulative_zeroSum fullPrior) 2 1 2 freshChainControlLoss (by norm_num)
    (fun player h => cfrPayoff_abs_le_two player h) freshControlModels unknown 0 1
    (by decide) 1 (freshChainControlLoss_pos 1)

/-- Zero execution fuel bypasses both fresh-plan drawing and continuation play. -/
theorem freshChainControl_zero_fuel
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (state : PrivateIterationState (model fullPrior) Unit) :
    carriedResolvedTail (model fullPrior) freshChainControlResolver unknown who 0 state =
      FinDist.pure state.history := by
  simp only [carriedResolvedTail, cfrDCutLive_zero, Bool.false_eq_true, if_false]

private theorem freshChainControl_pure_fibre (bit : Bool) :
    (FinDist.pure bit).condOnFibre (fun _ => ()) () = FinDist.pure bit := by
  simpa only [FinDist.map_pure, FinDist.pure_bind] using
    (FinDist.eq_bind_condOnFibre (FinDist.pure bit) (fun _ => ())).symm

/-- Identical observation laws do not justify telescoping across different
hidden conditionals. Here the alleged signed-change identity reads 0 = 0 + 1. -/
theorem freshChainControl_observation_law_not_enough :
    (FinDist.pure false).map (fun _ => ()) = (FinDist.pure true).map (fun _ => ()) ∧
      conditionalOracleValue (FinDist.pure false) (fun _ => ())
          (fun bit => if bit then (1 : ℝ) else 0) () ≠
        conditionalOracleValue (FinDist.pure false) (fun _ => ()) (fun _ => (0 : ℝ)) () +
          conditionalOracleValue (FinDist.pure true) (fun _ => ())
            (fun bit => if bit then (1 : ℝ) else 0) () := by
  constructor
  · simp only [FinDist.map_pure]
  · norm_num [conditionalOracleValue, freshChainControl_pure_fibre, FinDist.expect_pure]


/-- Equality is used only by the abstract real-valued parent learner. -/
local instance freshChainControlInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- The nonzero parent bias, finite outer time, old and final child losses and
both inter-solve drifts are retained in the concrete two-refresh control. -/
def freshChainControlBudget (t : Nat) [NeZero t] : ℝ :=
  (cfrDDepthErrorConstant (model fullPrior) decisionClock informationControlFullFallback 2 1 0 +
      cfrDDepthErrorConstant (model fullPrior) decisionClock informationControlFullFallback 2 1 1) *
      (1 / 8) +
    (cfrDDepthFiniteConstant (model fullPrior) decisionClock informationControlFullFallback
        2 1 2 0 +
      cfrDDepthFiniteConstant (model fullPrior) decisionClock informationControlFullFallback
        2 1 2 1) / Real.sqrt t + 1 / 4 + freshChainControlLoss 1 +
    ∑ n ∈ Finset.range 2, cfrDFreshUniformDrift (model fullPrior)
      (fun k => cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t k) n)
      (fun k => cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t k) (n + 1))
      informationControlFullFallback 1 (cfrPayoff 1) 2 1

/-- The actual biased parent and twice-recomputed child achieve the stated
root bound against every unknown behavioral opponent. The Nash comparison
only names the game's value; it is not a solver or child-quality input. -/
theorem freshChainControl_biased_security
    (reference : Profile (model fullPrior).behavioralSignature)
    (equilibrium : IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreference (fun h who => cfrPayoff who h)) reference)
    (unknown : Profile (model fullPrior).behavioralSignature) (t : Nat) [NeZero t] :
    ((model fullPrior).runBehavioral reference 3).expect (cfrPayoff 0) - freshChainControlBudget t ≤
      (privateCarriedResolve (model fullPrior) (cfrIterationLaw t) (freshControlParentPlays t)
        (cfrDFreshChainResolver (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t) 2)
        unknown 0 2 1).expect (cfrPayoff 0) := by
  apply cfrDFreshChain_security (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
    (cumulative_zeroSum fullPrior) 2 1 2 (1 / 8) (1 / 4) freshChainControlLoss 1
    (by norm_num) (by norm_num) (by norm_num) (freshChainControlLoss_pos 1)
    (fun player h => cfrPayoff_abs_le_two player h) (fun _ _ _ _ => 1 / 8) _
    reference equilibrium unknown 0 1 (by decide) t
  intro n trunk player info
  norm_num

end GameTheory.ReBeL.Examples.HiddenTypes
