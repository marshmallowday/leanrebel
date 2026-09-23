/-
# Live, off-model and biased fresh-child controls

The canonical two-stage hidden-type game uses distinct old/new child budgets.
The new solver is actually recomputed, and its private plan draw is checked
on a live history with an absent carried posterior as well as at zero fuel.
A separate finite-law guard rejects replacing a fiber maximum by its mean.
-/

import GameTheory.Analysis.ReBeL.CFRDFreshResolve
import GameTheory.Analysis.ReBeL.Examples.CFRDInformationSampledDriver

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Enumerate all legal histories, not the factual support of one policy. -/
local instance freshControlHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- The finite legal menus include inactive singleton choices. -/
local instance freshControlChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Equality is confined to the abstract reference learner. -/
local instance freshControlInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- A retained model which has genuine factually absent reference queries. -/
def freshControlModels : Unit → Profile (model fullPrior).behavioralSignature :=
  fun _ => carriedBitProfile false

/-- The new finite information-set solve uses its own positive tolerance. -/
def freshControlResolver : CarriedPublicResolver (model fullPrior) Unit :=
  cfrDFreshInformationResolver (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff 2 1 2 (1 / 8) freshControlModels

/-- No fictitious posterior is required to realize the fresh child at a live
legal history. This record deliberately tests the absent-posterior interface. -/
theorem freshControl_none_tail
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    carriedResolvedTail (model fullPrior) freshControlResolver unknown who 1
        { iteration := (), history := zeroControlHistory, belief := none } =
      (model fullPrior).runBehavioralFrom
        (Profile.update unknown who
          (cfrDInformationContinuation (reducedModel fullPrior) (carriedBitProfile false)
            pbsRootControlFallback 2 1 (fun h player => cfrPayoff player h) 2 (1 / 8) who))
        1 zeroControlHistory :=
  cfrDFreshInformationResolver_tail (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff 2 1 2 (1 / 8) freshControlModels unknown who _

/-- The old model's absent factual query remains a genuine reference query. -/
theorem freshControl_zero_query_counted :
    cfrDFreshValueChange (model fullPrior) (carriedBitProfile false)
        (cfrDInformationContinuation (reducedModel fullPrior) (carriedBitProfile false)
          pbsRootControlFallback 2 1 (fun h player => cfrPayoff player h) 2 (1 / 8))
        informationControlFullFallback 0 (cfrPayoff 0) 2 1
        ((model fullPrior).infoOf 0 zeroControlHistory.trace) ≤
      cfrDFreshValueDrift (model fullPrior) (carriedBitProfile false)
        (cfrDInformationContinuation (reducedModel fullPrior) (carriedBitProfile false)
          pbsRootControlFallback 2 1 (fun h player => cfrPayoff player h) 2 (1 / 8))
        informationControlFullFallback 0 (cfrPayoff 0) 2 1 :=
  cfrDFreshValueChange_le_drift (model fullPrior) _ _ informationControlFullFallback
    0 (cfrPayoff 0) 2 1 _ informationSamplingControl_zero_query_sampled

/-- The actual new solver supplies the opponent envelope without a child
quality or support certificate from the caller. Its measured drift stays visible. -/
theorem freshControl_envelope
    (unknown : Profile (model fullPrior).behavioralSignature) :
    CFRDResolverEnvelope (model fullPrior) freshControlModels freshControlResolver
      informationControlFullFallback unknown 0 1 2 1 (cfrPayoff 1)
      (1 / 8 + cfrDFreshInformationDrift (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff 2 1 2 (1 / 8) freshControlModels 1) :=
  cfrDFreshInformationResolver_envelope (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff (cumulative_zeroSum fullPrior) 2 1 2 (1 / 8) (by norm_num) (by norm_num)
    (fun player h => cfrPayoff_abs_le_two player h) freshControlModels unknown 0 1 (by decide)

/-- Keeping the same legal continuation has no model-drift penalty. -/
theorem freshControl_same_drift (who : Player) :
    cfrDFreshValueDrift (model fullPrior) (carriedBitProfile false) (carriedBitProfile false)
      informationControlFullFallback who (cfrPayoff who) 2 1 = 0 :=
  cfrDFreshValueDrift_self (model fullPrior) _ informationControlFullFallback who
    (cfrPayoff who) 2 1

/-- No live value query exists with zero remaining fuel, even if policies differ. -/
theorem freshControl_zero_drift
    (next : Profile (model fullPrior).behavioralSignature) (who : Player) :
    cfrDFreshValueDrift (model fullPrior) (carriedBitProfile false) next
      informationControlFullFallback who (cfrPayoff who) 2 0 = 0 :=
  cfrDFreshValueDrift_zero_remaining (model fullPrior) _ next
    informationControlFullFallback who (cfrPayoff who) 2

/-- The zero-fuel resolver really takes the no-draw branch on every carried state. -/
theorem freshControl_zero_stopped
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (state : PrivateIterationState (model fullPrior) Unit) :
    carriedResolvedTail (model fullPrior)
      (cfrDFreshInformationResolver (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff 2 0 2 (1 / 8) freshControlModels) unknown who 0 state =
      FinDist.pure state.history := by
  apply cfrDFreshInformationResolver_stopped
  rw [cfrDCutLive_zero]
  decide

/-- The actual noisy parent uses old loss 1/4; the new child will use 1/8. -/
def freshControlParentPlays (t : Nat) : Fin t → Profile (model fullPrior).behavioralSignature :=
  fun n => cfrDDepthPlay (model fullPrior) decisionClock informationControlFullFallback
    cfrPayoff 2 1
    (cfrDConstructedSampledInformationOracle (reducedModel fullPrior) pbsRootControlFallback
      cfrPayoff 2 1 2 (1 / 4) (fun _ _ _ _ => 1 / 8)) n.val

/-- All distinct error sources remain in the concrete nonzero-error control. -/
def freshControlBudget (t : Nat) [NeZero t] : ℝ :=
  (cfrDDepthErrorConstant (model fullPrior) decisionClock informationControlFullFallback 2 1 0 +
      cfrDDepthErrorConstant (model fullPrior) decisionClock informationControlFullFallback 2 1 1) *
      (1 / 8) +
    (cfrDDepthFiniteConstant (model fullPrior) decisionClock informationControlFullFallback
        2 1 2 0 +
      cfrDDepthFiniteConstant (model fullPrior) decisionClock informationControlFullFallback
        2 1 2 1) /
      Real.sqrt t + 1 / 4 + 1 / 8 +
    cfrDFreshInformationDrift (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 1 2
      (1 / 8) (freshControlParentPlays t) 1

/-- A complete unknown-opponent guarantee for the freshly recomputed child.
The comparison equilibrium only names the value of this concrete game. -/
theorem freshControl_biased_security
    (reference : Profile (model fullPrior).behavioralSignature)
    (equilibrium : IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreference (fun h who => cfrPayoff who h)) reference)
    (unknown : Profile (model fullPrior).behavioralSignature) (t : Nat) [NeZero t] :
    ((model fullPrior).runBehavioral reference 3).expect (cfrPayoff 0) - freshControlBudget t ≤
      (privateCarriedResolve (model fullPrior) (cfrIterationLaw t) (freshControlParentPlays t)
        (cfrDFreshInformationResolver (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 2 1 2 (1 / 8) (freshControlParentPlays t)) unknown 0 2 1).expect
        (cfrPayoff 0) := by
  apply cfrDFreshInformation_security (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
    (cumulative_zeroSum fullPrior) 2 1 2 (1 / 8) (1 / 4) (1 / 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun player h => cfrPayoff_abs_le_two player h) (fun _ _ _ _ => 1 / 8) _
    reference equilibrium unknown 0 1 (by decide) t
  intro n trunk player info
  norm_num

/-- A finite-law negative guard: a zero mean does not bound every coordinate.
This is not a game-level counterexample to the original recursive source theorem. -/
theorem freshControl_mean_not_uniform :
    (cfrIterationLaw 2).expect (fun n => if n.val = 0 then (1 : ℝ) else -1) = 0 ∧
      ¬ (∀ n : Fin 2, (if n.val = 0 then (1 : ℝ) else -1) ≤ 0) := by
  constructor
  · rw [cfrIterationLaw_expect 2 (fun n => if n = 0 then (1 : ℝ) else -1)]
    norm_num [Finset.sum_range_succ]
  · intro bounded
    have impossible := bounded 0
    norm_num at impossible

end GameTheory.ReBeL.Examples.HiddenTypes
