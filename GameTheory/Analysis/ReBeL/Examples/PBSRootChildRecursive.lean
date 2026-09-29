/-
# A factual child of a noisy parent inside an existing rooted game

The parent has already drawn its joint root and made one original transition.
Its child posterior is decoded at the same remaining clock. Internal and fresh
solvers retain separate computations; only full decoded laws and scalar Nash
values are compared.
-/

import GameTheory.Analysis.ReBeL.PBSRootChildRecursive
import GameTheory.Analysis.ReBeL.Examples.CFRDStoredChildDefect

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Enumerate every original legal history. -/
local instance rootedChildHistory : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Include all histories of the existing outer rooted protocol. -/
local instance rootedChildRootHistory :
    Fintype (pbsRootProtocol recursiveInitialBelief.law).History :=
  pbsRootHistoryFintype recursiveInitialBelief.law

/-- The actual internal model exposes only original local snapshots. -/
@[reducible]
def rootedChildModel :=
  pbsRootInformation (model fullPrior) recursiveInitialBelief.law

/-- Equality is used in the reference parent's full information recurrence. -/
local instance rootedChildInfo (who : Player) :
    DecidableEq ((fullInformation rootedChildModel).InfoState who) := Classical.decEq _

/-- Finite menus retain the original action options. -/
local instance rootedChildChoice (who : Player)
    (info : (fullInformation rootedChildModel).InfoState who) :
    Fintype ((fullInformation rootedChildModel).Choice who info) := by
  classical
  infer_instance

/-- An actual one-step computational child, not a supplied Nash certificate. -/
def rootedChildSolve : PBSChildSolve rootedChildModel :=
  pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (pbsRootProtocol recursiveInitialBelief.law)
    rootedChildModel
    (pbsRootDepthFallback (reducedModel fullPrior) recursiveInitialBelief.law
      pbsRootControlFallback)
    (pbsRootPayoff recursiveInitialBelief.law cfrPayoff) 2

/-- The root draw plus one original transition form this noisy parent's trunk.
Its prediction bias and requested child loss are distinct positive numbers. -/
def rootedChildTrunk (round : Nat) :
    Profile (fullInformation rootedChildModel).behavioralSignature :=
  cfrDComposedTrunk rootedChildModel
    (pbsRootDepthFallback (reducedModel fullPrior) recursiveInitialBelief.law
      pbsRootControlFallback)
    (pbsRootPayoff recursiveInitialBelief.law cfrPayoff) 2 1 (1 / 4)
    rootedChildSolve (fun _ _ _ _ => 1 / 8) round

/-- Decode the actual live posterior of that parent. A positive factual query
is required; no fallback at an absent public observation is called a posterior. -/
def rootedChildPosterior (round : Nat)
    (observations : List (reducedModel fullPrior).PublicSignal)
    (past : List (Option (List (reducedModel fullPrior).PublicSignal)))
    (possible : CFRDFactualChildPossible rootedChildModel (rootedChildTrunk round)
      2 1 (some observations :: past)) :
    PublicBelief (fullInformation rootedChildModel).toInfoSignals
      (some observations :: past) :=
  cfrDFactualChildBelief rootedChildModel (rootedChildTrunk round) 2 1
    (some observations :: past) possible

/-- The independent original solve has scalar gap at most the parent's
mass-scaled child request plus 1/4 from
the decoded internal solve. It need not have the same policy, noise or budget. -/
theorem rootedChild_fresh_value (round : Nat)
    (observations : List (reducedModel fullPrior).PublicSignal)
    (past : List (Option (List (reducedModel fullPrior).PublicSignal)))
    (possible : CFRDFactualChildPossible rootedChildModel (rootedChildTrunk round)
      2 1 (some observations :: past)) (who : Player) :
    let child := rootedChildPosterior round observations past possible
    let decoded := pbsRootChildBelief (reducedModel fullPrior) recursiveInitialBelief.law child
    let internal := pbsRootChildRecursiveProfile (reducedModel fullPrior) recursiveInitialBelief
      pbsRecursiveAllocatedNoise [1] pbsRootControlFallback cfrPayoff 2 child
        (child.law.positiveMassFloor * (1 / 4))
    let fresh := pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
      (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 decoded (1 / 4)
    |(decoded.law.bind ((model fullPrior).runBehavioralFrom internal 1)).expect (cfrPayoff who) -
      (decoded.law.bind ((model fullPrior).runBehavioralFrom fresh 1)).expect (cfrPayoff who)| ≤
      child.law.positiveMassFloor * (1 / 4) + 1 / 4 := by
  intro child decoded internal fresh
  exact pbsRootChildRecursive_fresh_value (reducedModel fullPrior) recursiveInitialBelief
    pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise_bounded
    pbsRecursiveAllocatedNoise_bounded [1] [1] rfl pbsRootControlFallback pbsRootControlFallback
    cfrPayoff (cumulative_zeroSum fullPrior) 2 (by norm_num) cfrPayoff_abs_le_two
    child (child.law.positiveMassFloor * (1 / 4)) (1 / 4)
    (mul_pos (FinDist.positiveMassFloor_pos child.law) (by norm_num)) (by norm_num) who

/-- The same decoded private draw is retained through arbitrary continuation
fuel, including a stage and all later steps. No seed-aware opponent is admitted. -/
theorem rootedChild_private_law (round : Nat)
    (observations : List (reducedModel fullPrior).PublicSignal)
    (past : List (Option (List (reducedModel fullPrior).PublicSignal)))
    (possible : CFRDFactualChildPossible rootedChildModel (rootedChildTrunk round)
      2 1 (some observations :: past))
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) (fuel : Nat) :
    let child := rootedChildPosterior round observations past possible
    let decoded := pbsRootChildBelief (reducedModel fullPrior) recursiveInitialBelief.law child
    (pbsRootChildRecursiveDraw (reducedModel fullPrior) recursiveInitialBelief
      pbsRecursiveAllocatedNoise [1] pbsRootControlFallback cfrPayoff 2 child
        (child.law.positiveMassFloor * (1 / 4))).bind
      (fun chosen => decoded.law.bind ((model fullPrior).runBehavioralFrom
        (Profile.update unknown who (chosen who)) fuel)) =
      decoded.law.bind ((model fullPrior).runBehavioralFrom
        (Profile.update unknown who
          (pbsRootChildRecursiveProfile (reducedModel fullPrior) recursiveInitialBelief
            pbsRecursiveAllocatedNoise [1] pbsRootControlFallback cfrPayoff 2 child
            (child.law.positiveMassFloor * (1 / 4)) who)) fuel) := by
  intro child decoded
  exact pbsRootChildRecursiveDraw_law (reducedModel fullPrior) recursiveInitialBelief
    pbsRecursiveAllocatedNoise [1] pbsRootControlFallback cfrPayoff 2 child
    (child.law.positiveMassFloor * (1 / 4)) unknown who fuel

/-- A fresh exact numerical prediction is not required: the internal allocated
noise solver secures its own model value with its actual mass-scaled tolerance. -/
theorem rootedChild_private_security (round : Nat)
    (observations : List (reducedModel fullPrior).PublicSignal)
    (past : List (Option (List (reducedModel fullPrior).PublicSignal)))
    (possible : CFRDFactualChildPossible rootedChildModel (rootedChildTrunk round)
      2 1 (some observations :: past))
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    let child := rootedChildPosterior round observations past possible
    let decoded := pbsRootChildBelief (reducedModel fullPrior) recursiveInitialBelief.law child
    let internal := pbsRootChildRecursiveProfile (reducedModel fullPrior) recursiveInitialBelief
      pbsRecursiveAllocatedNoise [1] pbsRootControlFallback cfrPayoff 2 child
        (child.law.positiveMassFloor * (1 / 4))
    (decoded.law.bind ((model fullPrior).runBehavioralFrom internal 1)).expect
        (cfrPayoff who) - child.law.positiveMassFloor * (1 / 4) ≤
      (pbsRootChildRecursiveDraw (reducedModel fullPrior) recursiveInitialBelief
        pbsRecursiveAllocatedNoise [1] pbsRootControlFallback cfrPayoff 2 child
        (child.law.positiveMassFloor * (1 / 4))).expect
        (fun chosen => (decoded.law.bind ((model fullPrior).runBehavioralFrom
          (Profile.update unknown who (chosen who)) 1)).expect (cfrPayoff who)) := by
  intro child decoded internal
  exact pbsRootChildRecursiveDraw_security (reducedModel fullPrior) recursiveInitialBelief
    pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise_bounded [1] pbsRootControlFallback
    cfrPayoff (cumulative_zeroSum fullPrior) 2 (by norm_num) cfrPayoff_abs_le_two
    child (child.law.positiveMassFloor * (1 / 4))
    (mul_pos (FinDist.positiveMassFloor_pos child.law) (by norm_num)) unknown who

/-- The actual noisy parent's public splice has the decoded internal child's
whole continuation law, at the parent's mass-scaled requested tolerance. -/
theorem rootedChild_parent_law (round : Nat)
    (observations : List (reducedModel fullPrior).PublicSignal)
    (past : List (Option (List (reducedModel fullPrior).PublicSignal)))
    (possible : CFRDFactualChildPossible rootedChildModel (rootedChildTrunk round)
      2 1 (some observations :: past)) (fuel : Nat) :
    let child := rootedChildPosterior round observations past possible
    let rootFallback := pbsRootDepthFallback (reducedModel fullPrior)
      recursiveInitialBelief.law pbsRootControlFallback
    (child.law.bind ((fullInformation rootedChildModel).runBehavioralFrom
      (cfrDComposedChildProfile rootedChildModel (rootedChildTrunk round)
        rootFallback 2 1 (1 / 4) rootedChildSolve) fuel)).map History.state =
      ((pbsRootChildBelief (reducedModel fullPrior) recursiveInitialBelief.law child).law.bind
        ((model fullPrior).runBehavioralFrom
          (pbsRootChildRecursiveProfile (reducedModel fullPrior) recursiveInitialBelief
            pbsRecursiveAllocatedNoise [1] pbsRootControlFallback cfrPayoff 2 child
            (child.law.positiveMassFloor * (1 / 4))) fuel)).map some := by
  intro child rootFallback
  exact pbsRootChildRecursive_parent_law (reducedModel fullPrior) recursiveInitialBelief
    pbsRecursiveAllocatedNoise [1] pbsRootControlFallback cfrPayoff 2
    (rootedChildTrunk round) 2 (1 / 4) observations past possible fuel

/-- After the administrative draw, zero continuation fuel preserves the
current child law, not the outer initial law and not a new root sample. -/
theorem rootedChild_zero_continuation
    {observations : List (reducedModel fullPrior).PublicSignal}
    {past : List (Option (List (reducedModel fullPrior).PublicSignal))}
    (child : PublicBelief (fullInformation rootedChildModel).toInfoSignals
      (some observations :: past))
    (profile : Profile (fullInformation rootedChildModel).behavioralSignature) :
    (child.law.bind ((fullInformation rootedChildModel).runBehavioralFrom profile 0)).map
      History.state =
      (pbsRootChildBelief (reducedModel fullPrior) recursiveInitialBelief.law child).law.map
        some := by
  have equal := pbsRootChild_continuation_law (reducedModel fullPrior)
    recursiveInitialBelief.law _ (pbsRoot_publicBelief_depth (reducedModel fullPrior)
      recursiveInitialBelief) child profile 0
  have zero (strategy : Profile (model fullPrior).behavioralSignature) :
      (model fullPrior).runBehavioralFrom strategy 0 = FinDist.pure := rfl
  rw [zero, FinDist.bind_pure] at equal
  exact equal

end GameTheory.ReBeL.Examples.HiddenTypes
