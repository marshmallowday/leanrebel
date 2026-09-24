/-
# Concrete noisy depth-sampling and first-hit controls

The hidden-type protocol has a real joint PBS and two strategic rounds.
Child tolerance 1/4, prediction bias 1/8, and distinct finite outer counts
remain visible. Boolean hostile controls test first-hit accounting separately
from any claim about the source's recursive game-theoretic safety theorem.
-/

import GameTheory.Analysis.ReBeL.PBSCarriedDepthFirstHit
import GameTheory.Analysis.ReBeL.Examples.PBSCarriedDepth
import GameTheory.Analysis.ReBeL.Examples.PBSCarriedRecursion

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Use the existing exhaustive enumeration of legal canonical histories. -/
local instance depthSamplingHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- A concrete root history is supported by the four-outcome joint model PBS. -/
theorem depthSampling_supported :
    depthControlState.history ∈ depthControlBelief.law.support := by
  classical
  unfold depthControlBelief
  rw [FinDist.support_map]
  refine ⟨(0 : Fin 4), ?_, rfl⟩
  rw [← FinDist.prob_pos_iff]
  norm_num [cfrIterationLaw]

/-- The live-root equality is proved from concrete support, not assumed. -/
theorem depthSampling_not_exception :
    ¬ pbsCarriedCFRException (reducedModel fullPrior) 1 depthControlState := by
  rintro ⟨_, absent⟩
  exact absent depthSampling_supported

/-- Sampling actual noisy parent iterates agrees at the original hidden history. -/
theorem depthSampling_supported_law
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (t : Nat) [NeZero t] :
    (cfrIterationLaw t).bind (fun n => (model fullPrior).runBehavioralFrom
      (Profile.update unknown who (pbsInformationDepthCFRIterate (reducedModel fullPrior)
        depthControlBelief pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
        (depthControlNoise depthControlBelief.law) n.val who)) 2 depthControlState.history) =
      (model fullPrior).runBehavioralFrom (Profile.update unknown who
        (pbsInformationDepthCFR (reducedModel fullPrior) depthControlBelief
          pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
          (depthControlNoise depthControlBelief.law) t who)) 2 depthControlState.history :=
  pbsInformationDepthCFR_sampling_from_support (reducedModel fullPrior) depthControlBelief
    pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4) (depthControlNoise depthControlBelief.law)
    t unknown who 2 depthControlState.history depthSampling_supported

/-- A point-mass actual root is allowed instead of the model's four-point law. -/
theorem depthSampling_reweighted_law
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (t : Nat) [NeZero t] :
    (FinDist.pure depthControlState.history).bind (fun history =>
      (cfrIterationLaw t).bind (fun n => (model fullPrior).runBehavioralFrom
        (Profile.update unknown who (pbsInformationDepthCFRIterate (reducedModel fullPrior)
          depthControlBelief pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
          (depthControlNoise depthControlBelief.law) n.val who)) 2 history)) =
      (FinDist.pure depthControlState.history).bind ((model fullPrior).runBehavioralFrom
        (Profile.update unknown who (pbsInformationDepthCFR (reducedModel fullPrior)
          depthControlBelief pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
          (depthControlNoise depthControlBelief.law) t who)) 2) := by
  apply pbsInformationDepthCFR_sampling_reweighted
  intro history reached
  have same : history = depthControlState.history := by simpa using reached
  subst history
  exact depthSampling_supported

/-- Full-state equality retains the sampled profile paired with its own posterior. -/
theorem depthSampling_full_state
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    carriedResolvedStep (model fullPrior) (fun _ : Unit => carriedBitProfile false)
        (pbsCarriedDepthResolver (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
          1 1 2 (1 / 4) depthControlNoise 2 (fun _ : Unit => carriedBitProfile false))
        unknown who 1 depthControlState =
      pbsCarriedDepthHistoryFirstStep (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff 1 1 2 (1 / 4) depthControlNoise 2 (fun _ : Unit => carriedBitProfile false)
        unknown who 1 depthControlState :=
  pbsCarriedDepthResolver_step_eq_historyFirst (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff 1 1 2 (1 / 4) depthControlNoise 2 (fun _ : Unit => carriedBitProfile false)
    unknown who 1 depthControlState depthSampling_not_exception

/-- A missing model is not silently counted as a newly solved unsupported posterior. -/
theorem depthSampling_missing_not_exception :
    ¬ pbsCarriedCFRException (reducedModel fullPrior) 1
      { depthControlState with belief := none } := by
  rintro ⟨_, impossible⟩
  exact impossible

/-- Zero execution fuel cannot create a sampling exception at a live root. -/
theorem depthSampling_stopped_not_exception :
    ¬ pbsCarriedCFRException (reducedModel fullPrior) 0 depthControlState := by
  simp [pbsCarriedCFRException, cfrDCutLive_zero]

/-- First round: search one round, construct one child round, execute one round. -/
def depthSamplingFirst : PBSCarriedDepthParameters (reducedModel fullPrior) where
  cut := 1
  remaining := 1
  fuel := 1
  iterations := 2
  iterations_ne_zero := by decide
  bound := 2
  loss := 1 / 4
  noise := depthControlNoise

/-- The next carried PBS is solved with a different finite iteration count. -/
def depthSamplingLast : PBSCarriedDepthParameters (reducedModel fullPrior) where
  cut := 0
  remaining := 1
  fuel := 1
  iterations := 3
  iterations_ne_zero := by decide
  bound := 2
  loss := 1 / 4
  noise := depthControlNoise

/-- Preserve the already implemented real two-stage execution schedule. -/
theorem depthSampling_existing_schedule :
    [depthSamplingFirst, depthSamplingLast].map
      (pbsCarriedDepthConfiguredStage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
        (fun _ : Unit => carriedBitProfile false)) = depthControlStages := rfl

/-- Numerical error, child tolerance and finite counts are not collapsed to zero. -/
theorem depthSampling_positive_parameters :
    (0 : ℝ) < 1 / 8 ∧ 0 < depthSamplingFirst.loss ∧
      depthSamplingFirst.iterations = 2 ∧ depthSamplingLast.iterations = 3 := by
  norm_num [depthSamplingFirst, depthSamplingLast]

/-- The sharp sampling charge composes with any future reading the retained state. -/
theorem depthSampling_two_stage_first_hit
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (states : FinDist (PrivateIterationState (model fullPrior)
      (CarriedResolveMemory (model fullPrior) Unit)))
    (future : PrivateIterationState (model fullPrior)
      (CarriedResolveMemory (model fullPrior) Unit) → FinDist ((protocol fullPrior).History)) :
    |((pbsCarriedDepthNativeStates (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
        (fun _ : Unit => carriedBitProfile false) unknown who
        [depthSamplingFirst, depthSamplingLast] states).bind future).expect (cfrPayoff who) -
      ((pbsCarriedDepthHistoryFirstStates (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff (fun _ : Unit => carriedBitProfile false) unknown who
        [depthSamplingFirst, depthSamplingLast] states).bind future).expect (cfrPayoff who)| ≤
      4 * pbsCarriedDepthFirstHitProbability (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff (fun _ : Unit => carriedBitProfile false) unknown who
        [depthSamplingFirst, depthSamplingLast] states := by
  have result := pbsCarriedDepthFirstHit_future_error (reducedModel fullPrior)
    pbsRootControlFallback cfrPayoff (fun _ : Unit => carriedBitProfile false) unknown who
    [depthSamplingFirst, depthSamplingLast] states future (cfrPayoff who) 2
    (cfrPayoff_abs_le_two who)
  simpa only [show (2 : ℝ) * 2 = 4 from by norm_num] using result

/-- The actual pre-existing recursive runner receives the same first-hit guarantee. -/
theorem depthSampling_existing_runner_first_hit
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) (finalFuel : Nat)
    (states : FinDist (PrivateIterationState (model fullPrior)
      (CarriedResolveMemory (model fullPrior) Unit))) :
    |(states.bind (executeCarriedResolves (model fullPrior)
        (fun _ : Unit => carriedBitProfile false) unknown who finalFuel depthControlStages)).expect
        (cfrPayoff who) -
      ((pbsCarriedDepthHistoryFirstStates (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff (fun _ : Unit => carriedBitProfile false) unknown who
        [depthSamplingFirst, depthSamplingLast] states).bind
        (carriedSelectedTail (model fullPrior) (fun _ : Unit => carriedBitProfile false)
          unknown who finalFuel)).expect (cfrPayoff who)| ≤
      4 * pbsCarriedDepthFirstHitProbability (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff (fun _ : Unit => carriedBitProfile false) unknown who
        [depthSamplingFirst, depthSamplingLast] states := by
  have result := pbsCarriedDepthFirstHit_execute_error (reducedModel fullPrior)
    pbsRootControlFallback cfrPayoff (fun _ : Unit => carriedBitProfile false) unknown who
    finalFuel [depthSamplingFirst, depthSamplingLast] states (cfrPayoff who) 2
    (cfrPayoff_abs_le_two who)
  simpa only [depthSampling_existing_schedule, show (2 : ℝ) * 2 = 4 from by norm_num] using result

/-- The existing two-stage runner also admits the computed first-exit charge;
the final retained-policy kernel and all private memory are preserved. -/
theorem depthSampling_existing_runner_first_exit
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) (finalFuel : Nat)
    (states : FinDist (PrivateIterationState (model fullPrior)
      (CarriedResolveMemory (model fullPrior) Unit))) :
    |(states.bind (executeCarriedResolves (model fullPrior)
        (fun _ : Unit => carriedBitProfile false) unknown who finalFuel depthControlStages)).expect
        (cfrPayoff who) -
      ((pbsCarriedDepthHistoryFirstStates (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff (fun _ : Unit => carriedBitProfile false) unknown who
        [depthSamplingFirst, depthSamplingLast] states).bind
        (carriedSelectedTail (model fullPrior) (fun _ : Unit => carriedBitProfile false)
          unknown who finalFuel)).expect (cfrPayoff who)| ≤
      pbsCarriedDepthFirstExitCharge (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff (fun _ : Unit => carriedBitProfile false) unknown who
        [depthSamplingFirst, depthSamplingLast] states
        (carriedSelectedTail (model fullPrior) (fun _ : Unit => carriedBitProfile false)
          unknown who finalFuel) (cfrPayoff who) := by
  have same :
      states.bind (executeCarriedResolves (model fullPrior)
          (fun _ : Unit => carriedBitProfile false) unknown who finalFuel depthControlStages) =
        (pbsCarriedDepthNativeStates (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
          (fun _ : Unit => carriedBitProfile false) unknown who
          [depthSamplingFirst, depthSamplingLast] states).bind
          (carriedSelectedTail (model fullPrior) (fun _ : Unit => carriedBitProfile false)
            unknown who finalFuel) := by
    rw [← depthSampling_existing_schedule]
    simp only [pbsCarriedDepthNativeStates, FinDist.bind_bind]
    apply FinDist.bind_congr
    intro state _
    exact pbsCarriedDepthSequence_execute (reducedModel fullPrior) pbsRootControlFallback
      cfrPayoff (fun _ : Unit => carriedBitProfile false) unknown who finalFuel
      [depthSamplingFirst, depthSamplingLast] state
  rw [same]
  exact pbsCarriedDepthFirstExit_future_error (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff (fun _ : Unit => carriedBitProfile false) unknown who
    [depthSamplingFirst, depthSamplingLast] states
    (carriedSelectedTail (model fullPrior) (fun _ : Unit => carriedBitProfile false)
      unknown who finalFuel) (cfrPayoff who)

end GameTheory.ReBeL.Examples.HiddenTypes

namespace GameTheory.ReBeL.Examples.SequentialSampling

open GameTheory.Math.Probability

/-- The first-hit law detects an event absent from every initial-state calculation. -/
theorem late_exception_first_hit :
    FinDist.sequenceFirstHitProbability nativeKernel lateEvent [false, true]
      (FinDist.pure false) = 1 := by
  norm_num [FinDist.sequenceFirstHitProbability, FinDist.sequenceFirstHit, nativeKernel,
    lateEvent, FinDist.prob_bind, FinDist.prob_pure_eq_ite]

/-- The earlier hostile two-stage example attains the new first-hit bound exactly. -/
theorem late_exception_first_hit_sharp :
    |((FinDist.pure false).bind (FinDist.bindSequence nativeKernel [false, true])).expect
        bitValue -
      ((FinDist.pure false).bind (FinDist.bindSequence comparisonKernel [false, true])).expect
        bitValue| =
      2 * FinDist.sequenceFirstHitProbability nativeKernel lateEvent [false, true]
        (FinDist.pure false) := by
  rw [late_exception_error_sharp, late_exception_first_hit, mul_one]

/-- Three guaranteed visits count three times in the old sum but only once as a hit. -/
theorem repeated_exceptions_counted_once :
    FinDist.sequenceFirstHitProbability (fun (_ : Unit) state => FinDist.pure state)
        (fun _ => Set.univ) [(), (), ()] (FinDist.pure false) = 1 ∧
      FinDist.sequenceEventMass (fun (_ : Unit) state => FinDist.pure state)
        (fun _ => Set.univ) [(), (), ()] (FinDist.pure false) = 3 := by
  classical
  constructor
  · norm_num [FinDist.sequenceFirstHitProbability, FinDist.sequenceFirstHit,
      FinDist.prob_bind, FinDist.prob_pure_eq_ite]
  · norm_num [FinDist.sequenceEventMass, ← FinDist.expect_indicator_eq_probOf]

/-- No events gives zero hit probability even for a nonempty schedule. -/
theorem empty_events_have_no_hit :
    FinDist.sequenceFirstHitProbability (fun (_ : Unit) state => FinDist.pure state)
      (fun _ => ∅) [(), (), ()] (FinDist.pure false) = 0 := by
  norm_num [FinDist.sequenceFirstHitProbability, FinDist.sequenceFirstHit,
    FinDist.prob_bind, FinDist.prob_pure_eq_ite]

/-- The witness excludes the safe prefix but includes the unexecuted exceptional stage. -/
theorem late_exception_first_exit :
    FinDist.sequenceFirstExit nativeKernel lateEvent [false, true] false =
      FinDist.pure (some ([true], true)) := by
  norm_num [FinDist.sequenceFirstExit, nativeKernel, lateEvent]

/-- Even different complete executions have the same first-exit witnesses. -/
theorem first_exit_kernel_invariance (stages : List Bool) (state : Bool) :
    FinDist.sequenceFirstExit nativeKernel lateEvent stages state =
      FinDist.sequenceFirstExit comparisonKernel lateEvent stages state :=
  FinDist.sequenceFirstExit_eq_of_eq_off_event nativeKernel comparisonKernel lateEvent
    kernels_agree_outside stages state

/-- Repeated event labels retain the first occurrence, not the last or an empty suffix. -/
theorem first_exit_keeps_first_suffix :
    FinDist.sequenceFirstExit (fun (_ : Unit) state => FinDist.pure state)
      (fun _ => Set.univ) [(), (), ()] false =
      FinDist.pure (some ([(), (), ()], false)) := by
  simp [FinDist.sequenceFirstExit]

/-- No-exception completion has no invented stopping history or suffix. -/
theorem first_exit_absent :
    FinDist.sequenceFirstExit (fun (_ : Unit) state => FinDist.pure state)
      (fun _ => ∅) [(), (), ()] false = FinDist.pure none := by
  simp [FinDist.sequenceFirstExit]

/-- The signed witness value keeps the orientation of the full native-minus-comparison gap. -/
theorem late_exception_first_exit_value :
    FinDist.sequenceFirstExitValue nativeKernel comparisonKernel
      (fun state => FinDist.pure state) bitValue (some ([true], true)) = -2 := by
  norm_num [FinDist.sequenceFirstExitValue, FinDist.bindSequence,
    nativeKernel, comparisonKernel, bitValue]

/-- A future erasing the difference gives zero refined charge despite hit probability one. -/
theorem first_exit_harmless_future :
    (FinDist.sequenceFirstExit nativeKernel lateEvent [false, true] false).expect
        (fun witness => |FinDist.sequenceFirstExitValue nativeKernel comparisonKernel
          (fun _ => FinDist.pure true) bitValue witness|) = 0 ∧
      FinDist.sequenceFirstHitProbability nativeKernel lateEvent [false, true]
        (FinDist.pure false) = 1 := by
  constructor
  · rw [late_exception_first_exit]
    norm_num [FinDist.sequenceFirstExitValue, bitValue]
  · exact late_exception_first_hit

/-- A nondegenerate actual law catches accidental normalization to zero or one. -/
def fractionalExitRoot : FinDist Bool :=
  FinDist.mix (1 / 4) (by norm_num) (by norm_num) (FinDist.pure true) (FinDist.pure false)

/-- First-exit probability remains fractional, including the no-hit branch. -/
theorem fractional_first_exit_probability :
    FinDist.sequenceFirstHitProbability nativeKernel lateEvent [true] fractionalExitRoot =
      1 / 4 := by
  norm_num [FinDist.sequenceFirstHitProbability, fractionalExitRoot, FinDist.prob_bind,
    FinDist.expect_mix, FinDist.sequenceFirstHit, nativeKernel, lateEvent,
    FinDist.prob_pure_eq_ite]

/-- The computed charge is sharp at a genuinely fractional stopping probability. -/
theorem fractional_first_exit_charge :
    (fractionalExitRoot.bind (FinDist.sequenceFirstExit nativeKernel lateEvent [true])).expect
        (fun witness => |FinDist.sequenceFirstExitValue nativeKernel comparisonKernel
          (fun state => FinDist.pure state) bitValue witness|) = 1 / 2 := by
  norm_num [fractionalExitRoot, FinDist.expect_bind, FinDist.expect_mix,
    FinDist.sequenceFirstExit, FinDist.sequenceFirstExitValue, FinDist.bindSequence,
    nativeKernel, comparisonKernel, lateEvent, bitValue]

end GameTheory.ReBeL.Examples.SequentialSampling
