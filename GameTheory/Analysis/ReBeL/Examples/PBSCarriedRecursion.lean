/-
# Multi-stage carried sampling controls

The hidden-type controls use the existing native schedule with different
iteration counts. The independent two-state controls catch charging every
event under the initial law instead of the actual successive prefix laws.
They refute that invalid proof shortcut, not the paper's Theorem 3.
-/

import GameTheory.Analysis.ReBeL.PBSCarriedRecursion
import GameTheory.Analysis.ReBeL.Examples.PBSCarriedSampling

noncomputable section

namespace GameTheory.ReBeL.Examples.SequentialSampling

open GameTheory.Math.Probability

/-- Both executions first move to true; the native second stage moves to false. -/
def nativeKernel (stage : Bool) (_state : Bool) : FinDist Bool := FinDist.pure (!stage)

/-- The comparison agrees at stage one and preserves the reached bit at stage two. -/
def comparisonKernel (stage state : Bool) : FinDist Bool :=
  FinDist.pure (if stage then state else true)

/-- The sole exception occurs at the second stage, in a state absent initially. -/
def lateEvent (stage : Bool) : Set Bool := {state | stage = true ∧ state = true}

/-- A bounded final observable distinguishes the resulting complete laws. -/
def bitValue (state : Bool) : ℝ := if state then 1 else -1

/-- The local equality used by the generic hybrid lemma is proved, not assumed. -/
theorem kernels_agree_outside (stage state : Bool) (outside : state ∉ lateEvent stage) :
    nativeKernel stage state = comparisonKernel stage state := by
  cases stage <;> cases state <;> simp_all [nativeKernel, comparisonKernel, lateEvent]

/-- The observable has bound one on the entire finite state space. -/
theorem bitValue_bounded (state : Bool) : |bitValue state| ≤ 1 := by
  cases state <;> norm_num [bitValue]

/-- Both stage events have zero probability at the INITIAL law. Using these
masses in a recursive error bound would incorrectly predict zero total error. -/
theorem initial_events_miss_later_exception :
    (FinDist.pure false).probOf (lateEvent false) +
      (FinDist.pure false).probOf (lateEvent true) = 0 := by
  classical
  simp [← FinDist.expect_indicator_eq_probOf, FinDist.expect_pure, lateEvent]

/-- The native prefix actually reaches the second event with probability one. -/
theorem actual_forward_exception_mass :
    FinDist.sequenceEventMass nativeKernel lateEvent [false, true] (FinDist.pure false) = 1 := by
  classical
  simp [FinDist.sequenceEventMass, nativeKernel, FinDist.pure_bind,
    ← FinDist.expect_indicator_eq_probOf, FinDist.expect_pure, lateEvent]

/-- The two-stage discrepancy is nonzero and attains twice the payoff bound. -/
theorem late_exception_error_sharp :
    |((FinDist.pure false).bind (FinDist.bindSequence nativeKernel [false, true])).expect
        bitValue -
      ((FinDist.pure false).bind (FinDist.bindSequence comparisonKernel [false, true])).expect
        bitValue| = 2 := by
  norm_num [FinDist.bindSequence, nativeKernel, comparisonKernel, bitValue,
    FinDist.pure_bind, FinDist.expect_pure]

/-- The proved hybrid bound uses the correct forward mass in this hostile case. -/
theorem late_exception_hybrid_bound :
    |((FinDist.pure false).bind (FinDist.bindSequence nativeKernel [false, true])).expect
        bitValue -
      ((FinDist.pure false).bind (FinDist.bindSequence comparisonKernel [false, true])).expect
        bitValue| ≤
      2 * FinDist.sequenceEventMass nativeKernel lateEvent [false, true] (FinDist.pure false) := by
  have result := FinDist.abs_expect_sequence_sub_le_of_eq_off_event nativeKernel comparisonKernel
    lateEvent kernels_agree_outside bitValue 1 bitValue_bounded [false, true] (FinDist.pure false)
  simpa only [mul_one] using result

end GameTheory.ReBeL.Examples.SequentialSampling

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Reuse the proved canonical enumeration, not an assumed finite PBS carrier. -/
local instance recursiveSamplingHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Two real native solves with distinct positive counts and training horizons. -/
def recursiveSamplingParameters : List PBSCarriedCFRParameters :=
  [⟨2, 1, 2, by decide⟩, ⟨1, 1, 3, by decide⟩]

/-- The parameterized interface is definitionally the previously tested schedule. -/
theorem recursiveSampling_existing_schedule :
    recursiveSamplingParameters.map
      (pbsCarriedCFRConfiguredStage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
        (fun _ : Unit => carriedBitProfile false)) = carriedSamplingControlStages := rfl

/-- At the genuine supported live root, flattening memory preserves equality
of complete next-state laws, including the propagated model posterior. -/
theorem recursiveSampling_live_stored_step
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    carriedMemoryStep (model fullPrior) (fun _ : Unit => carriedBitProfile false) unknown who
        (pbsCarriedCFRConfiguredStage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
          (fun _ : Unit => carriedBitProfile false) ⟨2, 1, 2, by decide⟩)
        (enterCarriedMemory (model fullPrior) carriedSamplingControlState) =
      pbsCarriedCFRHistoryFirstMemoryStep (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
        (fun _ : Unit => carriedBitProfile false) unknown who ⟨2, 1, 2, by decide⟩
        (enterCarriedMemory (model fullPrior) carriedSamplingControlState) := by
  apply pbsCarriedCFRConfiguredStep_eq_historyFirst
  exact carriedSamplingControl_not_exception

/-- Every subsequent finite observation, including one reading private memory,
obeys the two-stage bound. No support condition on the actual input law is supplied. -/
theorem recursiveSampling_two_stage_future_error
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (states : FinDist (PrivateIterationState (model fullPrior)
      (CarriedResolveMemory (model fullPrior) Unit)))
    (future : PrivateIterationState (model fullPrior)
      (CarriedResolveMemory (model fullPrior) Unit) → FinDist ((protocol fullPrior).History)) :
    |((pbsCarriedCFRNativeStates (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
        (fun _ : Unit => carriedBitProfile false) unknown who recursiveSamplingParameters
        states).bind future).expect (cfrPayoff who) -
      ((pbsCarriedCFRHistoryFirstStates (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
        (fun _ : Unit => carriedBitProfile false) unknown who recursiveSamplingParameters
        states).bind future).expect (cfrPayoff who)| ≤
      4 * pbsCarriedCFRSequenceExceptionMass (reducedModel fullPrior)
        pbsRootControlFallback cfrPayoff (fun _ : Unit => carriedBitProfile false)
        unknown who recursiveSamplingParameters states := by
  have result := pbsCarriedCFRSequence_future_error (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff (fun _ : Unit => carriedBitProfile false) unknown who recursiveSamplingParameters
    states future (cfrPayoff who) 2 (cfrPayoff_abs_le_two who)
  simpa only [show (2 : ℝ) * 2 = 4 from by norm_num] using result

/-- The SAME bound applies to the existing runner's old two-stage schedule,
not only to a newly defined state-law expression. The final horizon stays explicit. -/
theorem recursiveSampling_existing_runner_error
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) (finalFuel : Nat)
    (states : FinDist (PrivateIterationState (model fullPrior)
      (CarriedResolveMemory (model fullPrior) Unit))) :
    |(states.bind (executeCarriedResolves (model fullPrior)
        (fun _ : Unit => carriedBitProfile false) unknown who finalFuel
        carriedSamplingControlStages)).expect (cfrPayoff who) -
      ((pbsCarriedCFRHistoryFirstStates (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
        (fun _ : Unit => carriedBitProfile false) unknown who
        recursiveSamplingParameters states).bind
        (carriedSelectedTail (model fullPrior) (fun _ : Unit => carriedBitProfile false)
          unknown who finalFuel)).expect (cfrPayoff who)| ≤
      4 * pbsCarriedCFRSequenceExceptionMass (reducedModel fullPrior)
        pbsRootControlFallback cfrPayoff (fun _ : Unit => carriedBitProfile false)
        unknown who recursiveSamplingParameters states := by
  have result := pbsCarriedCFRSequence_execute_error (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff (fun _ : Unit => carriedBitProfile false) unknown who finalFuel
    recursiveSamplingParameters states (cfrPayoff who) 2 (cfrPayoff_abs_le_two who)
  simpa only [recursiveSampling_existing_schedule, show (2 : ℝ) * 2 = 4 from by norm_num]
    using result

end GameTheory.ReBeL.Examples.HiddenTypes
