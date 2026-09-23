/-
# Carried-PBS native-iteration controls

Use a factual live joint posterior in the canonical hidden-type protocol.
The tests keep arbitrary unknown opponents, actual iteration indices, retained
model updates, missing beliefs, and zero execution fuel separate. Finite-law
negative controls do not pretend to refute the source game-level theorem.
-/

import GameTheory.Analysis.ReBeL.PBSCarriedSampling
import GameTheory.Analysis.ReBeL.Examples.PBSInformationSampling

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Use the actual canonical finite history enumeration. -/
local instance carriedSamplingHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- A real live state with the factual joint PBS, not an arbitrary posterior witness. -/
def carriedSamplingControlState : PrivateIterationState (model fullPrior) Unit where
  iteration := ()
  history := factualChildHistory
  belief := some finiteBudgetControlBelief

/-- Another strategic decision remains after the observed prefix. -/
theorem carriedSamplingControl_live :
    cfrDCutLive 1 carriedSamplingControlState.history = true := by
  classical
  rw [cfrDCutLive, decide_eq_true_eq]
  exact ⟨by decide, fun impossible => impossible⟩

/-- The actual state belongs to its stored posterior by canonical conditioning. -/
theorem carriedSamplingControl_supported :
    factualChildHistory ∈ finiteBudgetControlBelief.law.support := by
  exact FinDist.mem_support_condOn _ _ factualChild_possible
    ⟨rfl, carriedSamplingControl_live⟩ factualChildHistory_supported

/-- The positive example does not assume away a support failure. -/
theorem carriedSamplingControl_not_exception :
    ¬ pbsCarriedCFRException (reducedModel fullPrior) 1 carriedSamplingControlState := by
  rintro ⟨_, unsupported⟩
  exact unsupported carriedSamplingControl_supported

/-- The supplied carried PBS, rather than the retained parent family, determines
all native child iterates. The old family may be an entirely different policy. -/
theorem carriedSamplingControl_uses_incoming_belief :
    pbsCarriedCFRResolver (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 1 2
        (fun _ : Unit => carriedBitProfile false) () _ (some finiteBudgetControlBelief) =
      pbsCarriedCFRResolver (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 1 2
        (fun _ : Unit => carriedBitProfile true) () _ (some finiteBudgetControlBelief) := rfl

/-- A live private draw of actual child iterations has the correct history law
against every fixed unknown opponent, at a genuinely supported carried root. -/
theorem carriedSamplingControl_live_tail
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    carriedResolvedTail (model fullPrior)
        (pbsCarriedCFRResolver (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 1 2
          (fun _ : Unit => carriedBitProfile false)) unknown who 1 carriedSamplingControlState =
      carriedResolvedTail (model fullPrior)
        (pbsCarriedCFRAverageResolver (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 1 2 (fun _ : Unit => carriedBitProfile false))
        unknown who 1 carriedSamplingControlState :=
  pbsCarriedCFRResolver_tail_eq_average (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff 1 2 (fun _ : Unit => carriedBitProfile false) unknown who 1
    carriedSamplingControlState carriedSamplingControl_not_exception

/-- The selected iterate and the posterior propagated through that SAME iterate
remain paired. An average of history laws is not used to reset the posterior. -/
theorem carriedSamplingControl_joint_step
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    carriedResolvedStep (model fullPrior) (fun _ : Unit => carriedBitProfile false)
      (pbsCarriedCFRResolver (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 1 2
        (fun _ : Unit => carriedBitProfile false)) unknown who 1 carriedSamplingControlState =
      (cfrIterationLaw 2).bind (fun n =>
        ((model fullPrior).runBehavioralFrom
          (Profile.update unknown who (pbsInformationCFRIterate (reducedModel fullPrior)
            finiteBudgetControlBelief pbsRootControlFallback cfrPayoff 1 n.val who))
          1 factualChildHistory).map (resolvedNextState (model fullPrior)
            carriedSamplingControlState (pbsInformationCFRIterate (reducedModel fullPrior)
              finiteBudgetControlBelief pbsRootControlFallback cfrPayoff 1 n.val) 1)) :=
  pbsCarriedCFRResolver_step_some (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
    1 2 (fun _ : Unit => carriedBitProfile false) unknown who 1 carriedSamplingControlState
    finiteBudgetControlBelief rfl carriedSamplingControl_live

/-- With no model belief there is no fabricated child root or fresh iteration draw. -/
theorem carriedSamplingControl_missing_belief :
    pbsCarriedCFRResolver (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 1 2
        (fun _ : Unit => carriedBitProfile false) ()
        (publicTrace (model fullPrior).toInfoSignals factualChildHistory.trace) none =
      FinDist.pure (carriedBitProfile false) := rfl

/-- A live incoming state with zero allowed execution fuel bypasses the solver. -/
theorem carriedSamplingControl_zero_fuel
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    carriedResolvedTail (model fullPrior)
        (pbsCarriedCFRResolver (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 1 2
          (fun _ : Unit => carriedBitProfile false)) unknown who 0 carriedSamplingControlState =
      FinDist.pure factualChildHistory := by
  simp only [carriedResolvedTail, cfrDCutLive_zero, Bool.false_eq_true, if_false,
    carriedSamplingControlState]

/-- Arbitrary actual incoming state laws are admitted, including model-unsupported
histories. The payoff bound two yields the explicit four-times-event-mass error. -/
theorem carriedSamplingControl_actual_error
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (states : FinDist (PrivateIterationState (model fullPrior) Unit)) :
    |(states.bind (carriedResolvedTail (model fullPrior)
        (pbsCarriedCFRResolver (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 1 2
          (fun _ : Unit => carriedBitProfile false)) unknown who 1)).expect (cfrPayoff who) -
      (states.bind (carriedResolvedTail (model fullPrior)
        (pbsCarriedCFRAverageResolver (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 1 2 (fun _ : Unit => carriedBitProfile false)) unknown who 1)).expect
          (cfrPayoff who)| ≤
      4 * states.probOf {state | pbsCarriedCFRException (reducedModel fullPrior) 1 state} := by
  have error := pbsCarriedCFRResolver_actual_error (reducedModel fullPrior)
    pbsRootControlFallback cfrPayoff 1 2 (fun _ : Unit => carriedBitProfile false)
    unknown who 1 states (cfrPayoff who) 2 (cfrPayoff_abs_le_two who)
  simpa only [show (2 : ℝ) * 2 = 4 from by norm_num] using error

/-- At the genuine supported root, the full private-state distribution is
recovered by the native conditional law after sampling the average history. -/
theorem carriedSamplingControl_joint_disintegration
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    carriedResolvedStep (model fullPrior) (fun _ : Unit => carriedBitProfile false)
        (pbsCarriedCFRResolver (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 1 2
          (fun _ : Unit => carriedBitProfile false)) unknown who 1 carriedSamplingControlState =
      pbsCarriedCFRHistoryFirstStep (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
        1 2 (fun _ : Unit => carriedBitProfile false) unknown who 1 carriedSamplingControlState :=
  pbsCarriedCFRResolver_step_eq_historyFirst (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff 1 2 (fun _ : Unit => carriedBitProfile false) unknown who 1
    carriedSamplingControlState carriedSamplingControl_not_exception

/-- The same explicit event allowance survives any following finite execution,
even one which inspects the retained private profile and its model posterior. -/
theorem carriedSamplingControl_future_error
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (states : FinDist (PrivateIterationState (model fullPrior) Unit))
    (future : PrivateIterationState (model fullPrior)
      (Unit × Profile (model fullPrior).behavioralSignature) →
        FinDist ((protocol fullPrior).History)) :
    |((states.bind (carriedResolvedStep (model fullPrior)
        (fun _ : Unit => carriedBitProfile false)
        (pbsCarriedCFRResolver (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 1 2
          (fun _ : Unit => carriedBitProfile false)) unknown who 1)).bind future).expect
          (cfrPayoff who) -
      ((states.bind (pbsCarriedCFRHistoryFirstStep (reducedModel fullPrior)
        pbsRootControlFallback cfrPayoff 1 2 (fun _ : Unit => carriedBitProfile false)
        unknown who 1)).bind future).expect (cfrPayoff who)| ≤
      4 * states.probOf {state | pbsCarriedCFRException (reducedModel fullPrior) 1 state} := by
  have error := pbsCarriedCFRHistoryFirstStep_future_error (reducedModel fullPrior)
    pbsRootControlFallback cfrPayoff 1 2 (fun _ : Unit => carriedBitProfile false)
    unknown who 1 states future (cfrPayoff who) 2 (cfrPayoff_abs_le_two who)
  simpa only [show (2 : ℝ) * 2 = 4 from by norm_num] using error

/-- Two successive native stages can use different finite counts without
changing the existing runner or discarding its retained private profile list. -/
def carriedSamplingControlStages : List (CarriedResolveStage (model fullPrior) Unit) :=
  [pbsCarriedCFRStage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 1 2
      (fun _ : Unit => carriedBitProfile false),
    pbsCarriedCFRStage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 1 1 3
      (fun _ : Unit => carriedBitProfile false)]

/-- The finite schedule has exactly two canonical transitions available. -/
theorem carriedSamplingControl_schedule_fuel :
    carriedResolveFuel (model fullPrior) 0 carriedSamplingControlStages = 2 := rfl

end GameTheory.ReBeL.Examples.HiddenTypes

namespace GameTheory.ReBeL.Examples.CarriedSampling

open GameTheory.Math.Probability

/-- Charging an exceptional event is necessary in the general kernel lemma:
a unit-mass exception attains the complete two-times-bound error. -/
theorem exceptional_event_sharp :
    |(FinDist.pure false).expect (fun _ => (1 : ℝ)) -
        (FinDist.pure false).expect (fun flag => if flag then (1 : ℝ) else -1)| = 2 ∧
      (FinDist.pure false).probOf {flag : Bool | flag = false} = 1 := by
  constructor
  · norm_num [FinDist.expect_pure]
  · rw [← FinDist.expect_indicator_eq_probOf]
    simp [FinDist.expect_pure]

/-- Equal observed-history marginals alone do not determine a later transition
that reads retained private state. This guards against silently replacing the
full carried-state law by the averaged history marginal. -/
theorem history_marginal_not_future_law :
    (FinDist.pure (false, false)).map Prod.fst =
        (FinDist.pure (false, true)).map Prod.fst ∧
      (FinDist.pure (false, false)).bind (fun state => FinDist.pure state.2) ≠
        (FinDist.pure (false, true)).bind (fun state => FinDist.pure state.2) := by
  constructor
  · simp only [FinDist.map_pure]
  · intro equal
    have values := congrArg (fun law : FinDist Bool =>
      law.expect (fun flag => if flag then (1 : ℝ) else 0)) equal
    norm_num [FinDist.pure_bind, FinDist.expect_pure] at values

end GameTheory.ReBeL.Examples.CarriedSampling
