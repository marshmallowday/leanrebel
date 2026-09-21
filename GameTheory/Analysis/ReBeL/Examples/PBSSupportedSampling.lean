/-
# Supported-root and conditional-law controls for child iteration sampling

The live hidden-type solver is evaluated at individual supported roots and
changed root probabilities. A finite negative control shows why cancelling
a zero-mass root from a mixture would be an invalid inference.
-/

import GameTheory.Analysis.ReBeL.PBSSupportedSampling
import GameTheory.Analysis.ReBeL.Examples.CFRDInformationChild

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

local instance supportedSamplingHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- The live child works root by root, not only after averaging its prior. -/
theorem supportedSamplingControl_single_root
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (history : (protocol fullPrior).History)
    (supported : history ∈ finiteBudgetControlBelief.law.support) :
    pbsInformationCFR_sampleFrom (reducedModel fullPrior) finiteBudgetControlBelief
        pbsRootControlFallback cfrPayoff 1 2 unknown who 1 history =
      (model fullPrior).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFR (reducedModel fullPrior)
          finiteBudgetControlBelief pbsRootControlFallback cfrPayoff 1 2 who)) 1 history :=
  pbsInformationCFR_sampling_from_support (reducedModel fullPrior) finiteBudgetControlBelief
    pbsRootControlFallback cfrPayoff 1 2 unknown who 1 history supported

/-- Concentrating the actual law at any supported hidden root preserves the
solver's law without identifying this point mass with the model posterior. -/
theorem supportedSamplingControl_pure_reweight
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (history : (protocol fullPrior).History)
    (supported : history ∈ finiteBudgetControlBelief.law.support) :
    (FinDist.pure history).bind
        (pbsInformationCFR_sampleFrom (reducedModel fullPrior) finiteBudgetControlBelief
          pbsRootControlFallback cfrPayoff 1 2 unknown who 1) =
      (model fullPrior).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFR (reducedModel fullPrior)
          finiteBudgetControlBelief pbsRootControlFallback cfrPayoff 1 2 who)) 1 history := by
  rw [FinDist.pure_bind]
  exact supportedSamplingControl_single_root unknown who history supported

/-- Zero execution fuel is absorbing even without model support. This boundary
fact is weaker than a positive-fuel guarantee outside that support. -/
theorem supportedSamplingControl_zero_fuel
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (history : (protocol fullPrior).History) :
    pbsInformationCFR_sampleFrom (reducedModel fullPrior) finiteBudgetControlBelief
      pbsRootControlFallback cfrPayoff 1 2 unknown who 0 history = FinDist.pure history := by
  unfold pbsInformationCFR_sampleFrom
  have stopped (n : Fin 2) : (model fullPrior).runBehavioralFrom
      (Profile.update unknown who (pbsInformationCFRIterate (reducedModel fullPrior)
        finiteBudgetControlBelief pbsRootControlFallback cfrPayoff 1 n.val who))
      0 history = FinDist.pure history := rfl
  simp only [stopped, FinDist.bind_const]

/-- Type conditioning can change every positive root probability, while the
same child's complete value observable is still preserved. -/
theorem supportedSamplingControl_reweighted_value
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (actual : FinDist (protocol fullPrior).History)
    (dominated : ∀ h ∈ actual.support, h ∈ finiteBudgetControlBelief.law.support) :
    (actual.bind (pbsInformationCFR_sampleFrom (reducedModel fullPrior)
      finiteBudgetControlBelief pbsRootControlFallback cfrPayoff 1 2 unknown who 1)).expect
        (cfrPayoff who) =
      (actual.bind ((model fullPrior).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFR (reducedModel fullPrior)
          finiteBudgetControlBelief pbsRootControlFallback cfrPayoff 1 2 who)) 1)).expect
            (cfrPayoff who) :=
  pbsInformationCFR_sampling_reweighted_value (reducedModel fullPrior)
    finiteBudgetControlBelief pbsRootControlFallback cfrPayoff 1 2 unknown who 1 actual
    dominated (cfrPayoff who)

/-- Equality of mixtures cannot recover an omitted root's kernel. A zero-mass
root needs separate completion, not division by zero or unsupported cancellation. -/
theorem supportedSamplingControl_zero_mass_cannot_cancel :
    ∃ (prior : FinDist Bool) (first second : Bool → FinDist Bool),
      prior.bind first = prior.bind second ∧ first true ≠ second true := by
  refine ⟨FinDist.pure false, (fun _ => FinDist.pure false),
    (fun bit => FinDist.pure bit), ?_, ?_⟩
  · simp only [FinDist.pure_bind]
  · intro equal
    have impossible := congrArg (fun law : FinDist Bool => law.prob true) equal
    norm_num [FinDist.prob_pure_eq_ite] at impossible

end GameTheory.ReBeL.Examples.HiddenTypes
