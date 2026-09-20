/-
# Multiple live coherent draws and zero-fuel stage controls

Two positive stages cover the two remaining HiddenTypes strategic rounds.
An intervening zero-fuel stage retains canonical no-query behavior. The
exact history law, rather than only a utility bound, is checked.
-/

import GameTheory.Analysis.ReBeL.CFRDCoherentStages
import GameTheory.Analysis.ReBeL.Examples.CFRDCoherentDraw

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- The inherited canonical history enumeration, with no new execution model. -/
local instance coherentStagesHistory : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- A private two-stage realization starting before both strategic rounds has
the original joint history law against any fixed unknown behavioral opponent. -/
theorem coherent_two_live_stages
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    privateRecursiveResolve (model fullPrior) (FinDist.pure ())
        (fun _ : Unit => liveFairContinuation) unknown who 1 0
        ([1, 0, 1].map (cfrDCoherentStage (model fullPrior) cfrFallback
          (fun _ : Unit => liveFairContinuation))) =
      privateCarriedContinue (model fullPrior) (FinDist.pure ())
        (fun _ : Unit => liveFairContinuation) unknown who 1 2 := by
  simpa only [List.sum_cons, List.sum_nil, Nat.add_zero] using
    cfrDCoherentStages_recursive_eq (model fullPrior) (perfectRecall fullPrior) cfrFallback
      (FinDist.pure ()) (fun _ : Unit => liveFairContinuation) unknown who 1 [1, 0, 1]

/-- Full private memory and a possibly absent carried model belief do not
enter the source policy selection. The exact law holds from every such state. -/
theorem coherent_stages_arbitrary_memory
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (state : PrivateIterationState (model fullPrior)
      (CarriedResolveMemory (model fullPrior) Unit)) :
    executeCarriedResolves (model fullPrior) (fun _ : Unit => liveFairContinuation)
        unknown who 0
        ([1, 0, 1].map (cfrDCoherentStage (model fullPrior) cfrFallback
          (fun _ : Unit => liveFairContinuation))) state =
      (model fullPrior).runBehavioralFrom
        (Profile.update unknown who (liveFairContinuation who)) 2 state.history := by
  simpa only [List.sum_cons, List.sum_nil, Nat.add_zero] using
    cfrDCoherentStages_run (model fullPrior) (perfectRecall fullPrior) cfrFallback
      (fun _ : Unit => liveFairContinuation) unknown who [1, 0, 1] state

end GameTheory.ReBeL.Examples.HiddenTypes
