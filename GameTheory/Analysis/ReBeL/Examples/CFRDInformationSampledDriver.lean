/-
# Sampled noisy-parent controls

A genuine reference-supported but factually absent live query uses the sampled
branch. Positive child loss and prediction bias remain in the actual parent
recurrence. Zero remaining fuel exercises the unsupported-entry convention.
-/

import GameTheory.Analysis.ReBeL.CFRDInformationSampledDriver
import GameTheory.Analysis.ReBeL.Examples.PBSInformationSampling

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Enumerate all canonical legal histories, including off-path histories. -/
local instance sampledParentHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Retain inactive menus as well as actual decision menus. -/
local instance sampledParentChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Equality is confined to the noncomputable reference solver. -/
local instance sampledParentInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- Zero factual mass does not discard this genuine live reference query.
Its prediction includes a nonzero numerical bias and a positive child budget. -/
theorem sampledParentControl_off_path_prediction :
    (cfrDConstructedSampledInformationOracle (reducedModel fullPrior) pbsRootControlFallback
      cfrPayoff 2 1 2 (1 / 4) (fun _ _ _ _ => 1 / 8) 3
      (carriedBitProfile false)).prediction 0
        ((model fullPrior).infoOf 0 zeroControlHistory.trace) =
      (cfrDInformationQuerySample (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 (fun h who => cfrPayoff who h) 2 (1 / 4)
        0 ((model fullPrior).infoOf 0 zeroControlHistory.trace)
        (cfrDInformationContinuation (reducedModel fullPrior) (carriedBitProfile false)
          pbsRootControlFallback 2 1 (fun h who => cfrPayoff who h) 2 (1 / 4)) 1).expect
            (cfrPayoff 0) + 1 / 8 :=
  cfrDConstructedSampledInformationOracle_prediction (reducedModel fullPrior)
    pbsRootControlFallback cfrPayoff 2 1 2 (1 / 4) (fun _ _ _ _ => 1 / 8) 3
    (carriedBitProfile false) 0 ((model fullPrior).infoOf 0 zeroControlHistory.trace)
    informationSamplingControl_zero_query_sampled

/-- Equality is about the actual coupled state, not a supplied policy sequence. -/
theorem sampledParentControl_biased_state (n : Nat) :
    cfrDState (model fullPrior)
        (cfrDDepthTrunk (model fullPrior) (fullObservationClock (reducedModel fullPrior)) 2)
        informationControlFullFallback
        (cfrDDepthOracle (model fullPrior) (fullObservationClock (reducedModel fullPrior))
          informationControlFullFallback cfrPayoff 2 1
          (cfrDConstructedSampledInformationOracle (reducedModel fullPrior)
            pbsRootControlFallback cfrPayoff 2 1 2 (1 / 4) (fun _ _ _ _ => 1 / 8))) n =
      cfrDState (model fullPrior)
        (cfrDDepthTrunk (model fullPrior) (fullObservationClock (reducedModel fullPrior)) 2)
        informationControlFullFallback
        (cfrDDepthOracle (model fullPrior) (fullObservationClock (reducedModel fullPrior))
          informationControlFullFallback cfrPayoff 2 1
          (cfrDConstructedInformationOracle (reducedModel fullPrior)
            pbsRootControlFallback cfrPayoff 2 1 2 (1 / 4) (fun _ _ _ _ => 1 / 8))) n :=
  cfrDConstructedSampledInformationOracle_state_eq (reducedModel fullPrior)
    pbsRootControlFallback cfrPayoff 2 1 2 (1 / 4) (fun _ _ _ _ => 1 / 8) n

/-- At zero remaining fuel no live query exists; vector entries retain their
reference convention rather than inventing a sampled live posterior. -/
theorem sampledParentControl_zero_remaining
    (trunk : Profile (model fullPrior).behavioralSignature) (n : Nat) (who : Player)
    (info : (model fullPrior).InfoState who) :
    (cfrDConstructedSampledInformationOracle (reducedModel fullPrior) pbsRootControlFallback
      cfrPayoff 2 0 2 (1 / 4) (fun _ _ _ _ => 1 / 8) n trunk).prediction who info =
    (cfrDConstructedInformationOracle (reducedModel fullPrior) pbsRootControlFallback
      cfrPayoff 2 0 2 (1 / 4) (fun _ _ _ _ => 1 / 8) n trunk).prediction who info := by
  classical
  have absent : ¬ CFRDInformationQuerySampled (reducedModel fullPrior) trunk
      pbsRootControlFallback 2 0 who info := by
    rw [CFRDInformationQuerySampled, FinDist.support_map]
    rintro ⟨history, _reached, same⟩
    have impossible : (false : Bool) = true := by
      simpa only [cfrDCutLive_zero] using congrArg Prod.snd same
    cases impossible
  exact if_neg absent

end GameTheory.ReBeL.Examples.HiddenTypes
