/-
# Controls for actual child-iteration sampling

These use the canonical live hidden-type posterior and the information-set
recurrence. Unknown opponents, a randomized opponent, zero execution fuel,
posterior-dependent counts and the parent's public splice remain explicit.
-/

import GameTheory.Analysis.ReBeL.CFRDInformationSampling
import GameTheory.Analysis.ReBeL.Examples.CFRDInformationChild

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- The canonical hidden-type protocol has explicitly enumerated legal histories. -/
local instance samplingControlHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- The actual two-iteration law is uniform, not a last-iterate selection. -/
theorem informationSamplingControl_uniform_two :
    (cfrIterationLaw 2).prob 0 = 1 / 2 ∧ (cfrIterationLaw 2).prob 1 = 1 / 2 := by
  norm_num [cfrIterationLaw, FinDist.prob_ofWeights]

/-- Every prescribed conditional budget produces a nonempty private draw. -/
theorem informationSamplingControl_count_positive (loss : ℝ) :
    0 < pbsInformationConditionalRounds (reducedModel fullPrior)
      finiteBudgetControlBelief 1 2 loss :=
  Nat.pos_of_ne_zero (NeZero.ne _)

/-- The live child's entire continuation law agrees against arbitrary opponents. -/
theorem informationSamplingControl_live (t : Nat) [NeZero t]
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    (cfrIterationLaw t).bind (fun n => finiteBudgetControlBelief.law.bind
      ((model fullPrior).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFRIterate (reducedModel fullPrior)
          finiteBudgetControlBelief pbsRootControlFallback cfrPayoff 1 n.val who)) 1)) =
      finiteBudgetControlBelief.law.bind ((model fullPrior).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFR (reducedModel fullPrior)
          finiteBudgetControlBelief pbsRootControlFallback cfrPayoff 1 t who)) 1) :=
  pbsInformationCFR_sampling_law (reducedModel fullPrior) finiteBudgetControlBelief
    pbsRootControlFallback cfrPayoff 1 t unknown who 1

/-- Fresh opponent randomization is held outside the selected child index. -/
theorem informationSamplingControl_randomized_opponent (loss : ℝ) :
    pbsInformationConditionalSample (reducedModel fullPrior) finiteBudgetControlBelief
        pbsRootControlFallback 1 (fun h who => cfrPayoff who h) 2 loss
        (Profile.update (carriedBitProfile false) 0 freshBitPolicy) 1 1 =
      finiteBudgetControlBelief.law.bind ((model fullPrior).runBehavioralFrom
        (Profile.update (Profile.update (carriedBitProfile false) 0 freshBitPolicy) 1
          (pbsInformationConditionalProfile (reducedModel fullPrior) finiteBudgetControlBelief
            pbsRootControlFallback 1 (fun h who => cfrPayoff who h) 2 loss 1)) 1) :=
  pbsInformationConditionalSample_eq (reducedModel fullPrior) finiteBudgetControlBelief
    pbsRootControlFallback 1 (fun h who => cfrPayoff who h) 2 loss
    (Profile.update (carriedBitProfile false) 0 freshBitPolicy) 1 1

/-- With zero execution fuel the private draw cannot change the joint root law. -/
theorem informationSamplingControl_zero_fuel (loss : ℝ)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    pbsInformationConditionalSample (reducedModel fullPrior) finiteBudgetControlBelief
      pbsRootControlFallback 1 (fun h player => cfrPayoff player h) 2 loss unknown who 0 =
        finiteBudgetControlBelief.law := by
  rw [pbsInformationConditionalSample_eq]
  have stopped (profile : Profile (model fullPrior).behavioralSignature) :
      (model fullPrior).runBehavioralFrom profile 0 = FinDist.pure := rfl
  rw [stopped, FinDist.bind_pure]

/-- The positive-tolerance child used by the actual parent has the sampled law. -/
theorem informationSamplingControl_parent
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    pbsInformationConditionalSample (reducedModel fullPrior) finiteBudgetControlBelief
        pbsRootControlFallback 1 (fun h player => cfrPayoff player h) 2 (1 / 4) unknown who 1 =
      finiteBudgetControlBelief.law.bind ((model fullPrior).runBehavioralFrom
        (Profile.update unknown who (cfrDInformationChildProfile (reducedModel fullPrior)
          (carriedBitProfile false) pbsRootControlFallback 2 1
          (fun h player => cfrPayoff player h) 2 (1 / 4) who)) 1) :=
  cfrDInformationChildProfile_sampling (reducedModel fullPrior) (carriedBitProfile false)
    pbsRootControlFallback 2 1 (fun h player => cfrPayoff player h) 2 (1 / 4)
    (publicTrace (model fullPrior).toInfoSignals factualChildHistory.trace)
    factualChild_possible unknown who 1

/-- Values use the same genuine two-iteration policy family as execution. -/
theorem informationSamplingControl_value
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    (cfrIterationLaw 2).expect (fun n => (finiteBudgetControlBelief.law.bind
      ((model fullPrior).runBehavioralFrom (Profile.update unknown who
        (pbsInformationCFRIterate (reducedModel fullPrior) finiteBudgetControlBelief
          pbsRootControlFallback cfrPayoff 1 n.val who)) 1)).expect (cfrPayoff who)) =
      (finiteBudgetControlBelief.law.bind ((model fullPrior).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFR (reducedModel fullPrior)
          finiteBudgetControlBelief pbsRootControlFallback cfrPayoff 1 2 who)) 1)).expect
            (cfrPayoff who) :=
  pbsInformationCFR_sampling_value (reducedModel fullPrior) finiteBudgetControlBelief
    pbsRootControlFallback cfrPayoff 1 2 unknown who 1 (cfrPayoff who)

/-- Two independent actual child draws reproduce the live averaged self-play law. -/
theorem informationSamplingControl_independent_live :
    pbsInformationCFRIndependentSample (reducedModel fullPrior) finiteBudgetControlBelief
        pbsRootControlFallback cfrPayoff 1 2 1 =
      finiteBudgetControlBelief.law.bind ((model fullPrior).runBehavioralFrom
        (pbsInformationCFR (reducedModel fullPrior) finiteBudgetControlBelief
          pbsRootControlFallback cfrPayoff 1 2) 1) :=
  pbsInformationCFRIndependentSample_law (reducedModel fullPrior) finiteBudgetControlBelief
    pbsRootControlFallback cfrPayoff 1 2 1

/-- Independent retained indices do not advance a zero-fuel continuation. -/
theorem informationSamplingControl_independent_zero_fuel :
    pbsInformationCFRIndependentSample (reducedModel fullPrior) finiteBudgetControlBelief
      pbsRootControlFallback cfrPayoff 1 2 0 = finiteBudgetControlBelief.law := by
  rw [pbsInformationCFRIndependentSample_law]
  have stopped (profile : Profile (model fullPrior).behavioralSignature) :
      (model fullPrior).runBehavioralFrom profile 0 = FinDist.pure := rfl
  rw [stopped, FinDist.bind_pure]

/-- Independent uniform indices can disagree; a shared index cannot. This
rejects replacing the independent sampler by a diagonal joint draw. -/
theorem informationSamplingControl_independent_not_diagonal :
    ((cfrIterationLaw 2).bind (fun first =>
      (cfrIterationLaw 2).map (fun second => (first, second)))) ≠
        (cfrIterationLaw 2).map (fun round => (round, round)) := by
  have firstSupported : (0 : Fin 2) ∈ (cfrIterationLaw 2).support := by
    by_contra absent
    have zero : (cfrIterationLaw 2).prob 0 = 0 := FinDist.prob_eq_zero_iff.mpr absent
    rw [informationSamplingControl_uniform_two.1] at zero
    norm_num at zero
  have secondSupported : (1 : Fin 2) ∈ (cfrIterationLaw 2).support := by
    by_contra absent
    have zero : (cfrIterationLaw 2).prob 1 = 0 := FinDist.prob_eq_zero_iff.mpr absent
    rw [informationSamplingControl_uniform_two.2] at zero
    norm_num at zero
  intro equal
  have pairSupported : ((0 : Fin 2), (1 : Fin 2)) ∈
      ((cfrIterationLaw 2).bind (fun first =>
        (cfrIterationLaw 2).map (fun second => (first, second)))).support := by
    simp only [FinDist.support_bind, Set.mem_iUnion, FinDist.support_map, Set.mem_image]
    exact ⟨0, firstSupported, 1, secondSupported, rfl⟩
  rw [equal, FinDist.support_map] at pairSupported
  obtain ⟨round, _, coordinates⟩ := pairSupported
  have impossible : (0 : Fin 2) = 1 :=
    (congrArg Prod.fst coordinates).symm.trans (congrArg Prod.snd coordinates)
  exact (by decide : (0 : Fin 2) ≠ 1) impossible

end GameTheory.ReBeL.Examples.HiddenTypes
