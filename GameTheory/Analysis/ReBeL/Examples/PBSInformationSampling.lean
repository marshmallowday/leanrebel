/-
# Controls for actual child-iteration sampling

These use the canonical live hidden-type posterior and the information-set
recurrence. Unknown opponents, a randomized opponent, zero execution fuel,
posterior-dependent counts and both parent-query branches remain explicit.
-/

import GameTheory.Analysis.ReBeL.CFRDInformationQuerySampling
import GameTheory.Analysis.ReBeL.Examples.CFRDInformationChild

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- The canonical hidden-type protocol has explicitly enumerated legal histories. -/
local instance samplingControlHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Canonical reference queries include all finite legal local menus. -/
local instance samplingControlChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

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

/-- The positive private/live branch is inhabited for each actual player. -/
theorem informationSamplingControl_factual_query_exists (who : Player) :
    ∃ info : (model fullPrior).InfoState who,
      CFRDInformationQueryFactual (reducedModel fullPrior)
        (carriedBitProfile false) 2 1 who info := by
  obtain ⟨history, event, reached⟩ := factualChild_possible
  refine ⟨(model fullPrior).infoOf who history.trace, ?_⟩
  rw [CFRDInformationQueryFactual, FinDist.support_map]
  exact ⟨history, reached, Prod.ext rfl event.2⟩

/-- A genuine parent's private query evaluates actual retained child iterates
against an arbitrary fixed unknown opponent with a positive finite loss budget. -/
theorem informationSamplingControl_factual_query
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (info : (model fullPrior).InfoState who)
    (factual : CFRDInformationQueryFactual (reducedModel fullPrior)
      (carriedBitProfile false) 2 1 who info) :
    cfrDInformationFactualQuerySample (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 (fun h player => cfrPayoff player h) 2 (1 / 4)
        who info factual unknown 1 =
      (cfrDInformationQueryLaw (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 who info).bind ((model fullPrior).runBehavioralFrom
          (Profile.update unknown who (cfrDInformationChildProfile (reducedModel fullPrior)
            (carriedBitProfile false) pbsRootControlFallback 2 1
            (fun h player => cfrPayoff player h) 2 (1 / 4) who)) 1) :=
  cfrDInformationFactualQuerySample_law (reducedModel fullPrior) (carriedBitProfile false)
    pbsRootControlFallback 2 1 (fun h player => cfrPayoff player h) 2 (1 / 4)
    who info factual unknown 1

/-- Private conditioning retains its complete correlated root law at zero fuel. -/
theorem informationSamplingControl_factual_query_zero_fuel
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (info : (model fullPrior).InfoState who)
    (factual : CFRDInformationQueryFactual (reducedModel fullPrior)
      (carriedBitProfile false) 2 1 who info) :
    cfrDInformationFactualQuerySample (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 (fun h player => cfrPayoff player h) 2 (1 / 4)
        who info factual unknown 0 =
      cfrDInformationQueryLaw (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 who info := by
  rw [cfrDInformationFactualQuerySample_law]
  have stopped (profile : Profile (model fullPrior).behavioralSignature) :
      (model fullPrior).runBehavioralFrom profile 0 = FinDist.pure := rfl
  rw [stopped, FinDist.bind_pure]

/-- Reference support at the zero-own-reach root is independent of which legal
fallback supplies the inactive menus. Here it is derived for the actual backend. -/
theorem informationSamplingControl_zero_reference :
    zeroControlHistory ∈ (unilateralReferenceLaw (model fullPrior) (carriedBitProfile false)
      informationControlFullFallback 0 2).support := by
  have focal := ownReach_eq_of_policy_eq (model fullPrior)
    (Profile.update (carriedBitProfile false) 0
      (uniformLegalPolicy (model fullPrior) 0 (informationControlFullFallback 0)))
    (uniformLegalProfile (model fullPrior) informationControlFullFallback) 0
    (Profile.update_same _ _ _) zeroControlHistory.trace
  have other := ownReach_eq_of_policy_eq (model fullPrior)
    (Profile.update (carriedBitProfile false) 0
      (uniformLegalPolicy (model fullPrior) 0 (informationControlFullFallback 0)))
    (carriedBitProfile false) 1 (Profile.update_of_ne _ _ (by decide)) zeroControlHistory.trace
  apply FinDist.prob_pos_iff.mp
  rw [unilateralReferenceLaw, run_probability_factorization (model fullPrior),
    Fin.prod_univ_two, focal, other]
  have mask : outcomeChanceWeight 2 zeroControlHistory = chanceReach zeroControlHistory.trace := by
    unfold outcomeChanceWeight
    exact if_pos ⟨Nat.le_refl 2, Or.inl rfl⟩
  rw [mask]
  apply mul_pos (chanceReach_pos _)
  apply mul_pos (uniformOwnReach_positive (model fullPrior) informationControlFullFallback 0 _)
  rw [zeroControlHistory, zeroControl_own_reach]
  norm_num [GameTheory.ReBeL.Rational.HiddenTypes.own]

/-- A zero-factual-mass private/live query really occurs in the reference law. -/
theorem informationSamplingControl_zero_query_sampled :
    CFRDInformationQuerySampled (reducedModel fullPrior) (carriedBitProfile false)
      pbsRootControlFallback 2 1 0 ((model fullPrior).infoOf 0 zeroControlHistory.trace) := by
  rw [CFRDInformationQuerySampled, FinDist.support_map]
  refine ⟨zeroControlHistory, informationSamplingControl_zero_reference, Prod.ext rfl ?_⟩
  simp only [cfrDCutLive, decide_eq_true_eq]
  exact ⟨by decide, by decide⟩

/-- Replacing reference support by factual support would discard this real query. -/
theorem informationSamplingControl_zero_query_not_factual :
    ¬ CFRDInformationQueryFactual (reducedModel fullPrior) (carriedBitProfile false)
      2 1 0 ((model fullPrior).infoOf 0 zeroControlHistory.trace) := by
  intro factual
  rw [CFRDInformationQueryFactual, FinDist.support_map] at factual
  obtain ⟨history, reached, same⟩ := factual
  apply zeroControl_factual_info_absent
  rw [FinDist.support_map]
  exact ⟨history, reached, congrArg Prod.fst same⟩

/-- At that off-path query the implementation selects the actual computed
response, rather than attempting to cancel a root with model probability zero. -/
theorem informationSamplingControl_zero_query_branch
    (unknown : Profile (model fullPrior).behavioralSignature) :
    cfrDInformationQuerySample (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 (fun h player => cfrPayoff player h) 2 (1 / 4)
        0 ((model fullPrior).infoOf 0 zeroControlHistory.trace) unknown 1 =
      (cfrDInformationQueryLaw (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 0 ((model fullPrior).infoOf 0 zeroControlHistory.trace)).bind
          ((model fullPrior).runBehavioralFrom
            (Profile.update unknown 0 (cfrDInformationQueryResponse (reducedModel fullPrior)
              (carriedBitProfile false) pbsRootControlFallback 2 1
              (fun h player => cfrPayoff player h) 2 (1 / 4) 0)) 1) := by
  simp only [cfrDInformationQuerySample, dif_neg informationSamplingControl_zero_query_not_factual]

/-- The off-path branch has the same complete law as the completed parent,
with an arbitrary fixed unknown opponent and positive continuation fuel. -/
theorem informationSamplingControl_zero_query_law
    (unknown : Profile (model fullPrior).behavioralSignature) :
    cfrDInformationQuerySample (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 (fun h player => cfrPayoff player h) 2 (1 / 4)
        0 ((model fullPrior).infoOf 0 zeroControlHistory.trace) unknown 1 =
      (cfrDInformationQueryLaw (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 0 ((model fullPrior).infoOf 0 zeroControlHistory.trace)).bind
          ((model fullPrior).runBehavioralFrom
            (Profile.update unknown 0 (cfrDInformationContinuation (reducedModel fullPrior)
              (carriedBitProfile false) pbsRootControlFallback 2 1
              (fun h player => cfrPayoff player h) 2 (1 / 4) 0)) 1) :=
  cfrDInformationQuerySample_law (reducedModel fullPrior) (carriedBitProfile false)
    pbsRootControlFallback 2 1 (fun h player => cfrPayoff player h) 2 (1 / 4)
    0 ((model fullPrior).infoOf 0 zeroControlHistory.trace)
    informationSamplingControl_zero_query_sampled unknown 1

end GameTheory.ReBeL.Examples.HiddenTypes
