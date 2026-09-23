/-
# Retained child sampling and completed counterfactual query values

Factual private/live queries use actual retained child iterations. A sampled
reference query with zero factual mass uses the existing computed response
completion, not a fabricated zero-mass PBS. Both branches realize the same
completed continuation against fixed unknown opponents. The same law is then
consumed by the derived approximate leaf contract.
-/

import GameTheory.Analysis.ReBeL.CFRDInformationSampling
import GameTheory.Analysis.ReBeL.CFRDInformationContinuation
import GameTheory.Analysis.ReBeL.CFRDZeroReachContinuation
import GameTheory.Analysis.ReBeL.CFRDZeroReachOptimality

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)

private theorem completed_query_positive
    (base completion unknown : Profile (fullInformation M).behavioralSignature)
    (who : Fin 2) (fuel : Nat) (history : E.History)
    (positive : (fullInformation M).playerReachProbability base who history.trace ≠ 0) :
    (fullInformation M).runBehavioralFrom
        (Profile.update unknown who (cfrDCompleteZeroReach (fullInformation M)
          base completion who)) fuel history =
      (fullInformation M).runBehavioralFrom
        (Profile.update unknown who (base who)) fuel history := by
  classical
  have selection (profile : Profile (fullInformation M).behavioralSignature) :
      (fun player => if player ∈ ({who} : Finset (Fin 2)) then profile player
        else unknown player) = Profile.update unknown who (profile who) := by
    funext player
    by_cases same : player = who
    · subst player
      simp
    · simp only [Finset.mem_singleton, if_neg same, Profile.update_of_ne _ _ same]
  have result := cfrDCompleteZeroReach_selected_continuation (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals) base completion unknown {who} fuel history
    (by
      intro player member
      have same := Finset.mem_singleton.mp member
      subst player
      exact positive)
  simpa only [selection] using result

private theorem completed_query_zero
    (base completion unknown : Profile (fullInformation M).behavioralSignature)
    (who : Fin 2) (fuel : Nat) (history : E.History)
    (zero : (fullInformation M).playerReachProbability base who history.trace = 0) :
    (fullInformation M).runBehavioralFrom
        (Profile.update unknown who (cfrDCompleteZeroReach (fullInformation M)
          base completion who)) fuel history =
      (fullInformation M).runBehavioralFrom
        (Profile.update unknown who (completion who)) fuel history := by
  apply (fullInformation M).runBehavioralFrom_congr
  intro later reaches _ player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    apply cfrDCompleteZeroReach_of_zero
    rw [informationOwnReach_eq_player (fullInformation M)
      (fullSignals_perfectRecall M.toInfoSignals) base who later]
    exact cfrD_zero_ownReach_of_reaches (fullInformation M) base who reaches zero
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]

/-- The existing computed response component of the information-set continuation.
This is an exposed definition, not a newly assumed best-response certificate. -/
def cfrDInformationQueryResponse
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) :
    Profile (fullInformation M).behavioralSignature :=
  let base := cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss
  cfrDPublicResponseCompletion M cut
    (cfrDReferenceTable M base (cfrDInformationFallback M fallback) cut remaining)
    (cfrDInformationFallback M fallback) remaining utility base

/-- On a factual query, zero-own-reach completion does not alter the retained
child law, including when arbitrary fixed opponents replace the model opponents. -/
theorem cfrDInformationFactualQuerySample_completed
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ)
    (who : Fin 2) (info : (fullInformation M).InfoState who)
    (factual : CFRDInformationQueryFactual M trunk cut remaining who info)
    (unknown : Profile (fullInformation M).behavioralSignature) (steps : Nat) :
    cfrDInformationFactualQuerySample M trunk fallback cut remaining utility bound loss
        who info factual unknown steps =
      (cfrDInformationQueryLaw M trunk fallback cut remaining who info).bind
        ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who
            (cfrDInformationContinuation M trunk fallback cut remaining utility bound loss who))
          steps) := by
  rw [cfrDInformationFactualQuerySample_law]
  apply FinDist.bind_congr
  intro history reached
  have supported := cfrDInformationQuery_support M trunk fallback cut remaining
    who info factual history reached
  have inTrunk : history ∈ ((fullInformation M).runBehavioral trunk cut).support :=
    (FinDist.support_condOn _ _
      (cfrDInformationQuery_possible M trunk cut remaining who info factual) supported).2
  have inChild : history ∈ ((fullInformation M).runBehavioral
      (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss)
      cut).support := by
    simpa only [cfrDInformationChildProfile_prefixLaw] using inTrunk
  exact (completed_query_positive M
    (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss)
    (cfrDInformationQueryResponse M trunk fallback cut remaining utility bound loss)
    unknown who steps history (cfrD_run_support_ownReach (fullInformation M) _
      cut history inChild who)).symm

/-- A genuine live reference query. Factual support is deliberately not required. -/
def CFRDInformationQuerySampled
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (who : Fin 2) (info : (fullInformation M).InfoState who) : Prop :=
  (info, true) ∈ ((unilateralReferenceLaw (fullInformation M) trunk
    (cfrDInformationFallback M fallback) who cut).map
      (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support

/-- Completed query execution. Factual queries draw actual finite child iterates;
zero-factual-mass queries use the computed off-path response. The reference law
is correlated and its private/live conditioning never becomes a policy input. -/
def cfrDInformationQuerySample
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ)
    (who : Fin 2) (info : (fullInformation M).InfoState who)
    (unknown : Profile (fullInformation M).behavioralSignature) (steps : Nat) :
    FinDist E.History := by
  classical
  exact if factual : CFRDInformationQueryFactual M trunk cut remaining who info then
    cfrDInformationFactualQuerySample M trunk fallback cut remaining utility bound loss
      who info factual unknown steps
  else
    (cfrDInformationQueryLaw M trunk fallback cut remaining who info).bind
      ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (cfrDInformationQueryResponse M trunk fallback cut remaining utility bound loss who))
        steps)

/-- Every sampled reference query realizes the very same completed continuation.
There is no assertion about an arbitrary fallback conditional on an unsampled
reference fiber, nor any sampling equivalence outside the factual child support. -/
theorem cfrDInformationQuerySample_law
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ)
    (who : Fin 2) (info : (fullInformation M).InfoState who)
    (sampled : CFRDInformationQuerySampled M trunk fallback cut remaining who info)
    (unknown : Profile (fullInformation M).behavioralSignature) (steps : Nat) :
    cfrDInformationQuerySample M trunk fallback cut remaining utility bound loss
        who info unknown steps =
      (cfrDInformationQueryLaw M trunk fallback cut remaining who info).bind
        ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who
            (cfrDInformationContinuation M trunk fallback cut remaining utility bound loss who))
          steps) := by
  classical
  unfold cfrDInformationQuerySample
  split_ifs with factual
  · exact cfrDInformationFactualQuerySample_completed M trunk fallback cut remaining
      utility bound loss who info factual unknown steps
  · apply FinDist.bind_congr
    intro history reached
    let base := cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss
    let observe := fun h : E.History =>
      ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h)
    have sampledBase : (info, true) ∈ ((unilateralReferenceLaw (fullInformation M)
        base (cfrDInformationFallback M fallback) who cut).map observe).support := by
      simpa only [base, cfrDInformationChildProfile_referenceLaw,
        CFRDInformationQuerySampled] using sampled
    have absentBase : (info, true) ∉
        (((fullInformation M).runBehavioral base cut).map observe).support := by
      simpa only [base, cfrDInformationChildProfile_prefixLaw,
        CFRDInformationQueryFactual] using factual
    have reachedBase : history ∈ ((unilateralReferenceLaw (fullInformation M)
        base (cfrDInformationFallback M fallback) who cut).condOnFibre
          observe (info, true)).support := by
      simpa only [base, cfrDInformationChildProfile_referenceLaw,
        cfrDInformationQueryLaw] using reached
    have zero := cfrDReference_factual_absent_own_zero (fullInformation M)
      (fullSignals_perfectRecall M.toInfoSignals) base (cfrDInformationFallback M fallback)
      who cut observe Prod.fst (fun _ => rfl) (info, true)
      sampledBase absentBase history reachedBase
    exact (completed_query_zero M base
      (cfrDInformationQueryResponse M trunk fallback cut remaining utility bound loss)
      unknown who steps history zero).symm

/-- Arbitrary original-history observables agree for both genuine query branches. -/
theorem cfrDInformationQuerySample_value
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ)
    (who : Fin 2) (info : (fullInformation M).InfoState who)
    (sampled : CFRDInformationQuerySampled M trunk fallback cut remaining who info)
    (unknown : Profile (fullInformation M).behavioralSignature) (steps : Nat)
    (value : E.History → ℝ) :
    (cfrDInformationQuerySample M trunk fallback cut remaining utility bound loss
      who info unknown steps).expect value =
      ((cfrDInformationQueryLaw M trunk fallback cut remaining who info).bind
        ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who
            (cfrDInformationContinuation M trunk fallback cut remaining utility bound loss who))
          steps)).expect value :=
  congrArg (fun law : FinDist E.History => law.expect value)
    (cfrDInformationQuerySample_law M trunk fallback cut remaining utility bound loss
      who info sampled unknown steps)

/-- The actual completed sampler satisfies the derived conditional leaf-loss
bound against every full future deviation. Positive child loss is retained;
no per-iterate optimality or pre-supplied leaf certificate is assumed. -/
theorem cfrDInformationQuerySample_gain_le
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ h player, |utility h player| ≤ bound)
    (who : Fin 2) (info : (fullInformation M).InfoState who)
    (sampled : CFRDInformationQuerySampled M trunk fallback cut remaining who info)
    (target : (fullInformation M).BehavioralPolicy who) :
    ((cfrDInformationQueryLaw M trunk fallback cut remaining who info).bind
      ((fullInformation M).runBehavioralFrom
        (Profile.update
          (cfrDInformationContinuation M trunk fallback cut remaining utility bound loss)
          who target) remaining)).expect (fun h => utility h who) -
      (cfrDInformationQuerySample M trunk fallback cut remaining utility bound loss
        who info (cfrDInformationContinuation M trunk fallback cut remaining utility bound loss)
        remaining).expect (fun h => utility h who) ≤ loss := by
  have sampledCompleted : (info, true) ∈ ((unilateralReferenceLaw (fullInformation M)
      (cfrDInformationContinuation M trunk fallback cut remaining utility bound loss)
      (cfrDInformationFallback M fallback) who cut).map
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support := by
    simpa only [cfrDInformationContinuation_referenceLaw,
      CFRDInformationQuerySampled] using sampled
  have optimal := cfrDInformationContinuation_leafOptimal M trunk fallback cut remaining
    utility zeroSum bound loss nonneg positive bounded who target info sampledCompleted
  unfold conditionalOracleValue cfrDLeafGain at optimal
  rw [FinDist.expect_sub] at optimal
  rw [cfrDInformationQuerySample_law M trunk fallback cut remaining utility bound loss
    who info sampled, Profile.update_eq_self]
  simpa only [FinDist.expect_bind, cfrDInformationContinuation_referenceLaw,
    cfrDInformationQueryLaw] using optimal

end GameTheory.ReBeL
