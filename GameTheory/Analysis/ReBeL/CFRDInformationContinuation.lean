/-
# Information-set child contracts with zero-own-reach completion

The computed factual information-set CFR output reconstructs the same joint
reference slice. A derived posterior mass budget controls supported types;
the existing finite conditional response handles zero-own-reach types.
No child Nash, probability floor or continuation-quality certificate is an input.
-/

import GameTheory.Analysis.ReBeL.CFRDInformationChild
import GameTheory.Analysis.ReBeL.CFRDApproximateLeaf

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]

/-- Installing the information-set child preserves every reference cut law. -/
theorem cfrDInformationChildProfile_referenceLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (who : Fin 2) :
    unilateralReferenceLaw (fullInformation M)
        (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss)
        (cfrDInformationFallback M fallback) who cut =
      unilateralReferenceLaw (fullInformation M) trunk
        (cfrDInformationFallback M fallback) who cut :=
  cfrDDepthProfile_referenceLaw (fullInformation M) (fullObservationClock M)
    trunk _ (cfrDInformationFallback M fallback) who cut

/-- A factual type receives its mass-scaled budget in the actual reference slice.
Both the root equilibrium and the requested finite budget are derived. -/
theorem cfrDInformationChildProfile_referenceBudget
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ h player, |utility h player| ≤ bound) (who : Fin 2)
    (obs : List M.PublicSignal) (root type : PublicRootType M obs who)
    (sampled : (type.val, true) ∈ (((fullInformation M).runBehavioral
      (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss) cut).map
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support) :
    ∃ (own : FinDist (PublicRootType M obs who)) (error : ℝ),
      IsNash (behavioralBeliefForm (fullInformation M)
        ((cfrDReferenceSlice M
          (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss)
          (cfrDInformationFallback M fallback) cut remaining root).mixture own) remaining)
        (euPreferenceWithin error utility)
        (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss) ∧
      type ∈ own.support ∧ error ≤ own.prob type * loss := by
  classical
  let base := cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss
  have prefixLaw : (fullInformation M).runBehavioral base cut =
      (fullInformation M).runBehavioral trunk cut :=
    cfrDInformationChildProfile_prefixLaw M trunk fallback cut remaining utility bound loss
  have possible : CFRDFactualChildPossible M base cut remaining obs := by
    have witness := sampled
    rw [FinDist.support_map] at witness
    obtain ⟨h, reached, same⟩ := witness
    refine ⟨h, ⟨?_, congrArg Prod.snd same⟩, reached⟩
    rw [publicRoot_trace_eq]
    have known := congrArg AOH.publicHistory (congrArg Prod.fst same)
    simpa only [publicHistory_infoOf, cfrD_publicRootType_public M type] using known
  have original : CFRDFactualChildPossible M trunk cut remaining obs := by
    simpa only [CFRDFactualChildPossible, prefixLaw] using possible
  let belief := cfrDFactualChildBelief M base cut remaining obs possible
  let own := cfrDFactualChildTypeLaw M base cut remaining possible root
  have beliefExt (first second : PublicBelief (fullInformation M).toInfoSignals obs)
      (equal : first.law = second.law) : first = second := by
    cases first
    cases second
    cases equal
    rfl
  have beliefEq : belief = cfrDFactualChildBelief M trunk cut remaining obs original := by
    apply beliefExt
    dsimp only [belief, cfrDFactualChildBelief]
    simp only [prefixLaw]
  have mixture : (cfrDReferenceSlice M base (cfrDInformationFallback M fallback)
      cut remaining root).mixture own = belief :=
    beliefExt _ _ (cfrDFactualChild_referenceMixture M base
      (cfrDInformationFallback M fallback) cut remaining possible root)
  have supported : type ∈ own.support :=
    (cfrDFactualChildTypeLaw_support M base cut remaining possible root type).mpr sampled
  have floor : belief.law.positiveMassFloor ≤ own.prob type :=
    belief.law.positiveMassFloor_le_map
      (fun h => (publicRootMemory M root).typeAt ((fullInformation M).infoOf who h.trace))
      type supported
  refine ⟨own, belief.law.positiveMassFloor * loss, ?_, supported,
    mul_le_mul_of_nonneg_right floor positive.le⟩
  rw [mixture, beliefEq]
  exact cfrDInformationChildProfile_isNash M trunk fallback cut remaining utility zeroSum
    bound loss nonneg positive bounded obs original

/-- Complete only the omitted zero-own-reach part with the existing response.
The factual child remains the computed information-set CFR profile. -/
def cfrDInformationContinuation (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) :
    Profile (fullInformation M).behavioralSignature :=
  let base := cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss
  cfrDCompleteZeroReach (fullInformation M) base
    (cfrDPublicResponseCompletion M cut
      (cfrDReferenceTable M base (cfrDInformationFallback M fallback) cut remaining)
      (cfrDInformationFallback M fallback) remaining utility base)

/-- Completion retains the queried trunk's reference cut distribution. -/
theorem cfrDInformationContinuation_referenceLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (who : Fin 2) :
    unilateralReferenceLaw (fullInformation M)
        (cfrDInformationContinuation M trunk fallback cut remaining utility bound loss)
        (cfrDInformationFallback M fallback) who cut =
      unilateralReferenceLaw (fullInformation M) trunk
        (cfrDInformationFallback M fallback) who cut := by
  unfold cfrDInformationContinuation
  rw [cfrDCompleteZeroReach_referenceLaw (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals), cfrDInformationChildProfile_referenceLaw]

/-- Every live counterfactual query has the requested child loss, including
zero-factual-mass types. A positive budget is essential to the finite solve. -/
theorem cfrDInformationContinuation_leafOptimal
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ h player, |utility h player| ≤ bound) (who : Fin 2) :
    CFRDLeafOptimal (fullInformation M)
      (cfrDInformationContinuation M trunk fallback cut remaining utility bound loss)
      (cfrDInformationFallback M fallback) who (fun h => utility h who) cut remaining loss := by
  apply cfrDReferenceTable_approx_leafOptimal
  · exact positive.le
  · exact cfrDInformationChildProfile_referenceBudget M trunk fallback cut remaining utility
      zeroSum bound loss nonneg positive bounded who

end GameTheory.ReBeL
