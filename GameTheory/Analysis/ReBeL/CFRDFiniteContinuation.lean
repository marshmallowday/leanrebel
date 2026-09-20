/-
# Finite child budgets and counterfactual completion

The factual child has a computed finite horizon and a posterior-specific
root budget. Its factual type law reconstructs the same joint query game.
The existing zero-own-reach response supplies omitted types, so the completed
profile satisfies the actual all-deviation leaf contract with no supplied
child Nash, mass-floor, probability-budget or continuation-quality premise.
-/

import GameTheory.Analysis.ReBeL.CFRDFiniteChild
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

/-- Installing finite children preserves every unilateral reference cut law. -/
theorem cfrDFiniteChildProfile_referenceLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (who : Fin 2) :
    unilateralReferenceLaw (fullInformation M)
        (cfrDFiniteChildProfile M trunk fallback cut remaining utility bound loss)
        fallback who cut =
      unilateralReferenceLaw (fullInformation M) trunk fallback who cut :=
  cfrDDepthProfile_referenceLaw (fullInformation M) (fullObservationClock M)
    trunk _ fallback who cut

/-- A factual sampled type supplies a computed approximate-Nash budget in
its actual reference slice. One joint posterior supplies all type budgets. -/
theorem cfrDFiniteChildProfile_referenceBudget
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ h player, |utility h player| ≤ bound) (who : Fin 2)
    (obs : List M.PublicSignal) (root type : PublicRootType M obs who)
    (sampled : (type.val, true) ∈ (((fullInformation M).runBehavioral
      (cfrDFiniteChildProfile M trunk fallback cut remaining utility bound loss) cut).map
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support) :
    ∃ (own : FinDist (PublicRootType M obs who)) (error : ℝ),
      IsNash (behavioralBeliefForm (fullInformation M)
        ((cfrDReferenceSlice M
          (cfrDFiniteChildProfile M trunk fallback cut remaining utility bound loss)
          fallback cut remaining root).mixture own) remaining)
        (euPreferenceWithin error utility)
        (cfrDFiniteChildProfile M trunk fallback cut remaining utility bound loss) ∧
      type ∈ own.support ∧ error ≤ own.prob type * loss := by
  classical
  let base := cfrDFiniteChildProfile M trunk fallback cut remaining utility bound loss
  have prefixLaw : (fullInformation M).runBehavioral base cut =
      (fullInformation M).runBehavioral trunk cut :=
    cfrDFiniteChildProfile_prefixLaw M trunk fallback cut remaining utility bound loss
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
  have mixture : (cfrDReferenceSlice M base fallback cut remaining root).mixture own =
      belief :=
    beliefExt _ _ (cfrDFactualChild_referenceMixture M base fallback cut remaining possible root)
  have supported : type ∈ own.support :=
    (cfrDFactualChildTypeLaw_support M base cut remaining possible root type).mpr sampled
  have floor : belief.law.positiveMassFloor ≤ own.prob type :=
    belief.law.positiveMassFloor_le_map
      (fun h => (publicRootMemory M root).typeAt ((fullInformation M).infoOf who h.trace))
      type supported
  refine ⟨own, belief.law.positiveMassFloor * loss, ?_, supported,
    mul_le_mul_of_nonneg_right floor positive.le⟩
  rw [mixture, beliefEq]
  exact cfrDFiniteChildProfile_isNash M trunk fallback cut remaining utility zeroSum bound loss
    nonneg positive bounded obs original

/-- Complete the finite factual solve with the existing finite conditional
best responses where original own reach vanishes. No exact Nash is chosen. -/
def cfrDFiniteContinuation (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) :
    Profile (fullInformation M).behavioralSignature :=
  let base := cfrDFiniteChildProfile M trunk fallback cut remaining utility bound loss
  cfrDCompleteZeroReach (fullInformation M) base
    (cfrDPublicResponseCompletion M cut (cfrDReferenceTable M base fallback cut remaining)
      fallback remaining utility base)

/-- The completed finite continuation retains the queried trunk's reference. -/
theorem cfrDFiniteContinuation_referenceLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (who : Fin 2) :
    unilateralReferenceLaw (fullInformation M)
        (cfrDFiniteContinuation M trunk fallback cut remaining utility bound loss)
        fallback who cut =
      unilateralReferenceLaw (fullInformation M) trunk fallback who cut := by
  unfold cfrDFiniteContinuation
  rw [cfrDCompleteZeroReach_referenceLaw (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals), cfrDFiniteChildProfile_referenceLaw]

/-- The finite reference algorithm controls every actual live reference
query, including zero-factual-mass types. Positive child loss is essential
for its finite budget; error-zero exactness is not silently asserted. -/
theorem cfrDFiniteContinuation_leafOptimal
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ h player, |utility h player| ≤ bound) (who : Fin 2) :
    CFRDLeafOptimal (fullInformation M)
      (cfrDFiniteContinuation M trunk fallback cut remaining utility bound loss)
      fallback who (fun h => utility h who) cut remaining loss := by
  apply cfrDReferenceTable_approx_leafOptimal
  · exact positive.le
  · exact cfrDFiniteChildProfile_referenceBudget M trunk fallback cut remaining utility zeroSum
      bound loss nonneg positive bounded who

end GameTheory.ReBeL
