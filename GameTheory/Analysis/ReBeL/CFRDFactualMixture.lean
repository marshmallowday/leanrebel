/-
# Reconstructing factual child games from the actual reference type kernels

The own-type distribution is computed from the constructed factual posterior.
Its supported reference kernels reconstruct that entire joint law. This
supplies the factual Nash premise of the existing completed leaf contract,
without assuming an equilibrium, a posterior identity, or an optimality bound.
The construction is an exact mathematical reference, not finite-T CFR.
-/

import GameTheory.Analysis.ReBeL.CFRDFactualQuery
import GameTheory.Math.Probability.FinDistConditioning

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [Fintype E.History]

/-- The child type distribution is the pushforward of its actual joint law.
The memory fallback only encodes syntactic states outside the physical fiber. -/
def cfrDFactualChildTypeLaw (trunk : Profile (fullInformation M).behavioralSignature)
    (cut remaining : Nat) {observations : List M.PublicSignal}
    (possible : CFRDFactualChildPossible M trunk cut remaining observations)
    {who : ι} (root : PublicRootType M observations who) :
    FinDist (PublicRootType M observations who) :=
  (cfrDFactualChildBelief M trunk cut remaining observations possible).law.map fun h =>
    (publicRootMemory M root).typeAt ((fullInformation M).infoOf who h.trace)

/-- Encoded type support agrees with actual private/live observation support.
Zero own-weight types remain in the domain but are not falsely marked sampled. -/
theorem cfrDFactualChildTypeLaw_support
    (trunk : Profile (fullInformation M).behavioralSignature) (cut remaining : Nat)
    {observations : List M.PublicSignal}
    (possible : CFRDFactualChildPossible M trunk cut remaining observations)
    {who : ι} (root type : PublicRootType M observations who) :
    type ∈ (cfrDFactualChildTypeLaw M trunk cut remaining possible root).support ↔
      (type.val, true) ∈ (((fullInformation M).runBehavioral trunk cut).map
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support := by
  classical
  rw [cfrDFactualChildTypeLaw, FinDist.support_map, FinDist.support_map]
  constructor
  · rintro ⟨h, reached, equal⟩
    have member := FinDist.support_condOn _ _ possible reached
    have hpublic := member.1.1
    rw [publicRoot_trace_eq] at hpublic
    have read := publicRootMemory_read M root h hpublic
    refine ⟨h, member.2, Prod.ext ?_ member.1.2⟩
    exact read.symm.trans (congrArg Subtype.val equal)
  · rintro ⟨h, reached, equal⟩
    have info : (fullInformation M).infoOf who h.trace = type.val := congrArg Prod.fst equal
    have hpublic : publicTrace M.toInfoSignals h.trace = observations := by
      have known := congrArg AOH.publicHistory info
      simpa only [publicHistory_infoOf, cfrD_publicRootType_public M type] using known
    have rootPublic : publicTrace (fullInformation M).toInfoSignals h.trace = observations := by
      rw [publicRoot_trace_eq]
      exact hpublic
    refine ⟨h, FinDist.mem_support_condOn _ _ possible
      ⟨rootPublic, congrArg Prod.snd equal⟩ reached, ?_⟩
    apply Subtype.ext
    exact (publicRootMemory_read M root h hpublic).trans info

variable [DecidableEq ι] [∀ who info, Fintype ((fullInformation M).Choice who info)]

/-- Each supported encoded child kernel is precisely the child posterior's
conditional. Its reference law, live mask and information encoding are derived. -/
theorem cfrDFactualChildTypeLaw_kernel
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    {observations : List M.PublicSignal}
    (possible : CFRDFactualChildPossible M trunk cut remaining observations)
    {who : ι} (root type : PublicRootType M observations who)
    (supported : type ∈ (cfrDFactualChildTypeLaw M trunk cut remaining possible root).support) :
    (cfrDReferenceKernel M trunk fallback cut remaining type).law =
      (cfrDFactualChildBelief M trunk cut remaining observations possible).law.condOnFibre
        (fun h => (publicRootMemory M root).typeAt ((fullInformation M).infoOf who h.trace))
        type := by
  classical
  let law := (fullInformation M).runBehavioral trunk cut
  let observe := fun h : E.History =>
    ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h)
  have sampled := (cfrDFactualChildTypeLaw_support M trunk cut remaining possible root type).mp
    supported
  have referenceSampled : (type.val, true) ∈
      (FinDist.map observe
        (unilateralReferenceLaw (fullInformation M) trunk fallback who cut)).support := by
    rw [FinDist.support_map] at sampled ⊢
    obtain ⟨h, reached, same⟩ := sampled
    refine ⟨h, ?_, same⟩
    apply informationReweight_support
      (unilateralReferenceLaw (fullInformation M) trunk fallback who cut) law observe
      (fun tag =>
        unilateralDensity (fullInformation M) trunk fallback who (trunk who) tag.1)
      (fun x => by
        simpa only [Profile.update_eq_self] using
          unilateralReference_density (fullInformation M)
            (fullSignals_perfectRecall M.toInfoSignals) trunk fallback who (trunk who) cut x)
      reached
  rw [cfrDReferenceKernel_law M trunk fallback cut remaining type referenceSampled]
  rw [← cfrDFactualChildBelief_referenceConditional M trunk fallback cut remaining observations
    possible who type.val (cfrD_publicRootType_public M type) sampled]
  apply FinDist.condOnFibre_eq_of_support_iff
  intro h reached
  have member := FinDist.support_condOn _ _ possible reached
  have hpublic := member.1.1
  rw [publicRoot_trace_eq] at hpublic
  have read := publicRootMemory_read M root h hpublic
  constructor
  · intro tagged
    apply Subtype.ext
    exact read.trans (congrArg Prod.fst tagged)
  · intro typed
    exact Prod.ext (read.symm.trans (congrArg Subtype.val typed)) member.1.2

/-- Mixing the actual reference kernels reconstructs the complete factual
child law, rather than only its marginals or its expected payoff. -/
theorem cfrDFactualChild_referenceMixture
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    {observations : List M.PublicSignal}
    (possible : CFRDFactualChildPossible M trunk cut remaining observations)
    {who : ι} (root : PublicRootType M observations who) :
    ((cfrDReferenceSlice M trunk fallback cut remaining root).mixture
      (cfrDFactualChildTypeLaw M trunk cut remaining possible root)).law =
      (cfrDFactualChildBelief M trunk cut remaining observations possible).law := by
  let belief := cfrDFactualChildBelief M trunk cut remaining observations possible
  let read := fun h : E.History =>
    (publicRootMemory M root).typeAt ((fullInformation M).infoOf who h.trace)
  calc
    _ = (belief.law.map read).bind (belief.law.condOnFibre read) := by
      apply FinDist.bind_congr
      intro type supported
      exact cfrDFactualChildTypeLaw_kernel M trunk fallback cut remaining possible
        root type supported
    _ = belief.law := (FinDist.eq_bind_condOnFibre belief.law read).symm

variable [∀ who, Fintype (E.Action who)]

/-- Exact child continuations leave the original unilateral query law intact. -/
theorem cfrDFactualChildProfile_referenceLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) (who : ι) :
    unilateralReferenceLaw (fullInformation M)
        (cfrDFactualChildProfile M trunk fallback cut remaining utility) fallback who cut =
      unilateralReferenceLaw (fullInformation M) trunk fallback who cut := by
  unfold unilateralReferenceLaw
  apply runBehavioral_eq_of_before_depth (fullInformation M) (fullObservationClock M)
  intro player info before
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]
    exact cfrDFactualChildProfile_before M trunk fallback cut remaining utility player info before

/-- The typed query slice is identical before and after installing child Nash. -/
theorem cfrDFactualChildProfile_referenceSlice
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) {observations : List M.PublicSignal} {who : ι}
    (root : PublicRootType M observations who) :
    cfrDReferenceSlice M (cfrDFactualChildProfile M trunk fallback cut remaining utility)
        fallback cut remaining root =
      cfrDReferenceSlice M trunk fallback cut remaining root := by
  have kernels : ∀ type : PublicRootType M observations who,
      cfrDReferenceKernel M (cfrDFactualChildProfile M trunk fallback cut remaining utility)
          fallback cut remaining type =
        cfrDReferenceKernel M trunk fallback cut remaining type := by
    intro type
    simp only [cfrDReferenceKernel, cfrDFactualChildProfile_referenceLaw]
  have kernelFunction := funext kernels
  simp only [cfrDReferenceSlice, kernelFunction]

/-- The factual Nash premise of the reference-table contract is now obtained
from the constructed profile and actual sampled type, not supplied by a caller. -/
theorem cfrDFactualChildProfile_referenceNash
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) (who : ι) (observations : List M.PublicSignal)
    (root type : PublicRootType M observations who)
    (sampled : (type.val, true) ∈ (((fullInformation M).runBehavioral
      (cfrDFactualChildProfile M trunk fallback cut remaining utility) cut).map
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support) :
    ∃ own : FinDist (PublicRootType M observations who),
      IsNash (behavioralBeliefForm (fullInformation M)
        ((cfrDReferenceSlice M (cfrDFactualChildProfile M trunk fallback cut remaining utility)
          fallback cut remaining root).mixture own) remaining)
        (euPreference utility) (cfrDFactualChildProfile M trunk fallback cut remaining utility) ∧
      type ∈ own.support := by
  classical
  rw [cfrDFactualChildProfile_prefixLaw] at sampled
  have possible : CFRDFactualChildPossible M trunk cut remaining observations := by
    have witness := sampled
    rw [FinDist.support_map] at witness
    obtain ⟨h, reached, same⟩ := witness
    refine ⟨h, ⟨?_, congrArg Prod.snd same⟩, reached⟩
    rw [publicRoot_trace_eq]
    have hpublic := congrArg AOH.publicHistory (congrArg Prod.fst same)
    simpa only [publicHistory_infoOf, cfrD_publicRootType_public M type] using hpublic
  let own := cfrDFactualChildTypeLaw M trunk cut remaining possible root
  have mixture : (cfrDReferenceSlice M trunk fallback cut remaining root).mixture own =
      cfrDFactualChildBelief M trunk cut remaining observations possible := by
    have beliefExt (first second : PublicBelief (fullInformation M).toInfoSignals observations)
        (equal : first.law = second.law) : first = second := by
      cases first
      cases second
      cases equal
      rfl
    exact beliefExt _ _ (cfrDFactualChild_referenceMixture M trunk fallback cut remaining
      possible root)
  refine ⟨own, ?_, (cfrDFactualChildTypeLaw_support M trunk cut remaining possible root type).mpr
    sampled⟩
  rw [cfrDFactualChildProfile_referenceSlice, mixture]
  exact cfrDFactualChildProfile_isNash M trunk fallback cut remaining utility observations possible

/-- Exact child Nash plus constructed public zero-own-reach completion supplies
an all-deviation leaf contract at zero loss. No Nash, query identity or leaf
quality inequality is among the assumptions of this reference constructor. -/
theorem cfrDFactualChildProfile_completed_leafOptimal
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) (who : ι) :
    let base := cfrDFactualChildProfile M trunk fallback cut remaining utility
    CFRDLeafOptimal (fullInformation M)
      (cfrDCompleteZeroReach (fullInformation M) base
        (cfrDPublicResponseCompletion M cut (cfrDReferenceTable M base fallback cut remaining)
          fallback remaining utility base)) fallback who (fun h => utility h who)
      cut remaining 0 := by
  apply cfrDReferenceTable_leafOptimal
  exact cfrDFactualChildProfile_referenceNash M trunk fallback cut remaining utility who

end GameTheory.ReBeL
