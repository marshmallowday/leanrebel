/-
# Typed reference-query tables constructed from actual stopped execution

The kernels are the original unilateral reference law conditioned on live
full-information fibers. Public and private compatibility are proved, not
supplied. Physically impossible public histories have no table entry; other
unsampled fibers have explicitly physical fallback kernels with no posterior
claim. Equilibrium and finite-T child quality are not part of this construction.
-/

import GameTheory.Analysis.ReBeL.CFRDPublicResponse

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype E.History]

/-- Every physically attained root type contains its named public history. -/
theorem cfrD_publicRootType_public {observations : List M.PublicSignal} {who : ι}
    (type : PublicRootType M observations who) : type.val.publicHistory = observations := by
  rw [← (publicRootWitness_spec M type).2, publicHistory_infoOf]
  exact (publicRootWitness_spec M type).1

variable [Fintype ι] [DecidableEq ι]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]

/-- An actual sampled live reference fiber is already a joint public belief.
The fallback at an unsampled fiber is visible and physically compatible. -/
def cfrDReferenceKernel (base : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    {observations : List M.PublicSignal} {who : ι}
    (type : PublicRootType M observations who) :
    PublicBelief (fullInformation M).toInfoSignals observations := by
  classical
  let reference := unilateralReferenceLaw (fullInformation M) base fallback who cut
  let observe := fun h : E.History =>
    ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h)
  exact if sampled : (type.val, true) ∈ (reference.map observe).support then
    { law := reference.condOnFibre observe (type.val, true)
      supported := by
        intro history reached
        have information : (fullInformation M).infoOf who history.trace = type.val :=
          congrArg Prod.fst
          (conditionalOracle_support reference observe (type.val, true) sampled history reached)
        rw [publicRoot_trace_eq]
        have rootPublic : publicTrace M.toInfoSignals history.trace = type.val.publicHistory := by
          simpa only [publicHistory_infoOf] using congrArg AOH.publicHistory information
        exact rootPublic.trans (cfrD_publicRootType_public M type) }
  else publicRootOffPath M type

/-- No kernel-identification certificate is needed at sampled queries. -/
theorem cfrDReferenceKernel_law (base : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    {observations : List M.PublicSignal} {who : ι}
    (type : PublicRootType M observations who)
    (sampled : (type.val, true) ∈
      ((unilateralReferenceLaw (fullInformation M) base fallback who cut).map
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support) :
    (cfrDReferenceKernel M base fallback cut remaining type).law =
      (unilateralReferenceLaw (fullInformation M) base fallback who cut).condOnFibre
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))
        (type.val, true) := by
  simp only [cfrDReferenceKernel, dif_pos sampled]

/-- The complete constructed kernel, including a fallback when needed, has
its named full root type in the canonical persistent memory. -/
theorem cfrDReferenceKernel_typed (base : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    {observations : List M.PublicSignal} {who : ι}
    (root type : PublicRootType M observations who) (history : E.History)
    (reached : history ∈ (cfrDReferenceKernel M base fallback cut remaining type).law.support) :
    (publicRootMemory M root).typeAt ((fullInformation M).infoOf who history.trace) = type := by
  classical
  by_cases sampled : (type.val, true) ∈
      ((unilateralReferenceLaw (fullInformation M) base fallback who cut).map
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support
  · have rootPublic := (cfrDReferenceKernel M base fallback cut remaining type).supported
      history reached
    rw [publicRoot_trace_eq] at rootPublic
    apply Subtype.ext
    rw [publicRootMemory_read M root history rootPublic]
    rw [cfrDReferenceKernel_law M base fallback cut remaining type sampled] at reached
    exact congrArg Prod.fst (conditionalOracle_support
      (unilateralReferenceLaw (fullInformation M) base fallback who cut)
      (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))
      (type.val, true) sampled history reached)
  · apply publicRootOffPath_typed M root type history
    simpa only [cfrDReferenceKernel, dif_neg sampled] using reached

/-- Persistent full-AOH memory and actual reference conditionals construct the
slice data; neither a posterior equality nor a payoff inequality is supplied. -/
def cfrDReferenceSlice (base : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    {observations : List M.PublicSignal} {who : ι} (root : PublicRootType M observations who) :
    TypeBeliefSlice (fullInformation M) observations who (PublicRootType M observations who) where
  memory := publicRootMemory M root
  kernel := cfrDReferenceKernel M base fallback cut remaining
  typed := cfrDReferenceKernel_typed M base fallback cut remaining root

/-- Construct the entire public response table. Impossible public histories
are absent rather than furnished with an invented probability distribution. -/
def cfrDReferenceTable (base : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat) :
    CFRDPublicSliceTable M := fun observations who => by
  classical
  exact if possible : Nonempty (PublicRootType M observations who) then
    some ⟨PublicRootType M observations who,
      cfrDReferenceSlice M base fallback cut remaining (Classical.choice possible)⟩
  else none

/-- Every actual live reference query finds its constructed table entry and
its exact joint conditional kernel. The type domain and physical witnesses
are obtained from the sampled history, not added as query assumptions. -/
theorem cfrDReferenceTable_query (base : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (who : ι) (info : (fullInformation M).InfoState who)
    (sampled : (info, true) ∈
      ((unilateralReferenceLaw (fullInformation M) base fallback who cut).map
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support) :
    ∃ (observations : List M.PublicSignal) (root type : PublicRootType M observations who),
      cfrDReferenceTable M base fallback cut remaining observations who =
        some ⟨PublicRootType M observations who,
          cfrDReferenceSlice M base fallback cut remaining root⟩ ∧
      type.val = info ∧
      ((cfrDReferenceSlice M base fallback cut remaining root).kernel type).law =
        (unilateralReferenceLaw (fullInformation M) base fallback who cut).condOnFibre
          (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))
          (info, true) := by
  classical
  have witness := sampled
  rw [FinDist.support_map] at witness
  obtain ⟨history, _, same⟩ := witness
  let observations := publicTrace M.toInfoSignals history.trace
  let type : PublicRootType M observations who := ⟨info,
    (mem_publicRootInfos M observations who info).mpr
      ⟨history, rfl, congrArg Prod.fst same⟩⟩
  have possible : Nonempty (PublicRootType M observations who) := ⟨type⟩
  let root := Classical.choice possible
  refine ⟨observations, root, type, ?_, rfl, ?_⟩
  · simp only [cfrDReferenceTable, dif_pos possible]
  · exact cfrDReferenceKernel_law M base fallback cut remaining type sampled

/-- An empty public history is physically impossible because the initial
public observation is retained. The constructed table therefore returns none. -/
theorem cfrDReferenceTable_empty (base : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat) (who : ι) :
    cfrDReferenceTable M base fallback cut remaining [] who = none := by
  classical
  have impossible : ¬ Nonempty (PublicRootType M [] who) := by
    rintro ⟨type⟩
    have length := congrArg List.length (cfrD_publicRootType_public M type)
    rw [AOH.publicHistory_length] at length
    simp only [List.length_nil] at length
    omega
  simp only [cfrDReferenceTable, dif_neg impossible]

variable [∀ who, Fintype (E.Action who)]

/-- The actual reference table now discharges query typing, existence and
kernel matching in the public response contract. Only factual child-game
Nash remains to be proved by a child solver; no leaf-gain bound is assumed. -/
theorem cfrDReferenceTable_leafOptimal (base : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) (who : ι)
    (factual : ∀ (observations : List M.PublicSignal)
      (root type : PublicRootType M observations who),
      (type.val, true) ∈ (((fullInformation M).runBehavioral base cut).map
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support →
      ∃ own : FinDist (PublicRootType M observations who),
        IsNash (behavioralBeliefForm (fullInformation M)
          ((cfrDReferenceSlice M base fallback cut remaining root).mixture own) remaining)
          (euPreference utility) base ∧ type ∈ own.support) :
    CFRDLeafOptimal (fullInformation M)
      (cfrDCompleteZeroReach (fullInformation M) base
        (cfrDPublicResponseCompletion M cut (cfrDReferenceTable M base fallback cut remaining)
          fallback remaining utility base)) fallback who (fun h => utility h who)
      cut remaining 0 := by
  apply cfrDPublicResponseCompletion_live_leafOptimal M cut remaining
  intro info sampled
  obtain ⟨observations, root, type, present, same, kernel⟩ :=
    cfrDReferenceTable_query M base fallback cut remaining who info sampled
  refine ⟨observations, PublicRootType M observations who,
    cfrDReferenceSlice M base fallback cut remaining root, type, present, kernel, ?_⟩
  intro reached
  apply factual observations root type
  simpa only [same] using reached

end GameTheory.ReBeL
