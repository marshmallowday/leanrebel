/-
# Factual child posteriors and the actual reference queries

Conditioning a live public posterior again on a supported full private AOH
recovers the original private/live conditional. Information-local reweighting
then identifies it with the unilateral reference conditional exactly. No
identity of arbitrary fallback conditionals is asserted.
-/

import GameTheory.Analysis.ReBeL.CFRDFactualChild

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]

/-- The constructed child posterior and the actual unilateral reference law
have identical supported private/live kernels. The public observation is
recovered from full private AOH; independence of hidden variables is not used. -/
theorem cfrDFactualChildBelief_referenceConditional
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (observations : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining observations)
    (who : ι) (info : (fullInformation M).InfoState who)
    (rootPublic : info.publicHistory = observations)
    (sampled : (info, true) ∈ (((fullInformation M).runBehavioral trunk cut).map
      (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support) :
    (cfrDFactualChildBelief M trunk cut remaining observations possible).law.condOnFibre
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))
        (info, true) =
      (unilateralReferenceLaw (fullInformation M) trunk fallback who cut).condOnFibre
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))
        (info, true) := by
  classical
  let law := (fullInformation M).runBehavioral trunk cut
  let observe := fun h : E.History =>
    ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h)
  let event := {h : E.History |
    publicTrace (fullInformation M).toInfoSignals h.trace = observations ∧
      cfrDCutLive remaining h = true}
  have inner : ∃ h ∈ observe ⁻¹' {(info, true)}, h ∈ law.support := by
    rw [FinDist.support_map] at sampled
    obtain ⟨h, reached, same⟩ := sampled
    exact ⟨h, same, reached⟩
  have included : (observe ⁻¹' {(info, true)}) ∩ law.support ⊆ event := by
    intro h member
    have same : observe h = (info, true) := member.1
    refine ⟨?_, congrArg Prod.snd same⟩
    rw [publicRoot_trace_eq]
    have known := congrArg AOH.publicHistory (congrArg Prod.fst same)
    simpa only [observe, publicHistory_infoOf, rootPublic] using known
  have innerAfter : ∃ h ∈ observe ⁻¹' {(info, true)},
      h ∈ (law.condOn event possible).support := by
    obtain ⟨h, same, reached⟩ := inner
    exact ⟨h, same, FinDist.mem_support_condOn law event possible
      (included ⟨same, reached⟩) reached⟩
  have nested :
      (cfrDFactualChildBelief M trunk cut remaining observations possible).law.condOnFibre
        observe (info, true) = law.condOnFibre observe (info, true) := by
    unfold cfrDFactualChildBelief
    rw [FinDist.condOnFibre, dif_pos innerAfter, FinDist.condOnFibre, dif_pos inner]
    exact FinDist.condOn_condOn law possible inner included innerAfter
  calc
    _ = law.condOnFibre observe (info, true) := nested
    _ = _ := informationReweight_conditional
      (unilateralReferenceLaw (fullInformation M) trunk fallback who cut) law observe
      (fun tag => unilateralDensity (fullInformation M) trunk fallback who (trunk who) tag.1)
      (fun h => by simpa only [Profile.update_eq_self] using
        unilateralReference_density (fullInformation M) (fullSignals_perfectRecall M.toInfoSignals)
          trunk fallback who (trunk who) cut h) (info, true) sampled

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- The factual child's entire factual/counterfactual query packet is still
exactly the one produced by its trunk. Its new equilibrium continuation cannot
retroactively alter which child was queried. -/
theorem cfrDFactualChildProfile_currentPBS
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) :
    cfrDCurrentPBS (fullInformation M) fallback
        (cfrDFactualChildProfile M trunk fallback cut remaining utility) cut =
      cfrDCurrentPBS (fullInformation M) fallback trunk cut :=
  cfrDCurrentPBS_depthProfile (fullInformation M) (fullObservationClock M) fallback cut trunk
    (cfrDPublicContinuation M cut (cfrDFactualChildTable M trunk fallback cut remaining utility))

end GameTheory.ReBeL
