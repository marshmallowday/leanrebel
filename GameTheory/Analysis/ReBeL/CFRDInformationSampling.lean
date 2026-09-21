/-
# Actual retained child iterations and the parent's conditional queries

The factual joint posterior determines the positive finite child count.
Sampling an actual decoded child iterate gives the same unilateral law as
the parent's public-prefix-spliced child policy. Supported private/live
reference queries inherit this law by a derived support theorem, not by an
assumed posterior identity or a supplied conditional value certificate.
Zero-own-reach completion and recursive carried-PBS safety remain separate.
-/

import GameTheory.Analysis.ReBeL.PBSSupportedSampling
import GameTheory.Analysis.ReBeL.CFRDInformationChild

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {observations : List M.PublicSignal}

/-- The exact positive count used by the existing conditional child solver. -/
abbrev pbsInformationConditionalRounds
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fuel : Nat) (bound loss : ℝ) : Nat :=
  pbsInformationBudgetRounds M belief.law (fun _ => bound) fuel
    (belief.law.positiveMassFloor * loss)

/-- Sample a private index from the actual finite child recurrence, then
retain that decoded policy for the entire continuation against fixed opponents. -/
def pbsInformationConditionalSample
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) : FinDist E.History :=
  (cfrIterationLaw (pbsInformationConditionalRounds M belief fuel bound loss)).bind
    (fun n => belief.law.bind ((fullInformation M).runBehavioralFrom
      (Profile.update unknown who (pbsInformationCFRIterate M belief fallback
        (fun player h => utility h player) fuel n.val who)) steps))

/-- The computed posterior-dependent draw has exactly the law of the existing
conditional output. Semantic equality does not require a positive error budget. -/
theorem pbsInformationConditionalSample_eq
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) :
    pbsInformationConditionalSample M belief fallback fuel utility bound loss unknown who steps =
      belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (pbsInformationConditionalProfile M belief fallback fuel utility bound loss who))
        steps) :=
  pbsInformationCFR_sampling_law M belief fallback (fun player h => utility h player) fuel
    (pbsInformationConditionalRounds M belief fuel bound loss) unknown who steps

/-- The selected child's public table entry and its sampled actual iterations
have the same complete continuation law at the factual posterior. -/
theorem cfrDInformationChildTable_sampling
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) :
    pbsInformationConditionalSample M (cfrDFactualChildBelief M trunk cut remaining obs possible)
        fallback remaining utility bound loss unknown who steps =
      (cfrDFactualChildBelief M trunk cut remaining obs possible).law.bind
        ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who
            (cfrDInformationChildTable M trunk fallback cut remaining utility bound loss obs who))
          steps) := by
  simp only [pbsInformationConditionalSample_eq, cfrDInformationChildTable, dif_pos possible]

/-- The actual parent-spliced child policy has that same sampled law. Only the
deploying player's policy changes; arbitrary unknown opponents are held fixed. -/
theorem cfrDInformationChildProfile_sampling
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) :
    pbsInformationConditionalSample M (cfrDFactualChildBelief M trunk cut remaining obs possible)
        fallback remaining utility bound loss unknown who steps =
      (cfrDFactualChildBelief M trunk cut remaining obs possible).law.bind
        ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who
            (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss who))
          steps) := by
  rw [cfrDInformationChildTable_sampling M trunk fallback cut remaining
    utility bound loss obs possible unknown who steps]
  apply FinDist.bind_congr
  intro first supported
  have rootPublic :=
    (cfrDFactualChildBelief M trunk cut remaining obs possible).supported first supported
  rw [publicRoot_trace_eq] at rootPublic
  apply (fullInformation M).runBehavioralFrom_congr
  intro later reaches _ player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    symm
    simpa only [rootPublic] using cfrDInformationChildProfile_of_reaches M trunk fallback cut
      remaining utility bound loss who first later
      (cfrDFactualChildBelief_atCut M trunk cut remaining obs possible first supported) reaches
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]

/-- All original-history observables agree, so parent value consumers can use
the same sampled iteration family rather than an unrelated child value witness. -/
theorem cfrDInformationChildProfile_sampling_value
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) (value : E.History → ℝ) :
    (pbsInformationConditionalSample M
      (cfrDFactualChildBelief M trunk cut remaining obs possible)
      fallback remaining utility bound loss unknown who steps).expect value =
      ((cfrDFactualChildBelief M trunk cut remaining obs possible).law.bind
        ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who
            (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss who))
          steps)).expect value :=
  congrArg (fun law : FinDist E.History => law.expect value)
    (cfrDInformationChildProfile_sampling M trunk fallback cut remaining
      utility bound loss obs possible unknown who steps)

/-- Rootwise sampling also realizes the parent's public-prefix splice.
The positive root belongs to the actual factual child; other probabilities
may be reweighted without changing either the recurrence or its count. -/
theorem cfrDInformationChildProfile_sampling_supported
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) (history : E.History)
    (supported : history ∈
      (cfrDFactualChildBelief M trunk cut remaining obs possible).law.support) :
    pbsInformationCFRSampleFrom M (cfrDFactualChildBelief M trunk cut remaining obs possible)
        fallback (fun player h => utility h player) remaining
        (pbsInformationConditionalRounds M
          (cfrDFactualChildBelief M trunk cut remaining obs possible) remaining bound loss)
        unknown who steps history =
      (fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss who))
        steps history := by
  rw [pbsInformationCFR_sampling_from_support M _ fallback _ remaining _
    unknown who steps history supported]
  have table : pbsInformationCFR M
      (cfrDFactualChildBelief M trunk cut remaining obs possible) fallback
      (fun player h => utility h player) remaining
      (pbsInformationConditionalRounds M
        (cfrDFactualChildBelief M trunk cut remaining obs possible) remaining bound loss) =
        cfrDInformationChildTable M trunk fallback cut remaining utility bound loss obs := by
    simp only [cfrDInformationChildTable, dif_pos possible]
    rfl
  rw [table]
  have rootPublic :=
    (cfrDFactualChildBelief M trunk cut remaining obs possible).supported history supported
  rw [publicRoot_trace_eq] at rootPublic
  apply (fullInformation M).runBehavioralFrom_congr
  intro later reaches _ player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    symm
    simpa only [rootPublic] using cfrDInformationChildProfile_of_reaches M trunk fallback cut
      remaining utility bound loss who history later
      (cfrDFactualChildBelief_atCut M trunk cut remaining obs possible history supported) reaches
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]

variable [∀ who info, Fintype ((fullInformation M).Choice who info)]

/-- Factual support of one complete private observation at a live cut. -/
def CFRDInformationQueryFactual (trunk : Profile (fullInformation M).behavioralSignature)
    (cut remaining : Nat) (who : Fin 2) (info : (fullInformation M).InfoState who) : Prop :=
  (info, true) ∈ (((fullInformation M).runBehavioral trunk cut).map
    (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support

/-- The parent's canonical unilateral reference conditional, retaining the
complete correlated history law and the live flag. It is not a private PBS. -/
def cfrDInformationQueryLaw (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (who : Fin 2) (info : (fullInformation M).InfoState who) : FinDist E.History :=
  (unilateralReferenceLaw (fullInformation M) trunk
    (cfrDInformationFallback M fallback) who cut).condOnFibre
      (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h)) (info, true)

omit [Fintype E.History] [∀ who, Fintype (E.Action who)]
  [∀ who info, Fintype ((fullInformation M).Choice who info)] in
/-- A factual private/live query supplies its public posterior witness.
No independent support premise or hidden-history policy input is required. -/
theorem cfrDInformationQuery_possible
    (trunk : Profile (fullInformation M).behavioralSignature) (cut remaining : Nat)
    (who : Fin 2) (info : (fullInformation M).InfoState who)
    (factual : CFRDInformationQueryFactual M trunk cut remaining who info) :
    CFRDFactualChildPossible M trunk cut remaining info.publicHistory := by
  classical
  have witness : (info, true) ∈ (((fullInformation M).runBehavioral trunk cut).map
      (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support :=
    factual
  rw [FinDist.support_map] at witness
  obtain ⟨history, reached, same⟩ := witness
  refine ⟨history, ⟨?_, congrArg Prod.snd same⟩, reached⟩
  rw [publicRoot_trace_eq]
  simpa only [publicHistory_infoOf] using
    congrArg AOH.publicHistory (congrArg Prod.fst same)

omit [Fintype E.History] [∀ who, Fintype (E.Action who)] in
/-- The actual reference query is supported by its factual child posterior.
This derives the domination needed for sampled-root reweighting. It does not
apply to a type with zero factual mass or to an arbitrary fallback conditional. -/
theorem cfrDInformationQuery_support
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (who : Fin 2) (info : (fullInformation M).InfoState who)
    (factual : CFRDInformationQueryFactual M trunk cut remaining who info)
    (history : E.History)
    (reached : history ∈
      (cfrDInformationQueryLaw M trunk fallback cut remaining who info).support) :
    history ∈ (cfrDFactualChildBelief M trunk cut remaining info.publicHistory
      (cfrDInformationQuery_possible M trunk cut remaining who info factual)).law.support := by
  classical
  let possible := cfrDInformationQuery_possible M trunk cut remaining who info factual
  let belief := cfrDFactualChildBelief M trunk cut remaining info.publicHistory possible
  let observe := fun h : E.History =>
    ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h)
  have witness : (info, true) ∈
      (((fullInformation M).runBehavioral trunk cut).map observe).support := factual
  rw [FinDist.support_map] at witness
  obtain ⟨first, positive, same⟩ := witness
  have inEvent : first ∈ {h : E.History |
      publicTrace (fullInformation M).toInfoSignals h.trace = info.publicHistory ∧
        cfrDCutLive remaining h = true} := by
    refine ⟨?_, congrArg Prod.snd same⟩
    rw [publicRoot_trace_eq]
    simpa only [observe, publicHistory_infoOf] using
      congrArg AOH.publicHistory (congrArg Prod.fst same)
  have inBelief : first ∈ belief.law.support :=
    FinDist.mem_support_condOn _ _ possible inEvent positive
  have sampled : (info, true) ∈ (belief.law.map observe).support := by
    rw [FinDist.support_map]
    exact ⟨first, inBelief, same⟩
  have equal := cfrDFactualChildBelief_referenceConditional M trunk
    (cfrDInformationFallback M fallback) cut remaining info.publicHistory possible
    who info rfl factual
  rw [cfrDInformationQueryLaw, ← equal] at reached
  exact cfrD_conditional_support_source belief.law observe (info, true) sampled history reached

/-- Evaluate a factual parent query using a private retained index of the same
actual child recurrence. Its posterior-dependent count is unchanged by the
private conditioning, and the unknown opponents are outside the private draw. -/
def cfrDInformationFactualQuerySample
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ)
    (who : Fin 2) (info : (fullInformation M).InfoState who)
    (factual : CFRDInformationQueryFactual M trunk cut remaining who info)
    (unknown : Profile (fullInformation M).behavioralSignature) (steps : Nat) : FinDist E.History :=
  let belief := cfrDFactualChildBelief M trunk cut remaining info.publicHistory
    (cfrDInformationQuery_possible M trunk cut remaining who info factual)
  (cfrDInformationQueryLaw M trunk fallback cut remaining who info).bind
    (pbsInformationCFRSampleFrom M belief fallback (fun player h => utility h player)
      remaining (pbsInformationConditionalRounds M belief remaining bound loss) unknown who steps)

/-- The actual parent's type-conditioned reference query has the sampled law
of the public-spliced child, with all root-support obligations discharged. -/
theorem cfrDInformationFactualQuerySample_law
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
            (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss who))
          steps) := by
  apply FinDist.bind_congr
  intro history reached
  exact cfrDInformationChildProfile_sampling_supported M trunk fallback cut remaining
    utility bound loss info.publicHistory
    (cfrDInformationQuery_possible M trunk cut remaining who info factual) unknown who
    steps history (cfrDInformationQuery_support M trunk fallback cut remaining
      who info factual history reached)

/-- Every original-history observable of the private query uses that same
retained child family. No individual iterate is asserted to be optimal. -/
theorem cfrDInformationFactualQuerySample_value
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ)
    (who : Fin 2) (info : (fullInformation M).InfoState who)
    (factual : CFRDInformationQueryFactual M trunk cut remaining who info)
    (unknown : Profile (fullInformation M).behavioralSignature) (steps : Nat)
    (value : E.History → ℝ) :
    (cfrDInformationFactualQuerySample M trunk fallback cut remaining utility bound loss
      who info factual unknown steps).expect value =
      ((cfrDInformationQueryLaw M trunk fallback cut remaining who info).bind
        ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who
            (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss who))
          steps)).expect value :=
  congrArg (fun law : FinDist E.History => law.expect value)
    (cfrDInformationFactualQuerySample_law M trunk fallback cut remaining utility bound loss
      who info factual unknown steps)

end GameTheory.ReBeL
