/-
# Constructed public response tables discharge local continuation agreement

Optional typed query slices avoid demanding a probability law at impossible
public histories. At present queries, responses are computed by the existing
finite conditional optimizer and then spliced using only the public cut prefix.
The remaining query-game/Nash assumptions contain no policy-agreement premise.
-/

import GameTheory.Analysis.ReBeL.CFRDPublicSplice

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk ut
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

section RootDepth

variable [Fintype ι] [DecidableEq ι]
variable [∀ who info, Fintype (M.Choice who info)]

/-- A sampled live reference kernel consists of histories exactly at the cut.
Early terminal absorption cannot supply a live root of smaller depth. -/
theorem cfrDReference_live_rootDepth (base : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι) (cut remaining : Nat)
    (info : M.InfoState who)
    (sampled : (info, true) ∈ ((unilateralReferenceLaw M base fallback who cut).map
      (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h))).support)
    (history : E.History)
    (reached : history ∈ ((unilateralReferenceLaw M base fallback who cut).condOnFibre
      (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h)) (info, true)).support) :
    history.trace.length = cut := by
  have original := cfrD_conditional_support_source _ _ (info, true) sampled history reached
  have flag : cfrDCutLive remaining history = true := congrArg Prod.snd
    (conditionalOracle_support _ _ (info, true) sampled history reached)
  have live : remaining ≠ 0 ∧ ¬ E.terminal history.state := by
    simpa only [cfrDCutLive, decide_eq_true_eq] using flag
  rcases M.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
      (Profile.update base who (uniformLegalPolicy M who (fallback who))) cut
      E.initHistory history original with stopped | depth
  · exact (live.2 stopped).elim
  · simpa only [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length,
      Nat.zero_add] using depth

end RootDepth

/-- Query metadata may be absent at syntactic or impossible public histories.
Each present entry is an existing typed joint-belief slice, not a value certificate. -/
abbrev CFRDPublicSliceTable :=
  (observations : List M.PublicSignal) → (who : ι) →
    Option (Σ T : Type ut, TypeBeliefSlice (fullInformation M) observations who T)

variable [Fintype ι] [DecidableEq ι]
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- Compute the legal typewise best response at each present public query.
Absent entries use the supplied legal fallback; no posterior is invented there. -/
def cfrDPublicResponseTable (table : CFRDPublicSliceTable M)
    (fallback : Profile (fullInformation M).strategicSignature) (remaining : Nat)
    (utility : E.History → ι → ℝ) (base : Profile (fullInformation M).behavioralSignature) :
    List M.PublicSignal → Profile (fullInformation M).behavioralSignature := fun observations who =>
  match table observations who with
  | none => (fallback who).toBehavioral
  | some ⟨_, slice⟩ =>
      (slice.simultaneousResponse fallback remaining (fun h => utility h who) base).toBehavioral

/-- One complete joint completion is constructed from the computed public
response table. The selector sees neither hidden histories nor opponents' private data. -/
def cfrDPublicResponseCompletion (cut : Nat) (table : CFRDPublicSliceTable M)
    (fallback : Profile (fullInformation M).strategicSignature) (remaining : Nat)
    (utility : E.History → ι → ℝ) (base : Profile (fullInformation M).behavioralSignature) :
    Profile (fullInformation M).behavioralSignature :=
  cfrDPublicContinuation M cut (cfrDPublicResponseTable M table fallback remaining utility base)

/-- The constructed completion agrees with the computed response on every
legal continuation of each present query kernel, even at zero own reach. -/
theorem cfrDPublicResponseCompletion_local (cut : Nat) (table : CFRDPublicSliceTable M)
    (fallback : Profile (fullInformation M).strategicSignature) (remaining : Nat)
    (utility : E.History → ι → ℝ) (base : Profile (fullInformation M).behavioralSignature)
    {observations : List M.PublicSignal} {who : ι} {T : Type ut}
    (slice : TypeBeliefSlice (fullInformation M) observations who T)
    (present : table observations who = some ⟨T, slice⟩) (type : T)
    (first : E.History) (supported : first ∈ (slice.kernel type).law.support)
    (atCut : first.trace.length = cut) (later : E.History)
    (reaches : E.ReachesWithin remaining first later) :
    cfrDPublicResponseCompletion M cut table fallback remaining utility base who
        ((fullInformation M).infoOf who later.trace) =
      (slice.simultaneousResponse fallback remaining (fun h => utility h who) base).toBehavioral
        ((fullInformation M).infoOf who later.trace) := by
  have publicRoot := (slice.kernel type).supported first supported
  rw [publicRoot_trace_eq] at publicRoot
  unfold cfrDPublicResponseCompletion
  rw [cfrDPublicContinuation_eq_of_reaches M cut _ who first later atCut reaches, publicRoot]
  simp only [cfrDPublicResponseTable, present]

variable [∀ who info, Fintype ((fullInformation M).Choice who info)]

/-- The public constructor supplies local response agreement rather than
asking callers for it. Actual compatible query games and their Nash property
remain explicit obligations; no recursive child solver is assumed complete. -/
theorem cfrDPublicResponseCompletion_leafOptimal (cut remaining : Nat)
    (table : CFRDPublicSliceTable M) (fallback : Profile (fullInformation M).strategicSignature)
    (utility : E.History → ι → ℝ) (base : Profile (fullInformation M).behavioralSignature)
    (who : ι)
    (queries : ∀ info : (fullInformation M).InfoState who,
      (info, true) ∈ ((unilateralReferenceLaw (fullInformation M) base fallback who cut).map
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support →
      ∃ (observations : List M.PublicSignal) (T : Type ut)
        (slice : TypeBeliefSlice (fullInformation M) observations who T)
        (own : FinDist T) (type : T),
        table observations who = some ⟨T, slice⟩ ∧
        IsNash (behavioralBeliefForm (fullInformation M) (slice.mixture own) remaining)
          (euPreference utility) base ∧
        (slice.kernel type).law =
          (unilateralReferenceLaw (fullInformation M) base fallback who cut).condOnFibre
            (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))
            (info, true) ∧
        (type ∈ own.support ↔ (info, true) ∈ (((fullInformation M).runBehavioral base cut).map
          (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support)) :
    CFRDLeafOptimal (fullInformation M)
      (cfrDCompleteZeroReach (fullInformation M) base
        (cfrDPublicResponseCompletion M cut table fallback remaining utility base))
      fallback who (fun h => utility h who) cut remaining 0 := by
  apply cfrDCompleteZeroReach_leafOptimal_of_queryGames (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals)
  intro info sampled
  obtain ⟨observations, T, slice, own, type, present, equilibrium, kernel, factual⟩ :=
    queries info sampled
  refine ⟨observations, T, slice, own, type, equilibrium, ?_, kernel, factual⟩
  intro first supported later reaches _
  apply cfrDPublicResponseCompletion_local M cut table fallback remaining utility base
    slice present type first supported _ later reaches
  exact cfrDReference_live_rootDepth (fullInformation M) base fallback who cut remaining
    info sampled first (by simpa only [kernel] using supported)

end GameTheory.ReBeL
