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

/-- A present public response attains its conditional value either at a
zero-own-reach root, WITHOUT a Nash assumption, or at a supported Nash type.
The first case includes entirely unvisited public states. -/
theorem cfrDPublicResponseCompletion_value_of_root_cases (cut : Nat)
    (table : CFRDPublicSliceTable M) (fallback : Profile (fullInformation M).strategicSignature)
    (remaining : Nat) (utility : E.History → ι → ℝ)
    (base : Profile (fullInformation M).behavioralSignature)
    {observations : List M.PublicSignal} {who : ι} {T : Type ut}
    (slice : TypeBeliefSlice (fullInformation M) observations who T)
    (present : table observations who = some ⟨T, slice⟩) (type : T)
    (atCut : ∀ h ∈ (slice.kernel type).law.support, h.trace.length = cut)
    (opponents : ∀ h ∈ (slice.kernel type).law.support, ∀ other, other ≠ who →
      (fullInformation M).playerReachProbability base other h.trace ≠ 0)
    (rootCase :
      (∀ h ∈ (slice.kernel type).law.support,
        (fullInformation M).playerReachProbability base who h.trace = 0) ∨
      ∃ own : FinDist T,
        IsNash (behavioralBeliefForm (fullInformation M) (slice.mixture own) remaining)
          (euPreference utility) base ∧ type ∈ own.support ∧
        ∀ h ∈ (slice.kernel type).law.support,
          (fullInformation M).playerReachProbability base who h.trace ≠ 0) :
    (PublicBelief.continuationLaw (fullInformation M)
        (cfrDCompleteZeroReach (fullInformation M) base
          (cfrDPublicResponseCompletion M cut table fallback remaining utility base))
        remaining (slice.kernel type)).expect (fun h => utility h who) =
      slice.infoValue fallback remaining (fun h => utility h who) base type := by
  let completion := cfrDPublicResponseCompletion M cut table fallback remaining utility base
  have localResponse : ∀ first ∈ (slice.kernel type).law.support,
      ∀ later, E.ReachesWithin remaining first later → ¬ E.terminal later.state →
        completion who ((fullInformation M).infoOf who later.trace) =
          (slice.simultaneousResponse fallback remaining (fun h => utility h who) base).toBehavioral
            ((fullInformation M).infoOf who later.trace) := by
    intro first supported later reaches _
    exact cfrDPublicResponseCompletion_local M cut table fallback remaining utility base
      slice present type first supported (atCut first supported) later reaches
  rcases rootCase with zero | ⟨own, equilibrium, supported, positive⟩
  · calc
      _ = slice.conditionalPayoff base remaining (fun h => utility h who)
          (completion who) type := by
        unfold TypeBeliefSlice.conditionalPayoff
        apply congrArg (fun law : FinDist E.History => law.expect (fun h => utility h who))
        apply FinDist.bind_congr
        intro history reached
        exact cfrDCompleteZeroReach_counterfactual_continuation (fullInformation M)
          (fullSignals_perfectRecall M.toInfoSignals) base completion who remaining history
          (zero history reached) (opponents history reached)
      _ = slice.conditionalPayoff base remaining (fun h => utility h who)
          (slice.simultaneousResponse fallback remaining (fun h => utility h who) base).toBehavioral
          type := slice.conditionalPayoff_eq_of_reachable_agreement base remaining
            (fun h => utility h who) _ _ type localResponse
      _ = _ := slice.simultaneousResponse_attains fallback remaining
        (fun h => utility h who) base type
  · exact slice.completed_value_eq_of_local_response
      (fullSignals_perfectRecall M.toInfoSignals) fallback remaining utility own base completion
      equilibrium type localResponse opponents (fun _ => positive)
      (fun absent => (absent supported).elim)

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

/-- Nash is needed only for genuinely factual live queries. A whole public
state may have zero factual mass; its reference-supported queries instead use
the constructed off-path response. No probability law with empty support is required. -/
theorem cfrDPublicResponseCompletion_live_leafOptimal (cut remaining : Nat)
    (table : CFRDPublicSliceTable M) (fallback : Profile (fullInformation M).strategicSignature)
    (utility : E.History → ι → ℝ) (base : Profile (fullInformation M).behavioralSignature)
    (who : ι)
    (queries : ∀ info : (fullInformation M).InfoState who,
      (info, true) ∈ ((unilateralReferenceLaw (fullInformation M) base fallback who cut).map
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support →
      ∃ (observations : List M.PublicSignal) (T : Type ut)
        (slice : TypeBeliefSlice (fullInformation M) observations who T) (type : T),
        table observations who = some ⟨T, slice⟩ ∧
        (slice.kernel type).law =
          (unilateralReferenceLaw (fullInformation M) base fallback who cut).condOnFibre
            (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))
            (info, true) ∧
        ((info, true) ∈ (((fullInformation M).runBehavioral base cut).map
          (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support →
          ∃ own : FinDist T,
            IsNash (behavioralBeliefForm (fullInformation M) (slice.mixture own) remaining)
              (euPreference utility) base ∧ type ∈ own.support)) :
    CFRDLeafOptimal (fullInformation M)
      (cfrDCompleteZeroReach (fullInformation M) base
        (cfrDPublicResponseCompletion M cut table fallback remaining utility base))
      fallback who (fun h => utility h who) cut remaining 0 := by
  classical
  intro target info sampled
  rw [cfrDCompleteZeroReach_referenceLaw (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals)] at sampled ⊢
  obtain ⟨observations, T, slice, type, present, kernel, onPath⟩ := queries info sampled
  have roots (history : E.History) (reached : history ∈ (slice.kernel type).law.support) :
      history ∈ ((unilateralReferenceLaw (fullInformation M) base fallback who cut).condOnFibre
        (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))
        (info, true)).support := by simpa only [kernel] using reached
  have opponents : ∀ h ∈ (slice.kernel type).law.support, ∀ other, other ≠ who →
      (fullInformation M).playerReachProbability base other h.trace ≠ 0 := by
    intro history reached other different
    exact cfrDReference_conditional_opponents (fullInformation M) base fallback who cut
      _ (info, true) sampled history (roots history reached) other different
  have actual : (PublicBelief.continuationLaw (fullInformation M)
      (cfrDCompleteZeroReach (fullInformation M) base
        (cfrDPublicResponseCompletion M cut table fallback remaining utility base)) remaining
      (slice.kernel type)).expect (fun h => utility h who) =
        slice.infoValue fallback remaining (fun h => utility h who) base type := by
    apply cfrDPublicResponseCompletion_value_of_root_cases M cut table fallback remaining
      utility base slice present type
    · intro history reached
      exact cfrDReference_live_rootDepth (fullInformation M) base fallback who cut remaining
        info sampled history (roots history reached)
    · exact opponents
    · by_cases factual : (info, true) ∈ (((fullInformation M).runBehavioral base cut).map
          (fun h => ((fullInformation M).infoOf who h.trace, cfrDCutLive remaining h))).support
      · obtain ⟨own, equilibrium, supported⟩ := onPath factual
        refine Or.inr ⟨own, equilibrium, supported, ?_⟩
        intro history reached
        exact (cfrDReference_factual_support_iff (fullInformation M)
          (fullSignals_perfectRecall M.toInfoSignals) base fallback who cut _ Prod.fst
          (fun _ => rfl) (info, true) sampled history (roots history reached)).mp factual
      · left
        intro history reached
        exact cfrDReference_factual_absent_own_zero (fullInformation M)
          (fullSignals_perfectRecall M.toInfoSignals) base fallback who cut _ Prod.fst
          (fun _ => rfl) (info, true) sampled factual history (roots history reached)
  have better := slice.conditionalPayoff_le_infoValue
    (fullSignals_perfectRecall M.toInfoSignals) fallback remaining
    (fun h => utility h who) base type target
  rw [← slice.completeZeroReach_conditionalPayoff
    (fullSignals_perfectRecall M.toInfoSignals) base
    (cfrDPublicResponseCompletion M cut table fallback remaining utility base) remaining
    (fun h => utility h who) target type opponents, ← actual] at better
  unfold conditionalOracleValue cfrDLeafGain
  rw [FinDist.expect_sub]
  apply sub_nonpos.mpr
  simpa only [TypeBeliefSlice.conditionalPayoff, PublicBelief.continuationLaw,
    FinDist.expect_bind, kernel] using better

end GameTheory.ReBeL
