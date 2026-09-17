/-
# Public-rooted continuation regions and depth cuts

A public subgame is closed under legal continuation and under individual
indistinguishability. A depth cut is not a terminal history. These statements
use canonical histories and the existing behavioral runner.
-/

import GameTheory.ReBeL.BeliefExecution
import GameTheory.ReBeL.ReachFactorization

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

/-- Newest-first public observations extend a root by prefixing new observations. -/
def PublicSubgame (S : InfoSignals E) (root : List S.PublicSignal) : Set E.History :=
  {h | root <:+ publicTrace S h.trace}

/-- Public subgames do not cut an individual full-AOH information set in half. -/
theorem publicSubgame_info_closed (S : InfoSignals E) (root : List S.PublicSignal)
    (i : ι) (first second : E.History)
    (same : (fullSignals S).infoOf i first.trace = (fullSignals S).infoOf i second.trace)
    (inside : first ∈ PublicSubgame S root) : second ∈ PublicSubgame S root := by
  unfold PublicSubgame at inside ⊢
  simpa only [publicTrace_eq_of_infoOf_eq S i first.trace second.trace same] using inside

/-- Every legal continuation preserves the public root, independently of any policy's reach. -/
theorem publicTrace_suffix_of_reaches (S : InfoSignals E)
    {fuel : Nat} {first second : E.History} (path : E.ReachesWithin fuel first second) :
    publicTrace S first.trace <:+ publicTrace S second.trace := by
  induction path with
  | refl => exact List.suffix_refl _
  | step joint legal realized rest ih =>
      exact List.IsSuffix.trans (List.suffix_cons _ _) ih

/-- The same closure holds for every history with positive mass under behavioral execution. -/
theorem publicTrace_suffix_of_run [Fintype ι] (M : InformationModel E)
    (profile : Profile M.behavioralSignature) :
    ∀ (fuel : Nat) (first second : E.History),
      second ∈ (M.runBehavioralFrom profile fuel first).support →
        publicTrace M.toInfoSignals first.trace <:+ publicTrace M.toInfoSignals second.trace := by
  intro fuel
  induction fuel with
  | zero =>
      intro first second reached
      rw [InformationModel.runBehavioralFrom, runRandomizedFor_zero,
        FinDist.mem_support_pure] at reached
      subst second
      exact List.suffix_refl _
  | succ fuel ih =>
      intro first second reached
      by_cases stopped : E.terminal first.state
      · rw [M.runBehavioralFrom_of_terminal profile (fuel + 1) stopped,
          FinDist.mem_support_pure] at reached
        subst second
        exact List.suffix_refl _
      · rw [M.runBehavioralFrom_succ_of_not_terminal profile fuel stopped,
          FinDist.support_bind] at reached
        simp only [Set.mem_iUnion] at reached
        obtain ⟨joint, _, inner⟩ := reached
        rw [FinDist.support_bindOnSupport] at inner
        simp only [Set.mem_iUnion] at inner
        obtain ⟨target, realized, rest⟩ := inner
        exact List.IsSuffix.trans (List.suffix_cons _ _)
          (ih (first.extend joint.2 realized) second rest)

namespace PublicBelief

variable [Fintype ι] (M : InformationModel E)

/-- PBS-rooted execution remains in the corresponding public subgame. -/
theorem continuation_in_publicSubgame (profile : Profile M.behavioralSignature)
    (fuel : Nat) {root : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals root)
    (target : E.History) (reached : target ∈ (continuationLaw M profile fuel belief).support) :
    target ∈ PublicSubgame M.toInfoSignals root := by
  rw [continuationLaw, FinDist.support_bind] at reached
  simp only [Set.mem_iUnion] at reached
  obtain ⟨first, positive, rest⟩ := reached
  have suffix := publicTrace_suffix_of_run M profile fuel first target rest
  simpa only [belief.supported first positive] using suffix

/-- A nonterminal depth-cut leaf, explicitly separate from a true game terminal. -/
def CutLeaf (root : List M.PublicSignal) (fuel : Nat) (target : E.History) : Prop :=
  ¬ E.terminal target.state ∧ target.trace.length + 1 = root.length + fuel

/-- Every sampled continuation outcome is a real terminal or a nonterminal depth cut. -/
theorem continuation_terminal_or_cut (profile : Profile M.behavioralSignature)
    (fuel : Nat) {root : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals root)
    (target : E.History) (reached : target ∈ (continuationLaw M profile fuel belief).support) :
    E.terminal target.state ∨ CutLeaf M root fuel target := by
  rw [continuationLaw, FinDist.support_bind] at reached
  simp only [Set.mem_iUnion] at reached
  obtain ⟨first, positive, rest⟩ := reached
  rcases M.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
    profile fuel first target rest with stopped | length
  · exact Or.inl stopped
  · by_cases stopped : E.terminal target.state
    · exact Or.inl stopped
    · right
      refine ⟨stopped, ?_⟩
      have rootLength := publicTrace_length M.toInfoSignals first.trace
      rw [belief.supported first positive] at rootLength
      omega

/-- Zero-fuel output at a live history is already a cut, not evidence of game termination. -/
theorem zero_fuel_cut (history : E.History) (live : ¬ E.terminal history.state) :
    CutLeaf M (publicTrace M.toInfoSignals history.trace) 0 history := by
  exact ⟨live, by rw [publicTrace_length, Nat.add_zero]⟩

end PublicBelief

end GameTheory.ReBeL
