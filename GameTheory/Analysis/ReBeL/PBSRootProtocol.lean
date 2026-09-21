/-
# A canonical protocol rooted by a joint public belief

One genuine chance step samples an original legal history. Subsequent states
retain that history and extend it by the original protocol's realized steps.
No independence assumption is imposed on the joint root law. The extra chance
step consumes one unit of fuel and does not ask a player to select a root.
-/

import GameTheory.ReBeL.Finite

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol
open GameTheory.Math.Probability

universe uι us ua
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

/-- Restart execution at a finite law of legal histories, preserving all
realized transition evidence. `none` is the unique administrative root. -/
@[reducible]
def pbsRootProtocol (roots : FinDist E.History) : ExecutionProtocol ι where
  State := Option E.History
  Action := E.Action
  init := none
  active state i := match state with
    | none => False
    | some history => E.active history.state i
  available state i := match state with
    | none => ∅
    | some history => E.available history.state i
  terminal state := match state with
    | none => False
    | some history => E.terminal history.state
  step state draw := match state with
    | none => roots.map some
    | some history =>
        (E.step history.state draw).bindOnSupport fun _ realized =>
          FinDist.pure (some (history.extend draw.2 realized))
  progress state nonterminal := by
    cases state with
    | none => exact ⟨fun _ => none, fun _ => not_false⟩
    | some history => exact E.progress history.state nonterminal

/-- The administrative root is chance, never a player decision. -/
theorem pbsRootProtocol_isChance (roots : FinDist E.History) :
    (pbsRootProtocol roots).IsChance none :=
  ⟨not_false, fun _ => not_false⟩

/-- The entire joint law, including hidden correlations, is sampled once. -/
theorem pbsRootProtocol_chanceLaw (roots : FinDist E.History) :
    (pbsRootProtocol roots).chanceLaw (pbsRootProtocol_isChance roots) = roots.map some :=
  rfl

/-- Supported continuations are exactly realized original-history extensions. -/
theorem pbsRootProtocol_step_support (roots : FinDist E.History) (history : E.History)
    (draw : {joint // E.Legal history.state joint}) (next : Option E.History) :
    next ∈ ((pbsRootProtocol roots).step (some history) draw).support ↔
      ∃ (target : E.State) (realized : target ∈ (E.step history.state draw).support),
        next = some (history.extend draw.2 realized) := by
  simp only [pbsRootProtocol, FinDist.support_bindOnSupport, Set.mem_iUnion,
    FinDist.mem_support_pure]

/-- Every sampled root is an original legal history; no synthetic state is
identified with the administrative root. -/
theorem pbsRootProtocol_step_none_support (roots : FinDist E.History)
    (draw : {joint // (pbsRootProtocol roots).Legal none joint})
    (next : Option E.History) :
    next ∈ ((pbsRootProtocol roots).step none draw).support ↔
      ∃ history ∈ roots.support, some history = next := by
  change next ∈ (roots.map some).support ↔ _
  rw [FinDist.support_map]
  rfl

/-- The longest legal original history; no unique-predecessor assumption. -/
def pbsRootMaxDepth [Fintype E.History] : Nat :=
  Finset.univ.sup (fun history : E.History => history.trace.length)

/-- Finite enumeration bounds every original legal history, not just roots. -/
theorem pbsRoot_length_le [Fintype E.History] (history : E.History) :
    history.trace.length ≤ pbsRootMaxDepth (E := E) := by
  exact Finset.le_sup (f := fun h : E.History => h.trace.length) (Finset.mem_univ history)

/-- One additional rank unit accounts for the initial joint-belief draw. -/
def pbsRootRank [Fintype E.History] : Option E.History → Nat
  | none => pbsRootMaxDepth (E := E) + 1
  | some history => pbsRootMaxDepth (E := E) - history.trace.length

/-- Even merging-state protocols cannot loop through the retained history. -/
theorem pbsRootRank_decreases [Fintype E.History] (roots : FinDist E.History)
    (event : (pbsRootProtocol roots).StepEvent) :
    pbsRootRank event.target < pbsRootRank event.source := by
  rcases event with ⟨source, joint, legal, target, realized⟩
  cases source with
  | none =>
      obtain ⟨history, _, rfl⟩ :=
        (pbsRootProtocol_step_none_support roots ⟨joint, legal⟩ target).mp realized
      simp only [pbsRootRank]
      omega
  | some history =>
      obtain ⟨next, hnext, rfl⟩ :=
        (pbsRootProtocol_step_support roots history ⟨joint, legal⟩ target).mp realized
      have hlength := pbsRoot_length_le (history.extend legal hnext)
      simp only [History.extend, Trace.length] at hlength
      simp only [pbsRootRank, History.extend, Trace.length]
      omega

/-- The canonical bounded-horizon predicate is derived, not supplied. -/
theorem pbsRootProtocol_bounded [Fintype E.History] (roots : FinDist E.History) :
    (pbsRootProtocol roots).BoundedHorizon (pbsRootMaxDepth (E := E) + 1) :=
  boundedHorizon_of_rank (E := pbsRootProtocol roots)
    (pbsRootRank (E := E)) (pbsRootRank_decreases roots)

/-- An explicit enumeration of every legal rooted history. Full original
histories, not just finite states, are the required finiteness input. -/
@[reducible]
def pbsRootHistoryFintype [Fintype E.History] [Fintype ι]
    [∀ i, Fintype (E.Action i)] (roots : FinDist E.History) :
    Fintype (pbsRootProtocol roots).History :=
  boundedHistoryFintype (pbsRootMaxDepth (E := E) + 1) (pbsRootProtocol_bounded roots)

end GameTheory.ReBeL
