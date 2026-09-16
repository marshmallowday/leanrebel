/-
# Finite histories without a tree-shaped-state assumption

Finite state/action carriers alone do not make histories finite: loops and
merging histories must be handled separately. This module uses the canonical
Protocol horizon predicate and retains every realized transition and action.
-/

import GameTheory.Protocol.Randomized
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol

universe uι us ua
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

/-- Terminality at the horizon also bounds every realized trace length. -/
theorem trace_length_le (horizon : Nat) (bounded : E.BoundedHorizon horizon)
    {state : E.State} (trace : E.Trace state) : trace.length ≤ horizon := by
  cases trace with
  | start => exact Nat.zero_le _
  | extend prior joint legal realized =>
      have hlt : prior.length < horizon := by
        by_contra h
        exact legal.1 (bounded _ prior (Nat.le_of_not_gt h))
      exact Nat.succ_le_of_lt hlt

/-- A decreasing rank bounds the trace without assuming unique predecessors. -/
theorem trace_rank_bound (rank : E.State → Nat)
    (decreases : ∀ event : E.StepEvent, rank event.target < rank event.source)
    {state : E.State} (trace : E.Trace state) :
    rank state + trace.length ≤ rank E.init := by
  induction trace with
  | start => simp [Trace.length]
  | extend prior joint legal realized ih =>
      have hd := decreases ⟨_, joint, legal, _, realized⟩
      dsimp only at hd
      simp only [Trace.length]
      omega

/-- A nonterminal zero-rank state contradicts progress and nonempty support. -/
theorem terminal_of_rank_zero (rank : E.State → Nat)
    (decreases : ∀ event : E.StepEvent, rank event.target < rank event.source)
    (state : E.State) (hzero : rank state = 0) : E.terminal state := by
  by_contra hterm
  obtain ⟨joint, legal⟩ := E.exists_legal hterm
  obtain ⟨target, realized⟩ := (E.step state ⟨joint, legal⟩).support_nonempty
  have hd := decreases ⟨state, joint, legal, target, realized⟩
  dsimp only at hd
  omega

/-- Rank certificates produce the existing bounded-horizon predicate. -/
theorem boundedHorizon_of_rank (rank : E.State → Nat)
    (decreases : ∀ event : E.StepEvent, rank event.target < rank event.source) :
    E.BoundedHorizon (rank E.init) := by
  intro state trace hlength
  have hr := trace_rank_bound rank decreases trace
  apply terminal_of_rank_zero rank decreases state
  omega

/-- The canonical randomized runner terminates with enough fuel. -/
theorem run_terminal_of_horizon (horizon : Nat) (bounded : E.BoundedHorizon horizon)
    (chooser : E.RandomizedChooser) (fuel : Nat) (hfuel : horizon ≤ fuel)
    (start next : E.History)
    (hnext : next ∈ (E.runRandomizedFor chooser fuel start).support) :
    E.terminal next.state := by
  rcases E.runRandomizedFor_terminal_or_length chooser fuel start next hnext with ht | hl
  · exact ht
  · apply bounded next.state next.trace
    omega

/-- Proof-free enumeration data, not an input to a player's policy. -/
abbrev EventCode (E : ExecutionProtocol ι) :=
  E.State × (∀ i, Option (E.Action i)) × E.State

/-- Forget only an event's proof fields. -/
def stepEventCode (event : E.StepEvent) : EventCode E :=
  (event.source, event.joint, event.target)

/-- Keep all actions and both endpoints, in newest-first order. -/
def traceCode : {state : E.State} → E.Trace state → List (EventCode E)
  | _, .start => []
  | _, .extend prior joint legal realized =>
      stepEventCode ⟨_, joint, legal, _, realized⟩ :: traceCode prior

@[simp]
theorem traceCode_length {state : E.State} (trace : E.Trace state) :
    (traceCode trace).length = trace.length := by
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih =>
      simp only [traceCode, List.length_cons, Trace.length, ih]

/-- Encoding equality preserves the complete dependent history. -/
theorem history_eq_of_traceCode_eq {first second : E.State}
    (traceFirst : E.Trace first) (traceSecond : E.Trace second)
    (hcode : traceCode traceFirst = traceCode traceSecond) :
    (⟨first, traceFirst⟩ : E.History) = ⟨second, traceSecond⟩ := by
  induction traceFirst generalizing second with
  | start =>
      cases traceSecond with
      | start => rfl
      | extend prior joint legal realized => cases hcode
  | @extend source target prior joint legal realized ih =>
      cases traceSecond with
      | start => cases hcode
      | @extend otherSource _ otherPrior otherJoint otherLegal otherRealized =>
          obtain ⟨hevent, hprior⟩ := List.cons.inj hcode
          have hs : source = otherSource := congrArg Prod.fst hevent
          have hj : joint = otherJoint := congrArg (fun event => event.2.1) hevent
          have ht : target = second := congrArg (fun event => event.2.2) hevent
          subst otherSource
          subst otherJoint
          subst second
          have hh := ih otherPrior hprior
          have hp : prior = otherPrior := by simpa using (History.mk.inj hh).2
          subst otherPrior
          rfl

/-- Fixed-size padding of at most `horizon` events. -/
def boundedHistoryCode (horizon : Nat) (history : E.History) :
    Fin horizon → Option (EventCode E) :=
  fun index => (traceCode history.trace)[index.val]?

/-- Padding is injective by the proved length bound. -/
theorem boundedHistoryCode_injective (horizon : Nat)
    (bounded : E.BoundedHorizon horizon) :
    Function.Injective (boundedHistoryCode (E := E) horizon) := by
  intro first second heq
  apply history_eq_of_traceCode_eq first.trace second.trace
  apply List.ext_getElem?
  intro index
  by_cases hin : index < horizon
  · exact congrFun heq ⟨index, hin⟩
  · have hindex : horizon ≤ index := Nat.le_of_not_gt hin
    have hfirst := trace_length_le horizon bounded first.trace
    have hsecond := trace_length_le horizon bounded second.trace
    rw [List.getElem?_eq_none (by simpa using hfirst.trans hindex),
      List.getElem?_eq_none (by simpa using hsecond.trans hindex)]

/-- Explicit history enumeration, permitting merging states. No general
finite-to-enumeration escape hatch or tree-shaped-state assumption is used. -/
@[reducible]
def boundedHistoryFintype [Fintype ι] [Fintype E.State]
    [∀ i, Fintype (E.Action i)] (horizon : Nat) (bounded : E.BoundedHorizon horizon) :
    Fintype E.History := by
  classical
  exact Fintype.ofInjective (boundedHistoryCode horizon)
    (boundedHistoryCode_injective horizon bounded)

end GameTheory.ReBeL
