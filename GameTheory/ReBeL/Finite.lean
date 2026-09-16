/-
# Finite histories without a tree-shaped-state assumption

ReBeL's initial formalization scope is finite players, finite state/action
carriers and a finite horizon. A finite state space alone is not sufficient:
loops can generate infinitely many histories, and distinct histories can merge
at one state. The enumeration below retains every realized joint action and
state transition and uses the horizon, never `IsTreeShaped`.
-/

import GameTheory.Protocol.Randomized

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol

universe uι us ua

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

/-- A terminality bound also bounds the length of every realized history,
because terminal histories cannot be extended by a legal action. -/
theorem trace_length_le (horizon : Nat) (bounded : E.BoundedHorizon horizon)
    {state : E.State} (trace : E.Trace state) : trace.length ≤ horizon := by
  induction trace with
  | start => exact Nat.zero_le _
  | extend prior joint legal realized ih =>
      have hlt : prior.length < horizon := by
        by_contra h
        exact legal.1 (bounded _ prior (Nat.le_of_not_gt h))
      exact Nat.succ_le_of_lt hlt

/-- A decreasing natural-number rank bounds the length even when histories
merge. No correspondence between a state and a unique history is assumed. -/
theorem trace_rank_bound (rank : E.State → Nat)
    (decreases : ∀ event : E.StepEvent, rank event.target < rank event.source)
    {state : E.State} (trace : E.Trace state) :
    rank state + trace.length ≤ rank E.init := by
  induction trace with
  | start => simp [Trace.length]
  | extend prior joint legal realized ih =>
      have hd := decreases ⟨_, joint, legal, _, realized⟩
      simp only [Trace.length]
      omega

/-- Progress and a genuine probability distribution exclude a non-terminal
zero-rank state: there must be a supported successor, whose rank decreases. -/
theorem terminal_of_rank_zero (rank : E.State → Nat)
    (decreases : ∀ event : E.StepEvent, rank event.target < rank event.source)
    (state : E.State) (hzero : rank state = 0) : E.terminal state := by
  by_contra hterm
  obtain ⟨joint, legal⟩ := E.exists_legal hterm
  obtain ⟨target, realized⟩ := (E.step state ⟨joint, legal⟩).support_nonempty
  have hd := decreases ⟨state, joint, legal, target, realized⟩
  omega

/-- A rank certificate produces the canonical Protocol horizon predicate. -/
theorem boundedHorizon_of_rank (rank : E.State → Nat)
    (decreases : ∀ event : E.StepEvent, rank event.target < rank event.source) :
    E.BoundedHorizon (rank E.init) := by
  intro state trace hlength
  have hr := trace_rank_bound rank decreases trace
  apply terminal_of_rank_zero rank decreases state
  omega

/-- Running at least the global horizon from any reachable history stops.
The terminality conclusion is about the existing randomized runner. -/
theorem run_terminal_of_horizon (horizon : Nat) (bounded : E.BoundedHorizon horizon)
    (chooser : E.RandomizedChooser) (fuel : Nat) (hfuel : horizon ≤ fuel)
    (start next : E.History)
    (hnext : next ∈ (E.runRandomizedFor chooser fuel start).support) :
    E.terminal next.state := by
  rcases E.runRandomizedFor_terminal_or_length chooser fuel start next hnext with ht | hl
  · exact ht
  · apply bounded next.state next.trace
    omega

/-- Proof-free event data. This is an enumeration code, not a policy input. -/
abbrev EventCode (E : ExecutionProtocol ι) :=
  E.State × (∀ i, Option (E.Action i)) × E.State

/-- Encode the realized trace in newest-first order, retaining joint actions
and both endpoints; an endpoint alone would lose merging histories. -/
def traceCode : {state : E.State} → E.Trace state → List (EventCode E)
  | _, .start => []
  | _, .extend prior joint _ _ => (_, joint, _) :: traceCode prior

@[simp]
theorem traceCode_length {state : E.State} (trace : E.Trace state) :
    (traceCode trace).length = trace.length := by
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih =>
      simp only [traceCode, List.length_cons, Trace.length, ih]

/-- Encoding equality preserves the complete history, not merely the state. -/
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
      | @extend otherSource otherTarget otherPrior otherJoint otherLegal otherRealized =>
          obtain ⟨hevent, hprior⟩ := List.cons.inj hcode
          have hs : source = otherSource := congrArg Prod.fst hevent
          have hj : joint = otherJoint := congrArg (fun event => event.2.1) hevent
          have ht : target = otherTarget := congrArg (fun event => event.2.2) hevent
          subst otherSource
          subst otherJoint
          subst otherTarget
          have hh := ih otherPrior hprior
          have hp : prior = otherPrior := by simpa using (History.mk.inj hh).2
          subst otherPrior
          rfl

/-- A fixed-size finite carrier for histories of at most `horizon` events.
Padding uses `none`, while every realized event uses `some`. -/
def boundedHistoryCode (horizon : Nat) (history : E.History) :
    Fin horizon → Option (EventCode E) :=
  fun index => (traceCode history.trace)[index.val]?

/-- Fixed-size padding is injective because all remaining entries are absent
by the proved horizon bound. -/
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

/-- Explicit finite enumeration of all realized histories in a finite-horizon
finite-carrier protocol. It permits merging states and does not assume a
history/state bijection or a general finite-to-enumeration escape hatch. -/
@[reducible]
def boundedHistoryFintype [Fintype ι] [Fintype E.State]
    [∀ i, Fintype (E.Action i)] (horizon : Nat) (bounded : E.BoundedHorizon horizon) :
    Fintype E.History :=
  Fintype.ofInjective (boundedHistoryCode horizon) (boundedHistoryCode_injective horizon bounded)

end GameTheory.ReBeL
