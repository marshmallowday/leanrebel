/-
# Two simultaneous decision stages with privately observed correlated types

Chance draws two bits. Each player sees only its own bit. Both players choose
simultaneously at both stages. Stage one pays player zero +1 for matching and
-1 otherwise. At stage two player zero guesses player one's type; player one's
simultaneous bit chooses whether a correct guess wins. Both stage rewards are
zero-sum. First-stage actions are not retained in the physical state: distinct
histories can merge, while their full AOHs retain the player's own action.
-/

import GameTheory.ReBeL.Adapter
import GameTheory.ReBeL.Payoff
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

abbrev Player := Fin 2
abbrev Types := Bool × Bool
abbrev Joint := Player → Option Bool

/-- Physical state, deliberately not an encoding of the complete history. -/
inductive State
  | initial
  | first (types : Types)
  | second (types : Types) (firstWin : Bool)
  | finished (firstWin finalWin : Bool)
  deriving DecidableEq, Fintype

/-- Public observations do not disclose either privately drawn type. -/
inductive Phase
  | initial
  | first
  | second (firstWin : Bool)
  | finished (firstWin finalWin : Bool)
  deriving DecidableEq, Fintype

/-- Select the player's own coordinate, never the opponent's. -/
def ownType (i : Player) (types : Types) : Bool := if i = 0 then types.1 else types.2

/-- Both players are active together, or neither is active. -/
def active : State → Player → Prop
  | .first _, _ => True
  | .second _ _, _ => True
  | _, _ => False

/-- Only the state after the second simultaneous decision is terminal. -/
def terminal : State → Prop
  | .finished _ _ => True
  | _ => False

/-- The unused `none` case is irrelevant at legal active nodes. -/
def action (joint : Joint) (i : Player) : Bool := (joint i).getD false

def firstResult (joint : Joint) : Bool := action joint 0 == action joint 1

def finalResult (types : Types) (joint : Joint) : Bool :=
  (action joint 0 == types.2) == action joint 1

/-- Chance is a transition law, not an additional strategic player. -/
def transition (prior : FinDist Types) : State → Joint → FinDist State
  | .initial, _ => FinDist.map State.first prior
  | .first types, joint => FinDist.pure (.second types (firstResult joint))
  | .second types firstWin, joint => FinDist.pure (.finished firstWin (finalResult types joint))
  | .finished firstWin finalWin, _ => FinDist.pure (.finished firstWin finalWin)

@[reducible]
def protocol (prior : FinDist Types) : ExecutionProtocol Player where
  State := State
  Action _ := Bool
  init := .initial
  active := active
  available _ _ := Set.univ
  terminal := terminal
  step state joint := transition prior state joint.1
  progress := by
    intro state hterm
    cases state with
    | initial => exact ⟨fun _ => none, by intro i; trivial⟩
    | first types => exact ⟨fun _ => some false, by intro i; trivial⟩
    | second types firstWin => exact ⟨fun _ => some false, by intro i; trivial⟩
    | finished firstWin finalWin => exact False.elim (hterm trivial)

/-- An explicit three-transition rank: chance, first decision, second decision. -/
def rank : State → Nat
  | .initial => 3
  | .first _ => 2
  | .second _ _ => 1
  | .finished _ _ => 0

theorem rank_decreases (prior : FinDist Types) (event : (protocol prior).StepEvent) :
    rank event.target < rank event.source := by
  rcases event with ⟨source, joint, legal, target, realized⟩
  cases source with
  | initial =>
      change target ∈ (FinDist.map State.first prior).support at realized
      rw [FinDist.support_map] at realized
      obtain ⟨types, _, rfl⟩ := realized
      decide
  | first types =>
      change target ∈ (FinDist.pure (.second types (firstResult joint))).support at realized
      rw [FinDist.mem_support_pure] at realized
      subst target
      decide
  | second types firstWin =>
      change target ∈ (FinDist.pure (.finished firstWin (finalResult types joint))).support at realized
      rw [FinDist.mem_support_pure] at realized
      subst target
      decide
  | finished firstWin finalWin => exact False.elim (legal.1 trivial)

theorem bounded (prior : FinDist Types) : (protocol prior).BoundedHorizon 3 :=
  boundedHorizon_of_rank rank (rank_decreases prior)

/-- Enumerate all histories, including off-policy histories and merging paths. -/
@[reducible]
def historyFintype (prior : FinDist Types) : Fintype (protocol prior).History :=
  boundedHistoryFintype 3 (bounded prior)

def phase : State → Phase
  | .initial => .initial
  | .first _ => .first
  | .second _ firstWin => .second firstWin
  | .finished firstWin finalWin => .finished firstWin finalWin

/-- The private signal is issued only at the type draw. -/
def privateObservation (i : Player) : State → Option Bool
  | .first types => some (ownType i types)
  | _ => none

abbrev View := Phase × Bool

def view (i : Player) : State → View
  | .initial => (.initial, false)
  | .first types => (.first, ownType i types)
  | .second types firstWin => (.second firstWin, ownType i types)
  | .finished firstWin finalWin => (.finished firstWin finalWin, false)

/-- A convenience reduction of the full observations; it is not asserted to
have perfect recall. The public policy interface below uses the full AOH. -/
def updateView (previous : View) (privateSignal : Option Bool) : Phase → View
  | .initial => (.initial, false)
  | .first => (.first, privateSignal.getD false)
  | .second firstWin => (.second firstWin, previous.2)
  | .finished firstWin finalWin => (.finished firstWin finalWin, false)

@[reducible]
def signals (prior : FinDist Types) : InfoSignals (protocol prior) where
  PublicSignal := Phase
  PrivateSignal _ := Option Bool
  initialPublic := .initial
  initialPrivate _ := none
  publicSignal event := phase event.target
  privateSignal i event := privateObservation i event.target
  InfoState _ := View
  initInfo _ _ _ := (.initial, false)
  pushInfo _ previous _ privateSignal publicSignal := updateView previous privateSignal publicSignal

theorem view_update (prior : FinDist Types) (event : (protocol prior).StepEvent) (i : Player) :
    (signals prior).pushInfo i (view i event.source) (event.joint i)
      ((signals prior).privateSignal i event) ((signals prior).publicSignal event) =
        view i event.target := by
  rcases event with ⟨source, joint, legal, target, realized⟩
  cases source with
  | initial =>
      change target ∈ (FinDist.map State.first prior).support at realized
      rw [FinDist.support_map] at realized
      obtain ⟨types, _, rfl⟩ := realized
      rfl
  | first types =>
      change target ∈ (FinDist.pure (.second types (firstResult joint))).support at realized
      rw [FinDist.mem_support_pure] at realized
      subst target
      rfl
  | second types firstWin =>
      change target ∈ (FinDist.pure (.finished firstWin (finalResult types joint))).support at realized
      rw [FinDist.mem_support_pure] at realized
      subst target
      rfl
  | finished firstWin finalWin => exact False.elim (legal.1 trivial)

theorem infoOf_view (prior : FinDist Types) (i : Player) {state : State}
    (trace : (protocol prior).Trace state) : (signals prior).infoOf i trace = view i state :=
  infoOf_eq_view (signals prior) view (fun _ => rfl) (view_update prior) i trace

/-- All Boolean actions are available at either simultaneous decision stage. -/
def menu (info : View) : Set (Option Bool) :=
  match info.1 with
  | .first => {choice | ∃ value, choice = some value}
  | .second _ => {choice | ∃ value, choice = some value}
  | _ => {none}

@[reducible]
def reducedModel (prior : FinDist Types) : InformationModel (protocol prior) where
  toInfoSignals := signals prior
  menu _ := menu
  menu_adequate := by
    intro i state trace choice
    rw [infoOf_view]
    cases state <;> cases choice <;> simp [menu, view, LegalOption, protocol, active]

/-- Strategies receive full local AOHs, never physical states or type pairs. -/
@[reducible]
def model (prior : FinDist Types) : InformationModel (protocol prior) :=
  fullInformation (reducedModel prior)

theorem perfectRecall (prior : FinDist Types) : (model prior).PerfectRecall :=
  fullSignals_perfectRecall (signals prior)

theorem simultaneous_first (prior : FinDist Types) (types : Types) (i : Player) :
    (protocol prior).active (.first types) i := trivial

theorem simultaneous_second (prior : FinDist Types) (types : Types) (firstWin : Bool) (i : Player) :
    (protocol prior).active (.second types firstWin) i := trivial

theorem no_chance_player (prior : FinDist Types) (i : Player) :
    ¬ (protocol prior).active .initial i := not_false

end GameTheory.ReBeL.Examples.HiddenTypes
