/-
# Liar's Dice observations and legal policies

Private observations reveal only the observer's own die. Repeating that known
value at a later bid does not reveal the opponent's die. Public observations
record every bid and whose turn it is; full AOH retains the complete sequence.
-/

import GameTheory.ReBeL.Examples.LiarsDice
import GameTheory.ReBeL.Adapter

noncomputable section

namespace GameTheory.ReBeL.Examples.LiarsDice

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

/-- Public phase, with no private dice in its type. -/
inductive Phase where
  | initial
  | live (turn : Player) (last : Option Bid)
  | finished (winner : Player)
  deriving DecidableEq, Fintype

/-- What is announced after a transition. -/
def phase : State → Phase
  | .initial => .initial
  | .live _ turn last => .live turn last
  | .finished winner => .finished winner

/-- The observer's own die, never the opponent's. -/
def ownDie (i : Player) (dice : Dice) : Face := if i = 0 then dice.1 else dice.2

/-- Private observations at live positions. -/
def privateObservation (i : Player) : State → Option Face
  | .live dice _ _ => some (ownDie i dice)
  | _ => none

abbrev View := Phase × Option Face

/-- An analyst-side characterization of the compressed observation. -/
def view (i : Player) (state : State) : View := (phase state, privateObservation i state)

/-- The reduced accumulator is a convenience, not a perfect-recall assertion. -/
@[reducible]
def signals (prior : FinDist Dice) : InfoSignals (protocol prior) where
  PublicSignal := Phase
  PrivateSignal _ := Option Face
  initialPublic := .initial
  initialPrivate _ := none
  publicSignal event := phase event.target
  privateSignal i event := privateObservation i event.target
  InfoState _ := View
  initInfo _ privateSignal publicSignal := (publicSignal, privateSignal)
  pushInfo _ _ _ privateSignal publicSignal := (publicSignal, privateSignal)

theorem infoOf_view (prior : FinDist Dice) (i : Player) {state : State}
    (trace : (protocol prior).Trace state) : (signals prior).infoOf i trace = view i state :=
  infoOf_eq_view (signals prior) view (fun _ => rfl) (fun _ _ => rfl) i trace

/-- The complete menu is determined by the public phase, not either hidden die. -/
def menu (i : Player) (info : View) : Set (Option Move) :=
  match info.1 with
  | .live turn last => {choice | match choice with
      | some move => i = turn ∧ allowed last move
      | none => i ≠ turn}
  | _ => {none}

theorem menu_view (prior : FinDist Dice) (state : State) (i : Player) (choice : Option Move) :
    choice ∈ menu i (view i state) ↔ LegalOption (protocol prior) state i choice := by
  cases state <;> cases choice <;>
    simp [menu, view, phase, LegalOption, protocol, active, available]

/-- The adequacy law is proved for all realized histories, including terminal ones. -/
@[reducible]
def reducedModel (prior : FinDist Dice) : InformationModel (protocol prior) where
  toInfoSignals := signals prior
  menu := menu
  menu_adequate := by
    intro i state trace choice
    rw [infoOf_view]
    exact menu_view prior state i choice

/-- Strategies receive a full local AOH, not the physical State or pair of Dice. -/
@[reducible]
def model (prior : FinDist Dice) : InformationModel (protocol prior) :=
  fullInformation (reducedModel prior)

theorem perfectRecall (prior : FinDist Dice) : (model prior).PerfectRecall :=
  fullSignals_perfectRecall (signals prior)

/-- An arbitrary opening bid followed by a call at every later decision.
This defines actions at off-path later bids as well as the realized one. -/
def bidCallAction (opening : Bid) (i : Player) (info : View) : Option Move :=
  match info.1 with
  | .live turn last => if i = turn then
      some (match last with | none => .bid opening | some _ => .call) else none
  | _ => none

theorem bidCallAction_mem (opening : Bid) (i : Player) (info : View) :
    bidCallAction opening i info ∈ menu i info := by
  rcases info with ⟨phase, privateSignal⟩
  cases phase with
  | initial => rfl
  | finished winner => rfl
  | live turn last =>
      by_cases hi : i = turn
      · cases last <;> simp [bidCallAction, menu, hi, allowed]
      · simp [bidCallAction, menu, hi]

/-- A legal policy using public information only, a subfamily of all local policies. -/
def bidCallPolicy (prior : FinDist Dice) (opening : Bid) (i : Player) :
    (reducedModel prior).Policy i :=
  fun info => ⟨bidCallAction opening i info, bidCallAction_mem opening i info⟩

/-- The same policy on the actual perfect-recall strategy interface. -/
def fullBidCallPolicy (prior : FinDist Dice) (opening : Bid) (i : Player) :
    (model prior).Policy i :=
  liftPolicy (reducedModel prior) i (bidCallPolicy prior opening i)

/-- A proved state-indexed characterization, used only to calculate this policy's law. -/
def bidCallChooser (prior : FinDist Dice) (opening : Bid) : (protocol prior).Chooser :=
  fun state nonterminal => ⟨fun i => bidCallAction opening i (view i state),
    (protocol prior).legal_of_legalOption nonterminal (fun i =>
      (menu_view prior state i _).mp (bidCallAction_mem opening i (view i state)))⟩

theorem bidCall_historyChooser (prior : FinDist Dice) (opening : Bid) :
    (reducedModel prior).historyChooser (bidCallPolicy prior opening) =
      (bidCallChooser prior opening).toHistoryChooser := by
  funext history nonterminal
  apply Subtype.ext
  funext i
  change bidCallAction opening i ((signals prior).infoOf i history.trace) =
    bidCallAction opening i (view i history.state)
  rw [infoOf_view]

theorem map_state_bidCall_run (prior : FinDist Dice) (opening : Bid) (fuel : Nat) :
    FinDist.map History.state ((model prior).run (fullBidCallPolicy prior opening) fuel) =
      (protocol prior).runFor (bidCallChooser prior opening) fuel .initial := by
  change FinDist.map History.state
    ((fullInformation (reducedModel prior)).run
      (fun i => liftPolicy (reducedModel prior) i (bidCallPolicy prior opening i)) fuel) = _
  rw [liftPolicy_run]
  change FinDist.map History.state
    ((protocol prior).runHistoryFor ((reducedModel prior).historyChooser
      (bidCallPolicy prior opening)) fuel (protocol prior).initHistory) = _
  rw [bidCall_historyChooser]
  exact map_state_runHistoryFor (bidCallChooser prior opening) fuel (protocol prior).initHistory

end GameTheory.ReBeL.Examples.LiarsDice
