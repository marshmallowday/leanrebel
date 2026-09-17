/-
# A finite Liar's Dice rule instance

One die per player, three faces, highest face wild. All strictly increasing
bid sequences are allowed; the game is not truncated to one bid and one call.
Rule locators: facebookresearch/rebel@7960a42750f3407ea9eb2c3333d4c2a7961f6df4,
csrc/liars_dice/liars_dice.h:51-129. This early semantic instance is not a
refinement proof for the complete C++ implementation (the M10 obligation).
-/

import GameTheory.ReBeL.Finite
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases

noncomputable section

namespace GameTheory.ReBeL.Examples.LiarsDice

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

abbrev Player := Fin 2
abbrev Face := Fin 3
abbrev Dice := Face × Face
abbrev Bid := Fin 6

/-- Six quantity-first bids and the separate challenge action. -/
inductive Move where
  | bid (value : Bid)
  | call
  deriving DecidableEq, Fintype

/-- The other strategic player, not a chance player. -/
def other (i : Player) : Player := if i = 0 then 1 else 0

theorem other_other (i : Player) : other (other i) = i := by
  fin_cases i <;> rfl

theorem other_ne (i : Player) : other i ≠ i := by
  fin_cases i <;> decide

/-- Official quantity-first action decoding. -/
def quantity (bid : Bid) : Nat := 1 + bid.val / 3

/-- The face component of the same encoded bid. -/
def bidFace (bid : Bid) : Face := ⟨bid.val % 3, Nat.mod_lt _ (by decide)⟩

/-- A die matching both the bid face and the wild face is counted only once. -/
def matches (die face : Face) : Nat := if die = face ∨ die = 2 then 1 else 0

/-- Truth of a bid, evaluated by the game, not supplied to a player's policy. -/
def truthful (dice : Dice) (bid : Bid) : Prop :=
  quantity bid ≤ matches dice.1 (bidFace bid) + matches dice.2 (bidFace bid)

instance (dice : Dice) (bid : Bid) : Decidable (truthful dice bid) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Legal moves depend on the public last bid alone. -/
def allowed : Option Bid → Move → Prop
  | none, .bid _ => True
  | some previous, .bid next => previous < next
  | none, .call => False
  | some _, .call => True

/-- Physical state. Different bidding histories may reach the same live state. -/
inductive State where
  | initial
  | live (dice : Dice) (turn : Player) (last : Option Bid)
  | finished (winner : Player)
  deriving DecidableEq, Fintype

/-- Only the public player-to-move is active; the initial draw has no active players. -/
def active : State → Player → Prop
  | .live _ turn _, i => i = turn
  | _, _ => False

/-- Information-local rule restrictions will be connected to this menu below. -/
def available : State → Player → Set Move
  | .live _ _ last, _ => {move | allowed last move}
  | _, _ => Set.univ

/-- A challenge, not merely a fuel limit, ends play. -/
def terminal : State → Prop
  | .finished _ => True
  | _ => False

abbrev Joint := Player → Option Move

/-- Total analyst-side selector; its fallback is unreachable at a legal live step. -/
def selected (joint : Joint) (turn : Player) : Move := (joint turn).getD (.bid 0)

/-- Perform a move. The illegal opening-call branch is excluded by Protocol legality. -/
def advance (dice : Dice) (turn : Player) (last : Option Bid) : Move → State
  | .bid next => .live dice (other turn) (some next)
  | .call => match last with
    | none => .finished turn
    | some previous => .finished (if truthful dice previous then other turn else turn)

/-- Chance is a finite law, followed by deterministic strategic transitions. -/
def transition (prior : FinDist Dice) : State → Joint → FinDist State
  | .initial, _ => prior.map (fun dice => .live dice 0 none)
  | .live dice turn last, joint => FinDist.pure (advance dice turn last (selected joint turn))
  | .finished winner, _ => FinDist.pure (.finished winner)

/-- The game uses the existing execution interface and preserves all legal raises. -/
@[reducible]
def protocol (prior : FinDist Dice) : ExecutionProtocol Player where
  State := State
  Action _ := Move
  init := .initial
  active := active
  available := available
  terminal := terminal
  step state joint := transition prior state joint.1
  progress := by
    intro state hterm
    cases state with
    | initial => exact ⟨fun _ => none, by intro i; trivial⟩
    | live dice turn last =>
        let move : Move := match last with | none => .bid 0 | some _ => .call
        refine ⟨fun i => if i = turn then some move else none, ?_⟩
        intro i
        by_cases hi : i = turn
        · subst i
          cases last <;> simp [move, active, available, allowed]
        · simp [hi, active]
    | finished winner => exact False.elim (hterm trivial)

/-- A legal live step supplies a real move from the public rule menu. -/
theorem selected_allowed (prior : FinDist Dice) (dice : Dice) (turn : Player)
    (last : Option Bid) (joint : Joint) (legal : (protocol prior).Legal (.live dice turn last) joint) :
    allowed last (selected joint turn) := by
  have h := legal.2 turn
  cases choice : joint turn with
  | none =>
      change (match joint turn with
        | some move => turn = turn ∧ allowed last move
        | none => ¬ turn = turn) at h
      rw [choice] at h
      exact False.elim (h rfl)
  | some move =>
      change (match joint turn with
        | some move => turn = turn ∧ allowed last move
        | none => ¬ turn = turn) at h
      rw [choice] at h
      simpa [selected, choice] using h.2

/-- Strictly increasing encoded bids yield a decreasing rank through every possible play. -/
def rank : State → Nat
  | .initial => 8
  | .live _ _ none => 7
  | .live _ _ (some bid) => 6 - bid.val
  | .finished _ => 0

theorem rank_decreases (prior : FinDist Dice) (event : (protocol prior).StepEvent) :
    rank event.target < rank event.source := by
  rcases event with ⟨source, joint, legal, target, realized⟩
  cases source with
  | initial =>
      change target ∈ (prior.map (fun dice => State.live dice 0 none)).support at realized
      rw [FinDist.support_map] at realized
      obtain ⟨dice, _, rfl⟩ := realized
      decide
  | live dice turn last =>
      change target ∈ (FinDist.pure (advance dice turn last (selected joint turn))).support at realized
      rw [FinDist.mem_support_pure] at realized
      subst target
      have permitted := selected_allowed prior dice turn last joint legal
      cases choice : selected joint turn with
      | bid next =>
          rw [choice] at permitted
          cases last with
          | none =>
              simp only [advance, rank]
              omega
          | some previous =>
              change previous.val < next.val at permitted
              simp only [advance, rank]
              have bound := next.isLt
              omega
      | call =>
          rw [choice] at permitted
          cases last with
          | none => exact False.elim permitted
          | some previous =>
              simp only [advance, rank]
              have bound := previous.isLt
              omega
  | finished winner => exact False.elim (legal.1 trivial)

theorem bounded (prior : FinDist Dice) : (protocol prior).BoundedHorizon 8 :=
  boundedHorizon_of_rank (E := protocol prior) rank (rank_decreases prior)

/-- Finite histories without falsely requiring the physical states to form a tree. -/
@[reducible]
def historyFintype (prior : FinDist Dice) : Fintype (protocol prior).History :=
  boundedHistoryFintype 8 (bounded prior)

theorem opening_call_illegal : ¬ allowed none .call := not_false

theorem repeat_bid_illegal (bid : Bid) : ¬ allowed (some bid) (.bid bid) :=
  lt_irrefl bid

/-- The maximum bid forces a call; it does not create an artificial dead end. -/
theorem after_maximum_only_call (move : Move) (legal : allowed (some 5) move) : move = .call := by
  cases move with
  | call => rfl
  | bid bid =>
      change 5 < bid.val at legal
      have bound := bid.isLt
      omega

theorem wild_counts_once (face : Face) : matches 2 face = 1 := by
  simp [matches]

theorem truthful_wild_example : truthful (0, 2) 3 := by decide

theorem false_bid_example : ¬ truthful (0, 1) 3 := by decide

theorem chance_not_a_player (prior : FinDist Dice) (i : Player) :
    ¬ (protocol prior).active .initial i := not_false

end GameTheory.ReBeL.Examples.LiarsDice
