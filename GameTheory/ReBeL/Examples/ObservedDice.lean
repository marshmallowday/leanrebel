/-
# The six-versus-thirty-six example in Section 3

Two players roll one private and one public six-sided die each. Faces are
encoded by Fin 6 (displayed face = index + 1). Thus the paper's actual roll
((3,4),(5,6)) is ((2,3),(4,5)) here. Fibers below contain real Protocol
histories of the chance draw, not a separately postulated tuple universe.
-/

import GameTheory.ReBeL.Adapter
import GameTheory.ReBeL.Knowledge
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum

noncomputable section

namespace GameTheory.ReBeL.Examples.ObservedDice

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

/-- The two observers of the private and public dice. -/
abbrev Player := Fin 2
/-- Six die faces encoded from zero; displayed labels are one greater. -/
abbrev Face := Fin 6
/-- Each player contributes a private/public die pair to the joint roll. -/
abbrev Dice := (Face × Face) × (Face × Face)

/-- All four dice are jointly sampled; every roll is possible. -/
def chanceLaw : FinDist Dice := FinDist.uniformOfFintype

/-- The initial position and the completed chance roll. -/
inductive State where
  | initial
  | rolled (dice : Dice)
  deriving DecidableEq, Fintype

/-- A genuine one-transition chance protocol, with neither player active. -/
@[reducible]
def protocol : ExecutionProtocol Player where
  State := State
  Action _ := Unit
  init := .initial
  active _ _ := False
  available _ _ := Set.univ
  terminal state := match state with | .initial => False | .rolled _ => True
  step state _ := match state with
    | .initial => chanceLaw.map State.rolled
    | .rolled dice => FinDist.pure (.rolled dice)
  progress := by
    intro state nonterminal
    cases state with
    | initial => exact ⟨fun _ => none, fun _ => not_false⟩
    | rolled dice => exact False.elim (nonterminal trivial)

/-- The complete realized history corresponding to one roll. -/
def draw (dice : Dice) : protocol.History :=
  protocol.initHistory.extend (joint := fun _ => none)
    (⟨not_false, fun _ => not_false⟩) (target := .rolled dice)
    (by
      change State.rolled dice ∈ (chanceLaw.map State.rolled).support
      rw [FinDist.support_map]
      exact ⟨dice, FinDist.mem_support_uniformOfFintype dice, rfl⟩)

/-- The one-step draw is tree-shaped, proved from real predecessor events. -/
theorem treeShaped : protocol.IsTreeShaped := by
  apply isTreeShaped_of_predecessor_unique
  · intro source joint legal realized
    cases source with
    | initial =>
        change State.initial ∈ (chanceLaw.map State.rolled).support at realized
        rw [FinDist.support_map] at realized
        obtain ⟨dice, _, equal⟩ := realized
        cases equal
    | rolled dice => exact False.elim (legal.1 trivial)
  · intro target firstSource secondSource firstJoint secondJoint firstLegal secondLegal _ _
    have firstInitial : firstSource = .initial := by
      cases firstSource with
      | initial => rfl
      | rolled dice => exact False.elim (firstLegal.1 trivial)
    have secondInitial : secondSource = .initial := by
      cases secondSource with
      | initial => rfl
      | rolled dice => exact False.elim (secondLegal.1 trivial)
    refine ⟨firstInitial.trans secondInitial.symm, ?_⟩
    exact (protocol.eq_noop_of_legal_of_inactive firstLegal (fun _ => not_false)).trans
      (protocol.eq_noop_of_legal_of_inactive secondLegal (fun _ => not_false)).symm

/-- The initial state has only the empty incoming history. -/
theorem trace_initial (trace : protocol.Trace .initial) : trace = .start :=
  (treeShaped .initial).elim trace .start

/-- No synthetic, duplicated, or longer histories enter the fiber counts. -/
theorem history_cases (history : protocol.History) :
    history = protocol.initHistory ∨ ∃ dice, history = draw dice := by
  rcases history with ⟨state, trace⟩
  cases state with
  | initial =>
      left
      have equal := trace_initial trace
      cases equal
      rfl
  | rolled dice =>
      right
      refine ⟨dice, ?_⟩
      have equal := (treeShaped (.rolled dice)).elim trace (draw dice).trace
      cases equal
      rfl

/-- Termination is a property of the protocol, not an imposed rollout truncation. -/
theorem bounded : protocol.BoundedHorizon 1 := by
  intro state trace enough
  cases trace with
  | start => change 1 ≤ 0 at enough; omega
  | @extend source _ previous joint legal realized =>
      cases source with
      | initial =>
          change _ ∈ (chanceLaw.map State.rolled).support at realized
          rw [FinDist.support_map] at realized
          obtain ⟨dice, _, rfl⟩ := realized
          trivial
      | rolled dice => exact False.elim (legal.1 trivial)

/-- The generic finite-history construction applies to this actual chance game. -/
@[reducible]
def historyFintype : Fintype protocol.History := boundedHistoryFintype 1 bounded

/-- The publicly rolled die of each player, with a distinct initial observation. -/
def publicObservation : State → Option (Face × Face)
  | .initial => none
  | .rolled dice => some (dice.1.2, dice.2.2)

/-- Only one's own hidden die is privately observed. -/
def privateObservation (i : Player) : State → Option Face
  | .initial => none
  | .rolled dice => some (if i = 0 then dice.1.1 else dice.2.1)

/-- Full AOHs are obtained by applying fullSignals to these observation maps. -/
@[reducible]
def signals : InfoSignals protocol where
  PublicSignal := Option (Face × Face)
  PrivateSignal _ := Option Face
  initialPublic := none
  initialPrivate _ := none
  publicSignal event := publicObservation event.target
  privateSignal i event := privateObservation i event.target
  InfoState _ := Unit
  initInfo _ _ _ := ()
  pushInfo _ _ _ _ _ := ()

/-- The paper's public observation (4,6), including the initial observation. -/
def publicObservations : List (Option (Face × Face)) := [some (3, 5), none]

/-- Player two additionally knows its private roll of five. -/
def secondInfo : AOH Unit (Option Face) (Option (Face × Face)) :=
  .step (.initial none none) none (some 4) (some (3, 5))

/-- Projection used for counting, never passed to a player policy. -/
def hiddenParts : State → Face × Face
  | .initial => (0, 0)
  | .rolled dice => (dice.1.1, dice.2.1)

/-- Every compatible public history corresponds to exactly two hidden dice. -/
def publicFiberEquiv : PublicFiber signals publicObservations ≃ (Face × Face) where
  toFun history := hiddenParts history.1.state
  invFun hidden := ⟨draw ((hidden.1, 3), (hidden.2, 5)), rfl⟩
  left_inv history := by
    rcases history with ⟨history, observed⟩
    rcases history_cases history with rfl | ⟨dice, rfl⟩
    · change [none] = [some ((3 : Face), 5), none] at observed
      cases observed
    · rcases dice with ⟨⟨a, b⟩, ⟨c, d⟩⟩
      change [some (b, d), none] = [some ((3 : Face), 5), none] at observed
      have pairEqual := Option.some.inj (List.cons.inj observed).1
      have hb : b = 3 := congrArg Prod.fst pairEqual
      have hd : d = 5 := congrArg Prod.snd pairEqual
      subst b
      subst d
      apply Subtype.ext
      rfl
  right_inv _ := rfl

/-- Fixing player two's private die leaves exactly one unknown die. -/
def secondFiberEquiv : InformationFiber signals 1 secondInfo ≃ Face where
  toFun history := (hiddenParts history.1.state).1
  invFun hidden := ⟨draw ((hidden, 3), (4, 5)), rfl⟩
  left_inv history := by
    rcases history with ⟨history, observed⟩
    rcases history_cases history with rfl | ⟨dice, rfl⟩
    · change AOH.initial (none : Option Face) (none : Option (Face × Face)) =
        AOH.step (.initial none none) (none : Option Unit) (some 4) (some (3, 5)) at observed
      cases observed
    · rcases dice with ⟨⟨a, b⟩, ⟨c, d⟩⟩
      change AOH.step (AOH.initial (none : Option Face) (none : Option (Face × Face)))
          (none : Option Unit) (some c) (some (b, d)) =
        AOH.step (.initial none none) none (some 4) (some (3, 5)) at observed
      have hc := Option.some.inj (AOH.step.inj observed).2.2.1
      have publicEqual := Option.some.inj (AOH.step.inj observed).2.2.2
      have hb : b = 3 := congrArg Prod.fst publicEqual
      have hd : d = 5 := congrArg Prod.snd publicEqual
      subst b
      subst c
      subst d
      apply Subtype.ext
      rfl
  right_inv _ := rfl

instance publicCountFintype : Fintype (PublicFiber signals publicObservations) :=
  Fintype.ofEquiv (Face × Face) publicFiberEquiv.symm

instance secondCountFintype : Fintype (InformationFiber signals 1 secondInfo) :=
  Fintype.ofEquiv Face secondFiberEquiv.symm

/-- The public history has the paper's 36 compatible realized histories. -/
theorem public_card : Fintype.card (PublicFiber signals publicObservations) = 36 := by
  rw [Fintype.card_congr publicFiberEquiv]
  norm_num

/-- The private information state has the paper's six compatible histories. -/
theorem second_card : Fintype.card (InformationFiber signals 1 secondInfo) = 6 := by
  rw [Fintype.card_congr secondFiberEquiv]
  norm_num

/-- The individual information state is not the public state. -/
theorem different_fiber_sizes :
    Fintype.card (InformationFiber signals 1 secondInfo) ≠
      Fintype.card (PublicFiber signals publicObservations) := by
  rw [second_card, public_card]
  decide

/-- Private information in the original example does not identify the history. -/
theorem second_not_perfect :
    ¬ Function.Injective
      (fun history : protocol.History => (fullSignals signals).infoOf 1 history.trace) := by
  intro injective
  have same := injective (show
    (fullSignals signals).infoOf 1 (draw ((0, 3), (4, 5))).trace =
      (fullSignals signals).infoOf 1 (draw ((1, 3), (4, 5))).trace from rfl)
  have impossible : (0 : Face) = 1 :=
    congrArg (fun history : protocol.History => (hiddenParts history.state).1) same
  exact (by decide : (0 : Face) ≠ 1) impossible

/-- A distinct positive control: reveal every die publicly after the same draw.
This is not silently substituted for the original private-observation game. -/
@[reducible]
def revealingSignals : InfoSignals protocol where
  PublicSignal := Option Dice
  PrivateSignal _ := Unit
  initialPublic := none
  initialPrivate _ := ()
  publicSignal event := match event.target with | .initial => none | .rolled dice => some dice
  privateSignal _ _ := ()
  InfoState _ := Unit
  initInfo _ _ _ := ()
  pushInfo _ _ _ _ _ := ()

/-- With fully revealing observations, all players identify the complete history. -/
theorem revealing_injective (i : Player) :
    Function.Injective
      (fun history : protocol.History =>
        (fullSignals revealingSignals).infoOf i history.trace) := by
  intro first second equal
  rcases history_cases first with rfl | ⟨firstDice, rfl⟩ <;>
    rcases history_cases second with rfl | ⟨secondDice, rfl⟩
  · rfl
  · cases equal
  · cases equal
  · change AOH.step (AOH.initial () (none : Option Dice)) (none : Option Unit) ()
        (some firstDice) =
      AOH.step (.initial () none) none () (some secondDice) at equal
    exact congrArg draw (Option.some.inj (AOH.step.inj equal).2.2.2)

/-- The positive control's realized information fibers are truly singletons. -/
theorem revealing_unique (i : Player) (history : protocol.History) :
    ∃! other : protocol.History,
      (fullSignals revealingSignals).infoOf i other.trace =
        (fullSignals revealingSignals).infoOf i history.trace :=
  existsUnique_history_of_injective revealingSignals i (revealing_injective i) history

end GameTheory.ReBeL.Examples.ObservedDice
