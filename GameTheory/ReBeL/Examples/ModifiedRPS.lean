/-
# The modified rock-paper-scissors game in Figure 1a

Source: ReBeL, published p. 1, Figure 1a. Scissors changes the nonzero
payoff magnitude to two. The existing NFG-to-FOSG and hidden-phase FOSG-to-EFG
compilers connect the simultaneous specification to the depicted sequential
choice without allowing the second chooser to inspect the first choice.
Figure 1b and the search/equilibrium claims remain separate ledger obligations.
-/

import GameTheory.Languages.Bridges.FOSGToEFG
import GameTheory.Languages.Bridges.NFGFOSG
import GameTheory.ReBeL.Information
import GameTheory.Core.ZeroSum
import Mathlib.Tactic.NormNum

noncomputable section

namespace GameTheory.ReBeL.Examples.ModifiedRPS

open GameTheory.Protocol GameTheory.Languages GameTheory.Languages.Bridges
open GameTheory.Math.Probability

/-- The three actions in the original figure, not an abstract payoff index. -/
inductive Move where
  | rock
  | paper
  | scissors
  deriving DecidableEq

instance : Fintype Move where
  elems := {.rock, .paper, .scissors}
  complete move := by cases move <;> simp

/-- The complete nine-entry payoff table, from the first player's perspective. -/
def payoff : Move → Move → ℝ
  | .rock, .rock => 0
  | .rock, .paper => -1
  | .rock, .scissors => 2
  | .paper, .rock => 1
  | .paper, .paper => 0
  | .paper, .scissors => -2
  | .scissors, .rock => -2
  | .scissors, .paper => 2
  | .scissors, .scissors => 0

/-- A utility-free canonical normal form; observations enter through its FOSG compiler. -/
def source : NFG.Game (Fin 2) where
  Action _ := Move
  Outcome := Move × Move
  outcome actions := (actions 0, actions 1)

private instance actionNonempty : ∀ i, Nonempty (source.Action i) := fun _ => ⟨.rock⟩

/-- The second player's payoff is the negative of the displayed first payoff. -/
def utility (outcome : Move × Move) (i : Fin 2) : ℝ :=
  if i = 0 then payoff outcome.1 outcome.2 else -payoff outcome.1 outcome.2

theorem zeroSum : IsZeroSum utility := by
  intro outcome
  simp [Fin.sum_univ_two, utility]

/-- Simultaneous play is interpreted by the existing Protocol compiler. -/
abbrev simultaneous : FOSG.Game (Fin 2) := NFG.OneShotFOSG.game source

/-- The actual local-memory refinement, with no omniscient strategy parameter. -/
abbrev fullModel := fullInformation simultaneous.information

theorem perfectRecall : fullModel.PerfectRecall :=
  fullSignals_perfectRecall simultaneous.information.toInfoSignals

/-- Player zero commits before player one in the hidden-action serialization. -/
def firstThenSecond : FOSGToEFG.ExplicitOrder (Fin 2) where
  slots := 2
  player := Equiv.refl _

/-- A sequential extensive-form game with the first action hidden until the round ends. -/
abbrev sequential : EFG.Game (Fin 2) := FOSGToEFG.toEFG simultaneous firstThenSecond

/-- Every legal sequential behavioral policy projects to simultaneous play with
exactly the same complete source-history law, not merely the same payoff. -/
theorem sequential_exact
    (target : (i : Fin 2) →
      (FOSGToEFG.information simultaneous firstThenSecond).BehavioralPolicy i) :
    FinDist.map (FOSGToEFG.eraseHistory simultaneous firstThenSecond)
        ((FOSGToEFG.information simultaneous firstThenSecond).runBehavioral target 3) =
      simultaneous.information.runBehavioral
        (FOSGToEFG.projectBehavioral simultaneous firstThenSecond target) 1 := by
  simpa [firstThenSecond, FOSGToEFG.roundWidth] using
    FOSGToEFG.map_erase_runBehavioral_eq_source simultaneous firstThenSecond target 1

/-- The actual Protocol evaluation recovers the displayed payoff table. -/
theorem protocol_utility_law (profile : Profile source.signature) :
    ((NFG.OneShotFOSG.toProtocolForm source).play
      (NFG.OneShotFOSG.policyProfile source profile)).map
        (NFG.OneShotFOSG.utilityOfOutcome source utility) =
      (source.toGameForm.play profile).map utility :=
  NFG.OneShotFOSG.toProtocolForm_utilityLaw_policyProfile source utility profile

/-- The probabilities displayed in the figure, with certified normalization. -/
def displayedLaw : FinDist Move :=
  FinDist.mix (2 / 5) (by norm_num) (by norm_num) (FinDist.pure .rock)
    (FinDist.mix (2 / 3) (by norm_num) (by norm_num)
      (FinDist.pure .paper) (FinDist.pure .scissors))

theorem displayed_probabilities :
    displayedLaw.prob .rock = 2 / 5 ∧ displayedLaw.prob .paper = 2 / 5 ∧
      displayedLaw.prob .scissors = 1 / 5 := by
  have hrp : Move.rock ≠ Move.paper := by decide
  have hrs : Move.rock ≠ Move.scissors := by decide
  have hps : Move.paper ≠ Move.scissors := by decide
  norm_num [displayedLaw, FinDist.prob_mix, FinDist.prob_pure_eq_ite,
    hrp, hrs, hps, Ne.symm hrp, Ne.symm hrs, Ne.symm hps]

/-- Every pure first action has value zero against the displayed opponent law. -/
theorem displayed_row_value (row : Move) :
    displayedLaw.expect (fun column => payoff row column) = 0 := by
  cases row <;> norm_num [displayedLaw, FinDist.expect_mix, FinDist.expect_pure, payoff]

/-- The matching column calculation checks the orientation and both payoff signs. -/
theorem displayed_column_value (column : Move) :
    displayedLaw.expect (fun row => payoff row column) = 0 := by
  cases column <;> norm_num [displayedLaw, FinDist.expect_mix, FinDist.expect_pure, payoff]

/-- The variant is not ordinary unit-payoff rock-paper-scissors. -/
theorem scissors_magnitude : payoff .rock .scissors = 2 ∧ payoff .paper .scissors = -2 :=
  ⟨rfl, rfl⟩

end GameTheory.ReBeL.Examples.ModifiedRPS
