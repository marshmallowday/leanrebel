/-
# Liar's Dice rewards and downstream policy values

One die per player, three faces, highest face wild. The rules allow every legal
raise; bid-then-call is only a policy subfamily, not a truncated game. Winning a
challenge pays +1 and losing pays -1. The full C++ refinement remains in M10.
-/

import GameTheory.ReBeL.Examples.LiarsDiceInformation
import GameTheory.ReBeL.Payoff
import Mathlib.Tactic.NormNum

noncomputable section

namespace GameTheory.ReBeL.Examples.LiarsDice

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

/-- Unit prize for the winner and its negative for the other player. -/
def winnerValue (winner i : Player) : ℝ := if i = winner then 1 else -1

theorem winnerValue_zeroSum (winner : Player) : ∑ i, winnerValue winner i = 0 := by
  fin_cases winner <;> norm_num [Fin.sum_univ_two, winnerValue]

/-- Only a challenge against a previous bid pays an immediate reward. -/
def reward (prior : FinDist Dice) : StageReward (protocol prior)
  | .live dice turn (some previous), joint, i =>
      if selected joint turn = .call then
        winnerValue (if truthful dice previous then other turn else turn) i else 0
  | _, _, _ => 0

/-- Terminal utility, later proved equal to the accumulated stage rewards. -/
def potential : State → Player → ℝ
  | .finished winner, i => winnerValue winner i
  | _, _ => 0

/-- Actual legal transitions, including all raises, telescope the stage reward. -/
theorem potential_step (prior : FinDist Dice) (event : (protocol prior).StepEvent) (i : Player) :
    potential event.target i = potential event.source i + reward prior event.source event.joint i := by
  rcases event with ⟨source, joint, legal, target, realized⟩
  cases source with
  | initial =>
      change target ∈ (prior.map (fun dice => State.live dice 0 none)).support at realized
      rw [FinDist.support_map] at realized
      obtain ⟨dice, _, rfl⟩ := realized
      simp [potential, reward]
  | live dice turn last =>
      change target ∈ (FinDist.pure (advance dice turn last (selected joint turn))).support at realized
      rw [FinDist.mem_support_pure] at realized
      subst target
      have permitted := selected_allowed prior dice turn last joint legal
      cases choice : selected joint turn with
      | bid next =>
          cases last <;> simp [advance, potential, reward, choice]
      | call =>
          rw [choice] at permitted
          cases last with
          | none => exact False.elim permitted
          | some previous => simp [advance, potential, reward, choice]
  | finished winner => exact False.elim (legal.1 trivial)

theorem cumulative_eq (prior : FinDist Dice) (history : (protocol prior).History) (i : Player) :
    cumulativeUtility (reward prior) history i = potential history.state i :=
  cumulativeUtility_eq_potential (reward prior) potential (fun _ => rfl)
    (potential_step prior) history i

theorem reward_zeroSum (prior : FinDist Dice) (event : (protocol prior).StepEvent) :
    ∑ i, reward prior event.source event.joint i = 0 := by
  cases source : event.source with
  | initial => simp [reward, source]
  | live dice turn last =>
      cases last with
      | none => simp [reward, source]
      | some previous =>
          by_cases call : selected event.joint turn = .call
          · simp only [source, reward, if_pos call]
            exact winnerValue_zeroSum _
          · simp [reward, source, call]
  | finished winner => simp [reward, source]

/-- Zero-sum holds for every legal history, not only for the example policy. -/
theorem cumulative_zeroSum (prior : FinDist Dice) :
    IsZeroSum (cumulativeUtility (reward prior)) :=
  cumulativeUtility_zeroSum (reward prior) (reward_zeroSum prior)

/-- A later live state is challenged by the observation-local bid/call policy. -/
theorem run_call (prior : FinDist Dice) (opening : Bid) (dice : Dice)
    (turn : Player) (previous : Bid) (fuel : Nat) :
    (protocol prior).runFor (bidCallChooser prior opening) (fuel + 1)
      (.live dice turn (some previous)) =
        FinDist.pure (.finished (if truthful dice previous then other turn else turn)) := by
  rw [runFor_succ_of_not_terminal _ fuel (by simp [terminal])]
  change (FinDist.pure (advance dice turn (some previous)
    (selected (fun i => bidCallAction opening i (view i (.live dice turn (some previous)))) turn))).bind
      (fun state => (protocol prior).runFor (bidCallChooser prior opening) fuel state) = _
  simp only [selected, bidCallAction, view, phase, if_pos rfl, Option.getD_some, advance]
  rw [FinDist.pure_bind]
  exact runFor_of_terminal _ fuel (by simp [terminal])

/-- The opening is followed by a challenge, through the real protocol runner. -/
theorem run_opening (prior : FinDist Dice) (opening : Bid) (dice : Dice) :
    (protocol prior).runFor (bidCallChooser prior opening) 2 (.live dice 0 none) =
      FinDist.pure (.finished (if truthful dice opening then 0 else 1)) := by
  rw [runFor_succ_of_not_terminal _ 1 (by simp [terminal])]
  change (FinDist.pure (advance dice 0 none
    (selected (fun i => bidCallAction opening i (view i (.live dice 0 none))) 0))).bind
      (fun state => (protocol prior).runFor (bidCallChooser prior opening) 1 state) = _
  simp only [selected, bidCallAction, view, phase, if_pos rfl, Option.getD_some, advance]
  rw [FinDist.pure_bind]
  simpa [other] using run_call prior opening dice (other 0) opening 0

/-- Chance remains a joint dice law; it is not replaced by independent marginals. -/
theorem run_initial (prior : FinDist Dice) (opening : Bid) :
    (protocol prior).runFor (bidCallChooser prior opening) 3 .initial =
      prior.map (fun dice => .finished (if truthful dice opening then 0 else 1)) := by
  rw [runFor_succ_of_not_terminal _ 2 (by simp [terminal])]
  change (prior.map (fun dice => State.live dice 0 none)).bind
    (fun state => (protocol prior).runFor (bidCallChooser prior opening) 2 state) = _
  rw [FinDist.bind_map, FinDist.map_eq_bind]
  exact FinDist.bind_congr fun dice _ => run_opening prior opening dice

/-- Value is evaluated on full-AOH policies in the canonical behavioral game. -/
def rootValue (prior : FinDist Dice) (opening : Bid) (i : Player) : ℝ :=
  policyValue (model prior) (reward prior) 3
    (fun j => (fullBidCallPolicy prior opening j).toBehavioral) i

theorem rootValue_formula (prior : FinDist Dice) (opening : Bid) (i : Player) :
    rootValue prior opening i =
      prior.expect (fun dice => winnerValue (if truthful dice opening then 0 else 1) i) := by
  unfold rootValue policyValue
  rw [InformationModel.toBehavioralGameForm_play_toBehavioral,
    InformationModel.toGameForm_play]
  unfold expectedUtility
  calc
    _ = ((model prior).run (fullBidCallPolicy prior opening) 3).expect
        (fun history => potential history.state i) := by
      apply FinDist.expect_congr
      intro history _
      exact cumulative_eq prior history i
    _ = (FinDist.map History.state
        ((model prior).run (fullBidCallPolicy prior opening) 3)).expect
          (fun state => potential state i) :=
      (FinDist.expect_map (fun history : (protocol prior).History => history.state)
        ((model prior).run (fullBidCallPolicy prior opening) 3)
        (fun state => potential state i)).symm
    _ = _ := by rw [map_state_bidCall_run, run_initial, FinDist.expect_map]; rfl

/-- A hidden chance draw with a truthful two-zero bid in three quarters of its mass. -/
def testPrior : FinDist Dice :=
  FinDist.mix (3 / 4) (by norm_num) (by norm_num)
    (FinDist.pure (0, 2)) (FinDist.pure (0, 1))

/-- A nonzero expected value after chance, an actual bid and an actual challenge. -/
theorem testPrior_value : rootValue testPrior 3 0 = 1 / 2 := by
  rw [rootValue_formula]
  norm_num [testPrior, FinDist.expect_mix, FinDist.expect_pure,
    truthful, quantity, dieMatches, bidFace, winnerValue]

theorem testPrior_opponent_value : rootValue testPrior 3 1 = -(1 / 2) := by
  rw [rootValue_formula]
  norm_num [testPrior, FinDist.expect_mix, FinDist.expect_pure,
    truthful, quantity, dieMatches, bidFace, winnerValue]

/-- The same policy loses against a surely false bid; legality is unchanged. -/
theorem false_bid_loses : rootValue (FinDist.pure (0, 1)) 3 0 = -1 := by
  rw [rootValue_formula]
  norm_num [FinDist.expect_pure, truthful, quantity, dieMatches, bidFace, winnerValue]

end GameTheory.ReBeL.Examples.LiarsDice
