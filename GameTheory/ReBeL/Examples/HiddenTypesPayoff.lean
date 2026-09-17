/-
# A downstream payoff test for the hidden-type protocol

The same information-local policy has different values under two joint priors
with identical marginals. The calculation uses the canonical history runner,
behavioral game form, and cumulative reward, not a separately postulated payoff.
-/

import GameTheory.ReBeL.Examples.HiddenTypes
import Mathlib.Tactic.NormNum

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

/-- The unit payoff for winning or losing one stage. -/
def winValue (won : Bool) : ℝ := if won then 1 else -1

/-- Player one receives the negative of player zero's reward. -/
def signed (i : Player) (value : ℝ) : ℝ := if i = 0 then value else -value

/-- The two immediate rewards; the initial chance draw itself pays nothing. -/
def reward (prior : FinDist Types) : StageReward (protocol prior)
  | .first _, joint, i => signed i (winValue (firstResult joint))
  | .second types _, joint, i => signed i (winValue (finalResult types joint))
  | _, _, _ => 0

/-- A proved state simplification of the cumulative reward, not its definition. -/
def potential : State → Player → ℝ
  | .second _ firstWin, i => signed i (winValue firstWin)
  | .finished firstWin finalWin, i => signed i (winValue firstWin + winValue finalWin)
  | _, _ => 0

theorem potential_step (prior : FinDist Types) (event : (protocol prior).StepEvent) (i : Player) :
    potential event.target i = potential event.source i + reward prior event.source event.joint i := by
  rcases event with ⟨source, joint, legal, target, realized⟩
  cases source with
  | initial =>
      change target ∈ (FinDist.map State.first prior).support at realized
      rw [FinDist.support_map] at realized
      obtain ⟨types, _, rfl⟩ := realized
      simp [potential, reward]
  | first types =>
      change target ∈ (FinDist.pure (.second types (firstResult joint))).support at realized
      rw [FinDist.mem_support_pure] at realized
      subst target
      simp [potential, reward]
  | second types firstWin =>
      change target ∈ (FinDist.pure (.finished firstWin (finalResult types joint))).support at realized
      rw [FinDist.mem_support_pure] at realized
      subst target
      by_cases hi : i = 0
      · simp [potential, reward, signed, hi]
      · simp [potential, reward, signed, hi, add_comm]
  | finished firstWin finalWin => exact False.elim (legal.1 trivial)

theorem cumulative_eq (prior : FinDist Types) (history : (protocol prior).History) (i : Player) :
    cumulativeUtility (reward prior) history i = potential history.state i :=
  cumulativeUtility_eq_potential (reward prior) potential (fun _ => rfl)
    (potential_step prior) history i

theorem reward_zeroSum (prior : FinDist Types) (event : (protocol prior).StepEvent) :
    ∑ i, reward prior event.source event.joint i = 0 := by
  cases event.source <;> simp [Fin.sum_univ_two, reward, signed]

theorem cumulative_zeroSum (prior : FinDist Types) :
    IsZeroSum (cumulativeUtility (reward prior)) :=
  cumulativeUtility_zeroSum (reward prior) (reward_zeroSum prior)

/-- A policy plan uses one's own type and the publicly observed first result.
It is only a convenient subfamily of all full-AOH policies. -/
structure Plan where
  /-- The first simultaneous action, depending on one's own type only. -/
  first : Bool → Bool
  /-- The second action, depending on one's own type and the public first result. -/
  second : Bool → Bool → Bool

/-- Legal options selected from the reduced local observation, including no-op phases. -/
def planAction (plan : Plan) (info : View) : Option Bool :=
  match info.1 with
  | .first => some (plan.first info.2)
  | .second firstWin => some (plan.second info.2 firstWin)
  | _ => none

/-- An observation-local policy with its information-local menu certificate. -/
def planPolicy (prior : FinDist Types) (i : Player) (plan : Plan) :
    (reducedModel prior).Policy i :=
  fun info => ⟨planAction plan info, by
    rcases info with ⟨phase, own⟩
    cases phase <;> simp [planAction, menu]⟩

/-- Implement the plan on the actual perfect-recall AOH interface. -/
def fullPlanPolicy (prior : FinDist Types) (i : Player) (plan : Plan) : (model prior).Policy i :=
  liftPolicy (reducedModel prior) i (planPolicy prior i plan)

/-- An analyst's state-indexed characterization of those same local policies. -/
def planChooser (prior : FinDist Types) (plans : Player → Plan) : (protocol prior).Chooser :=
  fun state hterm => ⟨fun i => planAction (plans i) (view i state), hterm, by
    intro i
    cases state <;> simp [planAction, view, protocol, active]⟩

theorem plan_historyChooser (prior : FinDist Types) (plans : Player → Plan) :
    (reducedModel prior).historyChooser (fun i => planPolicy prior i (plans i)) =
      (planChooser prior plans).toHistoryChooser := by
  funext history nonterminal
  apply Subtype.ext
  funext i
  change planAction (plans i) ((signals prior).infoOf i history.trace) =
    planAction (plans i) (view i history.state)
  rw [infoOf_view]

theorem map_state_plan_run (prior : FinDist Types) (plans : Player → Plan) (fuel : Nat) :
    FinDist.map History.state
      ((model prior).run (fun i => fullPlanPolicy prior i (plans i)) fuel) =
        (protocol prior).runFor (planChooser prior plans) fuel .initial := by
  change FinDist.map History.state
    ((fullInformation (reducedModel prior)).run
      (fun i => liftPolicy (reducedModel prior) i (planPolicy prior i (plans i))) fuel) = _
  rw [liftPolicy_run]
  change FinDist.map History.state
    ((protocol prior).runHistoryFor
      ((reducedModel prior).historyChooser (fun i => planPolicy prior i (plans i)))
      fuel (protocol prior).initHistory) = _
  rw [plan_historyChooser]
  exact map_state_runHistoryFor (planChooser prior plans) fuel (protocol prior).initHistory

/-- Both first-stage actions are selected simultaneously from private observations. -/
def firstJoint (plans : Player → Plan) (types : Types) : Joint :=
  fun i => some ((plans i).first (ownType i types))

/-- Neither player sees the other player's current second-stage action. -/
def secondJoint (plans : Player → Plan) (types : Types) (firstWin : Bool) : Joint :=
  fun i => some ((plans i).second (ownType i types) firstWin)

theorem run_second (prior : FinDist Types) (plans : Player → Plan) (types : Types)
    (firstWin : Bool) (fuel : Nat) :
    (protocol prior).runFor (planChooser prior plans) (fuel + 1) (.second types firstWin) =
      FinDist.pure (.finished firstWin (finalResult types (secondJoint plans types firstWin))) := by
  rw [runFor_succ_of_not_terminal _ fuel (by simp [protocol, terminal])]
  change (FinDist.pure (.finished firstWin
    (finalResult types (secondJoint plans types firstWin)))).bind
      (fun state => (protocol prior).runFor (planChooser prior plans) fuel state) = _
  rw [FinDist.pure_bind]
  exact runFor_of_terminal _ fuel (by simp [protocol, terminal])

theorem run_first (prior : FinDist Types) (plans : Player → Plan) (types : Types) :
    (protocol prior).runFor (planChooser prior plans) 2 (.first types) =
      FinDist.pure (.finished (firstResult (firstJoint plans types))
        (finalResult types (secondJoint plans types (firstResult (firstJoint plans types))))) := by
  rw [runFor_succ_of_not_terminal _ 1 (by simp [protocol, terminal])]
  change (FinDist.pure (.second types (firstResult (firstJoint plans types)))).bind
    (fun state => (protocol prior).runFor (planChooser prior plans) 1 state) = _
  rw [FinDist.pure_bind]
  exact run_second prior plans types _ 0

theorem run_initial (prior : FinDist Types) (plans : Player → Plan) :
    (protocol prior).runFor (planChooser prior plans) 3 .initial =
      prior.map (fun types => .finished (firstResult (firstJoint plans types))
        (finalResult types (secondJoint plans types (firstResult (firstJoint plans types))))) := by
  rw [runFor_succ_of_not_terminal _ 2 (by simp [protocol, terminal])]
  change (prior.map State.first).bind
    (fun state => (protocol prior).runFor (planChooser prior plans) 2 state) = _
  rw [FinDist.bind_map, FinDist.map_eq_bind]
  exact FinDist.bind_congr fun types _ => run_first prior plans types

/-- Evaluate through the existing behavioral game form, with point-mass local actions. -/
def rootValue (prior : FinDist Types) (plans : Player → Plan) (i : Player) : ℝ :=
  policyValue (model prior) (reward prior) 3
    (fun j => (fullPlanPolicy prior j (plans j)).toBehavioral) i

theorem rootValue_formula (prior : FinDist Types) (plans : Player → Plan) (i : Player) :
    rootValue prior plans i = prior.expect (fun types =>
      potential (.finished (firstResult (firstJoint plans types))
        (finalResult types (secondJoint plans types (firstResult (firstJoint plans types))))) i) := by
  unfold rootValue policyValue
  rw [InformationModel.toBehavioralGameForm_play_toBehavioral,
    InformationModel.toGameForm_play]
  unfold expectedUtility
  calc
    _ = ((model prior).run (fun j => fullPlanPolicy prior j (plans j)) 3).expect
        (fun history => potential history.state i) := by
      apply FinDist.expect_congr
      intro history _
      exact cumulative_eq prior history i
    _ = (FinDist.map History.state
        ((model prior).run (fun j => fullPlanPolicy prior j (plans j)) 3)).expect
          (fun state => potential state i) :=
      (FinDist.expect_map (fun history : (protocol prior).History => history.state)
        ((model prior).run (fun j => fullPlanPolicy prior j (plans j)) 3)
        (fun state => potential state i)).symm
    _ = _ := by rw [map_state_plan_run, run_initial, FinDist.expect_map]

/-- Correlated hidden types; both one-player marginals are fair. -/
def correlated : FinDist Types :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure (false, false)) (FinDist.pure (true, true))

/-- Anticorrelated hidden types with exactly the same one-player marginals. -/
def anticorrelated : FinDist Types :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure (false, true)) (FinDist.pure (true, false))

theorem same_marginals (i : Player) :
    FinDist.map (ownType i) correlated = FinDist.map (ownType i) anticorrelated := by
  apply FinDist.ext_of_prob
  intro value
  fin_cases i <;> cases value <;>
    norm_num [FinDist.prob_map, correlated, anticorrelated, FinDist.expect_mix,
      FinDist.expect_pure, ownType]

theorem different_joint_laws : correlated ≠ anticorrelated := by
  intro equal
  have mass := congrArg (fun law : FinDist Types => law.prob (false, false)) equal
  norm_num [correlated, anticorrelated, FinDist.prob_mix, FinDist.prob_pure_eq_ite] at mass

/-- Both play false first; player zero then guesses its own type and player one plays true. -/
def correlationPlans (i : Player) : Plan where
  first _ := false
  second own _ := if i = 0 then own else true

theorem correlation_value (prior : FinDist Types) :
    rootValue prior correlationPlans 0 = prior.expect (fun types =>
      1 + winValue (types.1 == types.2)) := by
  rw [rootValue_formula]
  apply FinDist.expect_congr
  intro types _
  simp [potential, signed, firstResult, finalResult, firstJoint, secondJoint,
    action, correlationPlans, ownType, winValue]

theorem correlated_value : rootValue correlated correlationPlans 0 = 2 := by
  rw [correlation_value]
  norm_num [correlated, FinDist.expect_mix, FinDist.expect_pure, winValue]

theorem anticorrelated_value : rootValue anticorrelated correlationPlans 0 = 0 := by
  rw [correlation_value]
  norm_num [anticorrelated, FinDist.expect_mix, FinDist.expect_pure, winValue]

/-- Replacing a joint law by its marginals loses information relevant to actual play. -/
theorem same_marginals_different_payoffs :
    (∀ i, FinDist.map (ownType i) correlated = FinDist.map (ownType i) anticorrelated) ∧
      rootValue correlated correlationPlans 0 ≠ rootValue anticorrelated correlationPlans 0 := by
  refine ⟨same_marginals, ?_⟩
  rw [correlated_value, anticorrelated_value]
  norm_num

end GameTheory.ReBeL.Examples.HiddenTypes
