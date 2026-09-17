/-
# Hostile histories for the two-stage hidden-type game

These are actual legal Protocol histories, not arbitrary pairs of observations.
They test information leakage, state merging, and zero-probability decisions.
The reference prior has full support; zero reach below comes from a policy,
not from deleting a possible chance outcome.
-/

import GameTheory.ReBeL.Examples.HiddenTypesPayoff

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

/-- Independent fair private bits, used to witness every legal hidden-type history. -/
def fullPrior : FinDist Types := FinDist.uniformOfFintype

/-- A legal chance draw, with no action supplied by either strategic player. -/
def drawHistory (prior : FinDist Types) (types : Types) (possible : types ∈ prior.support) :
    (protocol prior).History :=
  (protocol prior).initHistory.extend
    (joint := fun _ => none)
    (show (protocol prior).Legal .initial (fun _ => none) from
      ⟨by simp [terminal], by intro i; change ¬ False; exact not_false⟩)
    (target := .first types)
    (by
      change State.first types ∈ (FinDist.map State.first prior).support
      rw [FinDist.support_map]
      exact ⟨types, possible, rfl⟩)

/-- Both private types have been drawn, with their actual support witnesses. -/
def fullDraw (types : Types) : (protocol fullPrior).History :=
  drawHistory fullPrior types (FinDist.mem_support_uniformOfFintype types)

/-- Extend the draw by simultaneous choices. Neither choice is observed in advance. -/
def firstHistory (types : Types) (choices : Player → Bool) :
    (protocol fullPrior).History :=
  (fullDraw types).extend
    (joint := fun i => some (choices i))
    (show (protocol fullPrior).Legal (.first types) (fun i => some (choices i)) from
      ⟨by simp [terminal], by intro i; trivial⟩)
    (target := .second types (firstResult (fun i => some (choices i))))
    (by exact FinDist.mem_support_pure.mpr rfl)

/-- Exact full local history after the chance event, including initial observations. -/
theorem fullDraw_info (types : Types) (i : Player) :
    (model fullPrior).infoOf i (fullDraw types).trace =
      AOH.step (AOH.initial none Phase.initial) none (some (ownType i types)) Phase.first := rfl

/-- Exact full local history after the first simultaneous round. -/
theorem firstHistory_info (types : Types) (choices : Player → Bool) (i : Player) :
    (model fullPrior).infoOf i (firstHistory types choices).trace =
      AOH.step ((model fullPrior).infoOf i (fullDraw types).trace)
        (some (choices i)) none (.second (firstResult (fun j => some (choices j)))) := rfl

/-- Player zero cannot learn player one's bit from the draw. -/
theorem hidden_draw_indistinguishable :
    (model fullPrior).infoOf 0 (fullDraw (false, false)).trace =
      (model fullPrior).infoOf 0 (fullDraw (false, true)).trace := rfl

/-- The owner of the differing private bit can distinguish those same histories. -/
theorem hidden_draw_distinguishable :
    (model fullPrior).infoOf 1 (fullDraw (false, false)).trace ≠
      (model fullPrior).infoOf 1 (fullDraw (false, true)).trace := by
  intro equal
  rw [fullDraw_info, fullDraw_info] at equal
  cases equal

/-- The same public trace contains distinct physical states and private information. -/
theorem hidden_draw_same_public :
    publicTrace (signals fullPrior) (fullDraw (false, false)).trace =
      publicTrace (signals fullPrior) (fullDraw (false, true)).trace := rfl

/-- Locality holds for every legal policy, not merely for the convenient Plan subfamily. -/
theorem no_hidden_state_policy (policy : (model fullPrior).Policy 0) :
    policy.act ((model fullPrior).infoOf 0 (fullDraw (false, false)).trace) =
      policy.act ((model fullPrior).infoOf 0 (fullDraw (false, true)).trace) :=
  policy.act_eq_of_infoOf_eq _ _ hidden_draw_indistinguishable

/-- An omniscient policy that reads the opponent's bit cannot inhabit the local interface. -/
theorem no_omniscient_guess :
    ¬ ∃ policy : (model fullPrior).Policy 0,
      policy.act ((model fullPrior).infoOf 0 (fullDraw (false, false)).trace) = some false ∧
      policy.act ((model fullPrior).infoOf 0 (fullDraw (false, true)).trace) = some true := by
  rintro ⟨policy, first, second⟩
  have equal := no_hidden_state_policy policy
  rw [first, second] at equal
  cases equal

/-- Two first-round histories with different actions but the same round result. -/
def mergingHistory (choice : Bool) : (protocol fullPrior).History :=
  firstHistory (false, false) (fun _ => choice)

theorem merging_same_state :
    (mergingHistory false).state = (mergingHistory true).state := rfl

theorem merging_same_public :
    publicTrace (signals fullPrior) (mergingHistory false).trace =
      publicTrace (signals fullPrior) (mergingHistory true).trace := rfl

theorem merging_same_reduced_view :
    (signals fullPrior).infoOf 0 (mergingHistory false).trace =
      (signals fullPrior).infoOf 0 (mergingHistory true).trace := rfl

/-- Full AOH remembers one's own earlier action even after a physical state merge. -/
theorem merging_different_information :
    (model fullPrior).infoOf 0 (mergingHistory false).trace ≠
      (model fullPrior).infoOf 0 (mergingHistory true).trace := by
  intro equal
  change AOH.step _ (some false) (none : Option Bool) (Phase.second true) =
    AOH.step _ (some true) (none : Option Bool) (Phase.second true) at equal
  cases equal

theorem merging_different_histories : mergingHistory false ≠ mergingHistory true := by
  intro equal
  exact merging_different_information
    (congrArg (fun history => (model fullPrior).infoOf 0 history.trace) equal)

/-- Both players choose false in round one. Their second-stage choices remain local. -/
def baselinePlans (i : Player) : Plan := correlationPlans i

/-- The canonical state law after chance and the first simultaneous round. -/
theorem baseline_after_two :
    FinDist.map History.state
      ((model fullPrior).run (fun i => fullPlanPolicy fullPrior i (baselinePlans i)) 2) =
        fullPrior.map (fun types => State.second types true) := by
  rw [map_state_plan_run]
  rw [runFor_succ_of_not_terminal _ 1 (by simp [terminal])]
  change (fullPrior.map State.first).bind
    (fun state => (protocol fullPrior).runFor (planChooser fullPrior baselinePlans) 1 state) = _
  rw [FinDist.bind_map, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro types _
  rw [runFor_succ_of_not_terminal _ 0 (by simp [terminal])]
  change (FinDist.pure (State.second types true)).bind
    (fun state => FinDist.pure state) = _
  exact FinDist.bind_pure _

/-- A possible legal first-round disagreement; the baseline policy never chooses it. -/
def offPathHistory : (protocol fullPrior).History :=
  firstHistory (false, false) (fun i => i != 0)

theorem offPath_state : offPathHistory.state = .second (false, false) false := rfl

theorem offPath_nonterminal : ¬ (protocol fullPrior).terminal offPathHistory.state := by
  change ¬ terminal (.second (false, false) false)
  simp [terminal]

/-- The off-path decision has exactly zero probability under the baseline policy. -/
theorem offPath_zero_reach :
    ((model fullPrior).run (fun i => fullPlanPolicy fullPrior i (baselinePlans i)) 2).prob
      offPathHistory = 0 := by
  apply FinDist.prob_eq_zero_iff.mpr
  intro reachable
  have mapped : offPathHistory.state ∈ (FinDist.map History.state
      ((model fullPrior).run
        (fun i => fullPlanPolicy fullPrior i (baselinePlans i)) 2)).support := by
    rw [FinDist.support_map]
    exact ⟨offPathHistory, reachable, rfl⟩
  rw [baseline_after_two, FinDist.support_map] at mapped
  obtain ⟨types, _, equal⟩ := mapped
  change State.second types true = State.second (false, false) false at equal
  cases equal

/-- Zero reach does not erase the later legal choice or its accumulated history. -/
theorem offPath_two_legal_options :
    LegalOption (protocol fullPrior) offPathHistory.state 0 (some false) ∧
      LegalOption (protocol fullPrior) offPathHistory.state 0 (some true) := by
  constructor <;> trivial

/-- A genuine terminal extension of the zero-reach history. -/
def offPathFinish (guess : Bool) : (protocol fullPrior).History :=
  offPathHistory.extend
    (joint := fun i => some (if i = 0 then guess else true))
    (⟨offPath_nonterminal, by intro i; trivial⟩)
    (target := .finished false
      (finalResult (false, false) (fun i => some (if i = 0 then guess else true))))
    (by exact FinDist.mem_support_pure.mpr rfl)

/-- Past loss is excluded from the continuation reward; the next decision still matters. -/
theorem offPath_future_rewards :
    futureUtility (reward fullPrior) offPathHistory (offPathFinish false) 0 = 1 ∧
      futureUtility (reward fullPrior) offPathHistory (offPathFinish true) 0 = -1 := by
  constructor <;> unfold futureUtility <;> rw [cumulative_eq, cumulative_eq] <;>
    norm_num [offPathFinish, offPathHistory, firstHistory, fullDraw, drawHistory,
      History.extend, potential, signed, firstResult, finalResult, action, winValue]

end GameTheory.ReBeL.Examples.HiddenTypes
