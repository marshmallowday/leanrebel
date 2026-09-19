/-
# A source-uniform first-iteration control in modified rock-paper-scissors

The paper's Algorithm 2 samples the current policy before its next update.
With one iteration and no warm start this is independent uniform action play.
The established Figure 1 game has a profitable response to that actual law.
This is separate from the declared pure-fallback CFR-D implementation control.
-/

import GameTheory.ReBeL.Examples.ModifiedRPS
import GameTheory.Analysis.ReBeL.CFRDCarriedPlay
import GameTheory.ReBeL.Adapter

noncomputable section

namespace GameTheory.ReBeL.Examples.ModifiedRPS

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Languages GameTheory.Math.Probability

local instance : Nonempty Move := ⟨Move.rock⟩

local instance (who : Fin 2) : Nonempty (source.Action who) := ⟨Move.rock⟩

/-- A fixed action is lifted to the full information-local policy interface. -/
def uniformControlPolicy (who : Fin 2) (move : Move) : fullModel.Policy who :=
  liftPolicy simultaneous.information who (NFG.OneShotFOSG.Policy.ofAction source move)

/-- Complete action profiles are interpreted by the canonical protocol runner. -/
def uniformControlProfile (actions : Fin 2 → Move) : Profile fullModel.behavioralSignature :=
  fun who => (uniformControlPolicy who (actions who)).toBehavioral

/-- Read the original source payoff from a terminal protocol history. -/
def uniformControlPayoff (who : Fin 2) (history : simultaneous.execution.History) : ℝ :=
  NFG.OneShotFOSG.utilityOfOutcome source utility
    (NFG.OneShotFOSG.outcomeOfState source history.state) who

/-- The full-AOH implementation preserves the original Figure 1 payoff table. -/
theorem uniformControl_pure_value (actions : Fin 2 → Move) (who : Fin 2) :
    (fullModel.runBehavioral (uniformControlProfile actions) 1).expect
      (uniformControlPayoff who) = utility (actions 0, actions 1) who := by
  have same : fullModel.runBehavioral (uniformControlProfile actions) 1 =
      simultaneous.information.run (NFG.OneShotFOSG.policyProfile source actions) 1 := by
    rw [show fullModel.runBehavioral (uniformControlProfile actions) 1 =
        fullModel.run (fun who => uniformControlPolicy who (actions who)) 1 from
      fullModel.runBehavioralFrom_toBehavioral _ _ _]
    exact liftPolicy_run simultaneous.information _ 1
  rw [same]
  have h := congrArg (fun law => law.expect (fun values : Fin 2 → ℝ => values who))
    (protocol_utility_law actions)
  unfold uniformControlPayoff
  simpa only [FinDist.expect_map, NFG.OneShotFOSG.toProtocolForm,
    GameForm.mapOutcome_play, FOSG.Game.toGameForm, InformationModel.toGameForm,
    source, NFG.Game.toGameForm, FinDist.expect_pure, uniformControlPayoff] using h

private theorem move_univ : (Finset.univ : Finset Move) =
    {.rock, .paper, .scissors} := rfl

private theorem move_card : Fintype.card Move = 3 := rfl

/-- Uniform no-warm-start choices, sampled independently between the players. -/
def uniformControlLaw : FinDist Move := FinDist.uniformOfFintype

/-- The actual T=1, pre-update, no-warm-start outcome law in the source game. -/
def uniformFirstIteration : FinDist simultaneous.execution.History :=
  (FinDist.pi (fun _ : Fin 2 => uniformControlLaw)).bind fun actions =>
    fullModel.runBehavioral (uniformControlProfile actions) 1

/-- A legal seed-blind pure rock response against the other player's uniform move. -/
def uniformRockResponse : FinDist simultaneous.execution.History :=
  uniformControlLaw.bind fun column =>
    fullModel.runBehavioral (uniformControlProfile (fun who =>
      if who = 0 then .rock else column)) 1

/-- Full legal behavioral realization of independent uniform initial moves. -/
def uniformFirstProfile : Profile fullModel.behavioralSignature :=
  ownReachAverageProfile fullModel (fun _ => uniformControlLaw)
    (fun move => uniformControlProfile (fun _ => move)) (fun who => uniformControlPolicy who .rock)

/-- The source sampling convention has a canonical behavioral realization. -/
theorem uniformFirstProfile_law :
    fullModel.runBehavioral uniformFirstProfile 1 = uniformFirstIteration := by
  exact ownReachAverage_realizes_privateSeeds fullModel perfectRecall _ _ _ 1

/-- The response above is exactly a legal unilateral behavioral deviation,
not an unrelated alternative outcome law. -/
theorem uniformFirstProfile_rock_deviation :
    fullModel.runBehavioral
      (Profile.update uniformFirstProfile 0 (uniformControlPolicy 0 .rock).toBehavioral) 1 =
      uniformRockResponse := by
  unfold uniformFirstProfile uniformRockResponse
  rw [deviation_against_average fullModel perfectRecall (fun _ => uniformControlLaw)
    (fun move => uniformControlProfile (fun _ => move))
    (fun who => uniformControlPolicy who .rock) 0 1 (by decide)
    (by intro who; fin_cases who <;> simp)]
  apply FinDist.bind_congr
  intro column _
  congr 1
  funext who
  rcases (by decide : ∀ player : Fin 2, player = 0 ∨ player = 1) who with rfl | rfl
  · simp [uniformControlProfile]
  · simp [uniformControlProfile]

/-- The symmetric independent uniform first iterate has value zero. -/
theorem uniformFirstIteration_value :
    uniformFirstIteration.expect (uniformControlPayoff 0) = 0 := by
  rw [uniformFirstIteration, FinDist.expect_bind]
  have equal : (fun actions =>
      (fullModel.runBehavioral (uniformControlProfile actions) 1).expect (uniformControlPayoff 0)) =
      fun actions => utility (actions 0, actions 1) 0 :=
    funext fun actions => uniformControl_pure_value actions 0
  rw [equal, ← FinDist.piFin_eq_pi]
  simp only [FinDist.piFin, FinDist.expect_map, FinDist.expect_product, FinDist.expect_pure]
  have rp : Move.rock ≠ Move.paper := by decide
  have rs : Move.rock ≠ Move.scissors := by decide
  have ps : Move.paper ≠ Move.scissors := by decide
  norm_num [rp, rs, ps, Ne.symm rp, Ne.symm rs, Ne.symm ps, uniformControlLaw,
    FinDist.expect_eq_sum, FinDist.prob_uniformOfFintype,
    move_card, move_univ, utility, payoff, Fin.consEquiv]

/-- Actual first-iterate exploitability is at least one third, despite no
leaf approximations or continuation errors anywhere in this one-shot game. -/
theorem uniformRockResponse_value :
    uniformRockResponse.expect (uniformControlPayoff 0) = 1 / 3 := by
  rw [uniformRockResponse, FinDist.expect_bind]
  have equal : (fun column =>
      (fullModel.runBehavioral (uniformControlProfile (fun who =>
        if who = 0 then .rock else column)) 1).expect (uniformControlPayoff 0)) =
      fun column => payoff .rock column := by
    funext column
    exact uniformControl_pure_value _ 0
  rw [equal]
  have rp : Move.rock ≠ Move.paper := by decide
  have rs : Move.rock ≠ Move.scissors := by decide
  have ps : Move.paper ≠ Move.scissors := by decide
  norm_num [rp, rs, ps, Ne.symm rp, Ne.symm rs, Ne.symm ps, uniformControlLaw,
    FinDist.expect_eq_sum, FinDist.prob_uniformOfFintype,
    move_card, move_univ, utility, payoff]

/-- The printed all-delta bound cannot hold at delta=0, T=1 under the stated
uniform pre-update sampling convention, regardless of either finite constant. -/
theorem printedBound_fails_uniform_first (c₁ c₂ : ℝ) :
    ¬ uniformRockResponse.expect (uniformControlPayoff 0) -
        uniformFirstIteration.expect (uniformControlPayoff 0) ≤
      0 * c₁ + 0 * c₂ / Real.sqrt (1 : ℝ) := by
  rw [uniformRockResponse_value, uniformFirstIteration_value]
  norm_num

/-- The actual independent uniform pre-update profile is not an exact Nash
policy in the canonical game. The profitable response respects full AOH. -/
theorem uniformFirstProfile_not_nash :
    ¬ IsNash (fullModel.toBehavioralGameForm 1)
      (euPreference (fun history who => uniformControlPayoff who history)) uniformFirstProfile := by
  intro h
  have deviation :
      (fullModel.runBehavioral
        (Profile.update uniformFirstProfile 0 (uniformControlPolicy 0 .rock).toBehavioral) 1).expect
        (uniformControlPayoff 0) ≤
      (fullModel.runBehavioral uniformFirstProfile 1).expect (uniformControlPayoff 0) :=
    (isNash_iff (F := fullModel.toBehavioralGameForm 1)
      (weaklyPrefers := euPreference (fun history who => uniformControlPayoff who history)) _).mp
      h 0 (uniformControlPolicy 0 .rock).toBehavioral
  rw [uniformFirstProfile_rock_deviation, uniformFirstProfile_law,
    uniformRockResponse_value, uniformFirstIteration_value] at deviation
  norm_num at deviation

end GameTheory.ReBeL.Examples.ModifiedRPS
