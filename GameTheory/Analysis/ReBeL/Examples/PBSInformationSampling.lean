/-
# Actual child iteration, carried-state and safety controls

The canonical hidden-type game exercises the new information-set iteration
family, an arbitrary randomized opponent, two live strategic rounds and an
interposed zero-length segment. Terminal and off-model controls preserve the
referee/model distinction. The inherited reset counterexample is retained as
a negative regression test, not claimed to describe these specific CFR iterates.
-/

import GameTheory.Analysis.ReBeL.PBSInformationSecurity
import GameTheory.Analysis.ReBeL.Examples.PBSRootDecode

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

local instance samplingControlHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- The entire original game, before its chance draw, as an actual public belief. -/
def samplingInitialBelief : PublicBelief (model fullPrior).toInfoSignals
    (publicTrace (model fullPrior).toInfoSignals (protocol fullPrior).initHistory.trace) where
  law := FinDist.pure (protocol fullPrior).initHistory
  supported history supported := by
    rw [FinDist.mem_support_pure.mp supported]

/-- A certified terminal PBS is also a legitimate child-solver input. -/
def samplingTerminalBelief : PublicBelief (model fullPrior).toInfoSignals
    (publicTrace (model fullPrior).toInfoSignals (offPathFinish false).trace) where
  law := FinDist.pure (offPathFinish false)
  supported history supported := by
    rw [FinDist.mem_support_pure.mp supported]

/-- Each actual completed iteration has the stated positive uniform mass. -/
theorem samplingControl_uniform_three (iteration : Fin 3) :
    (cfrIterationLaw 3).prob iteration = 1 / 3 := by
  norm_num [cfrIterationLaw, FinDist.prob_ofWeights]

/-- Player one's actual child iterates work against a randomized opposing
player; the opponent is fixed outside the private child index binder. -/
theorem samplingControl_live_randomized_opponent :
    (cfrIterationLaw 3).bind (fun n => finiteBudgetControlBelief.law.bind
      ((model fullPrior).runBehavioralFrom
        (Profile.update (Profile.update carriedBitOpponent 0 freshBitPolicy) 1
          (pbsInformationCFRIterate (reducedModel fullPrior) finiteBudgetControlBelief
            pbsRootControlFallback cfrPayoff 1 n.val 1)) 1)) =
      finiteBudgetControlBelief.law.bind ((model fullPrior).runBehavioralFrom
        (Profile.update (Profile.update carriedBitOpponent 0 freshBitPolicy) 1
          (pbsInformationCFR (reducedModel fullPrior) finiteBudgetControlBelief
            pbsRootControlFallback cfrPayoff 1 3 1)) 1) :=
  pbsInformationCFR_sampling_law (reducedModel fullPrior) finiteBudgetControlBelief
    pbsRootControlFallback cfrPayoff 1 3
    (Profile.update carriedBitOpponent 0 freshBitPolicy) 1 1

/-- A live factual child with zero segments before and after its strategic move. -/
theorem samplingControl_live_segments (t : Nat) [NeZero t] :
    pbsInformationCarriedRun (reducedModel fullPrior) finiteBudgetControlBelief
        pbsRootControlFallback cfrPayoff 1 t carriedBitOpponent 0 [0, 1, 0] =
      finiteBudgetControlBelief.law.bind ((model fullPrior).runBehavioralFrom
        (Profile.update carriedBitOpponent 0
          (pbsInformationCFR (reducedModel fullPrior) finiteBudgetControlBelief
            pbsRootControlFallback cfrPayoff 1 t 0)) 1) := by
  simpa only [List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add] using
    pbsInformationCarriedRun_eq_average (reducedModel fullPrior) finiteBudgetControlBelief
      pbsRootControlFallback cfrPayoff 1 t carriedBitOpponent 0 [0, 1, 0]

/-- Chance and both live strategic rounds use one retained child iteration,
including a zero-length segment between chance and the first strategic move. -/
theorem samplingControl_two_live_rounds (t : Nat) [NeZero t] :
    pbsInformationCarriedRun (reducedModel fullPrior) samplingInitialBelief
        pbsRootControlFallback cfrPayoff 3 t carriedBitOpponent 0 [1, 0, 1, 1] =
      (model fullPrior).runBehavioral
        (Profile.update carriedBitOpponent 0
          (pbsInformationCFR (reducedModel fullPrior) samplingInitialBelief
            pbsRootControlFallback cfrPayoff 3 t 0)) 3 := by
  simpa only [samplingInitialBelief, FinDist.pure_bind, List.sum_cons, List.sum_nil,
    Nat.add_zero, Nat.zero_add] using
    pbsInformationCarriedRun_eq_average (reducedModel fullPrior) samplingInitialBelief
      pbsRootControlFallback cfrPayoff 3 t carriedBitOpponent 0 [1, 0, 1, 1]

/-- With no continuation moves, the full supplied joint posterior is unchanged. -/
theorem samplingControl_zero_continuation (t : Nat) [NeZero t] :
    pbsInformationCarriedRun (reducedModel fullPrior) finiteBudgetControlBelief
      pbsRootControlFallback cfrPayoff 1 t carriedBitOpponent 0 [] =
        finiteBudgetControlBelief.law := by
  rw [pbsInformationCarriedRun_eq_average]
  have stopped (strategy : Profile (model fullPrior).behavioralSignature) :
      (model fullPrior).runBehavioralFrom strategy 0 = FinDist.pure := rfl
  rw [List.sum_nil, stopped, FinDist.bind_pure]

/-- Arbitrary segmentation cannot make the terminal child take a strategic action. -/
theorem samplingControl_terminal (t : Nat) [NeZero t] (segments : List Nat) :
    pbsInformationCarriedRun (reducedModel fullPrior) samplingTerminalBelief
      pbsRootControlFallback cfrPayoff 3 t carriedBitOpponent 0 segments =
        FinDist.pure (offPathFinish false) := by
  rw [pbsInformationCarriedRun_eq_average]
  dsimp only [samplingTerminalBelief]
  rw [FinDist.pure_bind]
  exact runBehavioralFrom_of_terminal (model fullPrior) _ _
    (h := offPathFinish false) (by trivial)

/-- A real off-model referee history at time zero has no invented model PBS. -/
theorem samplingControl_off_model_absent (iteration : Fin 3) :
    (pbsInformationCarriedState (reducedModel fullPrior) samplingInitialBelief
      pbsRootControlFallback cfrPayoff 3 3 0 iteration (offPathFinish false)).belief = none := by
  rw [pbsInformationCarriedState_no_posterior]
  have stopped (strategy : Profile (model fullPrior).behavioralSignature) :
      (model fullPrior).runBehavioralFrom strategy 0 = FinDist.pure := rfl
  rw [stopped, FinDist.bind_pure]
  intro possible
  obtain ⟨history, same, supported⟩ := possible
  have initial : history = (protocol fullPrior).initHistory :=
    FinDist.mem_support_pure.mp supported
  rw [initial] at same
  have lengths := congrArg List.length same
  have incompatible : (1 : Nat) = 4 := lengths
  omega

/-- Even an actual newly learned iterate cannot inspect the opponent's hidden bit. -/
theorem samplingControl_iterate_no_hidden_leak (round : Nat) :
    pbsInformationCFRIterate (reducedModel fullPrior) samplingInitialBelief
        pbsRootControlFallback cfrPayoff 3 round 0
        ((model fullPrior).infoOf 0 (fullDraw (false, false)).trace) =
      pbsInformationCFRIterate (reducedModel fullPrior) samplingInitialBelief
        pbsRootControlFallback cfrPayoff 3 round 0
        ((model fullPrior).infoOf 0 (fullDraw (false, true)).trace) := rfl

/-- Preserve the hostile canonical example rejecting arbitrary fresh per-move
resampling. This is a distinct bit-plan family, not the actual CFR family above. -/
theorem samplingControl_reset_counterexample :
    privateCarriedContinue (model fullPrior) carriedBitLaw carriedBitProfile
        carriedBitOpponent 0 2 1 ≠
      (model fullPrior).runBehavioral (Profile.update carriedBitOpponent 0 freshBitPolicy) 3 :=
  carriedBit_resampling_changes_law

/-- The original reference equilibrium only anchors value. The new sampled
child gets the actual sum-of-CFR-regrets guarantee across both live rounds. -/
theorem samplingControl_security (t : Nat) [NeZero t]
    (reference : Profile (model fullPrior).behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm (model fullPrior) samplingInitialBelief 3)
      (euPreference (fun h who => cfrPayoff who h)) reference) :
    (samplingInitialBelief.law.bind ((model fullPrior).runBehavioralFrom reference 3)).expect
        (cfrPayoff 0) -
      pbsRootCFRBound (reducedModel fullPrior) samplingInitialBelief.law (fun _ => 2) 3 t ≤
      (pbsInformationCarriedRun (reducedModel fullPrior) samplingInitialBelief
        pbsRootControlFallback cfrPayoff 3 t carriedBitOpponent 0 [1, 0, 1, 1]).expect
        (cfrPayoff 0) :=
  pbsInformationCarriedRun_security (reducedModel fullPrior) samplingInitialBelief
    pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior)
    (fun _ => 2) (fun _ => by norm_num) cfrPayoff_abs_le_two 3 t reference equilibrium
    carriedBitOpponent 0 [1, 0, 1, 1] (by decide)

/-- A prescribed positive tolerance is realized by the computed finite count,
not by an assumed accuracy certificate for an arbitrary child solver. -/
theorem samplingControl_budget_security (error : ℝ) (positive : 0 < error)
    (reference : Profile (model fullPrior).behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm (model fullPrior) finiteBudgetControlBelief 1)
      (euPreference (fun h who => cfrPayoff who h)) reference) :
    (finiteBudgetControlBelief.law.bind ((model fullPrior).runBehavioralFrom reference 1)).expect
        (cfrPayoff 1) - error ≤
      (pbsInformationCarriedRun (reducedModel fullPrior) finiteBudgetControlBelief
        pbsRootControlFallback cfrPayoff 1
        (pbsInformationBudgetRounds (reducedModel fullPrior)
          finiteBudgetControlBelief.law (fun _ => 2) 1 error)
        (Profile.update carriedBitOpponent 0 freshBitPolicy) 1 [0, 1, 0]).expect (cfrPayoff 1) :=
  pbsInformationCarriedRun_budget_security (reducedModel fullPrior) finiteBudgetControlBelief
    pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior)
    (fun _ => 2) (fun _ => by norm_num) cfrPayoff_abs_le_two 1 error positive
    reference equilibrium (Profile.update carriedBitOpponent 0 freshBitPolicy)
    1 [0, 1, 0] (by decide)

end GameTheory.ReBeL.Examples.HiddenTypes
