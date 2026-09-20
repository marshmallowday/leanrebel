/-
# Carried-PBS refresh controls and a nonzero replacement-loss regression

The same canonical memory-step execution used in the recursive guarantee
exhibits a strictly positive loss under an unsuitable refresh. Fresh finite
candidates are also checked at a genuine live PBS, while missing beliefs and
zero-fuel stages retain their explicit no-fabrication and no-query behavior.
-/

import GameTheory.Analysis.ReBeL.CFRDFiniteRefreshSafety
import GameTheory.Analysis.ReBeL.Examples.PBSFinitePlanSolver
import GameTheory.Analysis.ReBeL.Examples.CFRDResolveNegative

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- The live game retains its finite canonical history enumeration. -/
local instance refreshHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Explicit finite legal menus for actual finite-plan PBS queries. -/
local instance refreshChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- The old selected continuation in the mixture regression is actual CFR-D. -/
def refreshControlPlays : Unit → Profile (model fullPrior).behavioralSignature :=
  liveResolvePlays (fun _ => 0)

/-- A legal live referee state with no invented model posterior. -/
def refreshControlState :
    PrivateIterationState (model fullPrior) (CarriedResolveMemory (model fullPrior) Unit) where
  iteration := ((), [])
  history := decode (.second false false false false)
  belief := none

/-- In the actual stored-profile execution the bad refresh loses exactly its
mixing weight, rather than having zero loss just because its policy is legal. -/
theorem refreshControl_loss (rate : ℝ) (nonneg : 0 ≤ rate) (atMostOne : rate ≤ 1) :
    (carriedSelectedTail (model fullPrior) refreshControlPlays (carriedBitProfile false) 0
        1 refreshControlState).expect (cfrPayoff 0) -
      (carriedMemoryStep (model fullPrior) refreshControlPlays (carriedBitProfile false) 0
        (mixedCarriedStage (model fullPrior) refreshControlPlays
          (wrongPublicResolver (CarriedResolveMemory (model fullPrior) Unit))
          1 rate nonneg atMostOne) refreshControlState).expect
        (fun next => (carriedSelectedTail (model fullPrior) refreshControlPlays
          (carriedBitProfile false) 0 0 next).expect (cfrPayoff 0)) = rate := by
  have live : cfrDCutLive 1 (decode (.second false false false false)) = true := by
    simp only [cfrDCutLive, decide_eq_true_eq]
    exact ⟨by decide, fun impossible => impossible⟩
  rw [carriedMemoryStep_selected_expect]
  simp only [mixedCarriedStage, refreshControlState, live, if_true, Nat.add_zero,
    mixedCarriedResolver, wrongPublicResolver, FinDist.expect_mix, FinDist.expect_pure,
    carriedSelectedTail, carriedMemoryProfile, List.headD_nil, refreshControlPlays,
    liveResolvePlays, Profile.update_eq_self]
  rw [wrongResolver_before, wrongResolver_after]
  ring

/-- The extra replacement term cannot simply be erased for positive refresh. -/
theorem refreshControl_not_lossless :
    0 < (carriedSelectedTail (model fullPrior) refreshControlPlays (carriedBitProfile false) 0
        1 refreshControlState).expect (cfrPayoff 0) -
      (carriedMemoryStep (model fullPrior) refreshControlPlays (carriedBitProfile false) 0
        (mixedCarriedStage (model fullPrior) refreshControlPlays
          (wrongPublicResolver (CarriedResolveMemory (model fullPrior) Unit))
          1 (1 / 4) (by norm_num) (by norm_num)) refreshControlState).expect
        (fun next => (carriedSelectedTail (model fullPrior) refreshControlPlays
          (carriedBitProfile false) 0 0 next).expect (cfrPayoff 0)) := by
  rw [refreshControl_loss]
  norm_num

/-- A finite solver without a carried posterior retains the CURRENT memory
profile even after earlier refreshes, not the original iteration's profile. -/
theorem finiteRefresh_missing_retains (memory : CarriedResolveMemory (model fullPrior) Unit)
    (obs : List Phase) (rate : ℝ) (nonneg : 0 ≤ rate) (atMostOne : rate ≤ 1) :
    mixedCarriedResolver (model fullPrior) refreshControlPlays
        (finiteRefreshCandidate (model fullPrior) refreshControlPlays decisionClock cfrFallback
          1 (fun h who => cfrPayoff who h) 2 (1 / 4))
        rate nonneg atMostOne memory obs none =
      FinDist.pure (carriedMemoryProfile (model fullPrior) refreshControlPlays memory) := by
  simp only [mixedCarriedResolver, finiteRefreshCandidate_none, FinDist.mix_self]

/-- A genuinely live carried PBS invokes the finite recurrence with its actual
joint posterior. This candidate is not an exact Nash witness chosen by existence. -/
theorem finiteRefresh_live_candidate
    (memory : CarriedResolveMemory (model fullPrior) Unit)
    (chosen : Profile (model fullPrior).behavioralSignature)
    (sampled : chosen ∈ (finiteRefreshCandidate (model fullPrior) refreshControlPlays
      decisionClock cfrFallback 1 (fun h who => cfrPayoff who h) 2 (1 / 4)
      memory _ (some finiteBudgetControlBelief)).support) :
    IsNash (behavioralBeliefForm (model fullPrior) finiteBudgetControlBelief 1)
      (euPreferenceWithin (finiteBudgetControlBelief.law.positiveMassFloor * (1 / 4))
        (fun h who => cfrPayoff who h)) chosen :=
  finiteRefreshCandidate_isNash (model fullPrior) (perfectRecall fullPrior) refreshControlPlays
    decisionClock cfrFallback 1 (fun h who => cfrPayoff who h) (cumulative_zeroSum fullPrior)
    2 (1 / 4) (by norm_num) (by norm_num)
    (fun h who => cfrPayoff_abs_le_two who h) memory _ finiteBudgetControlBelief chosen sampled

/-- A stopped zero-fuel stage ignores even a deliberately bad public resolver. -/
theorem refreshControl_zero_fuel (rate : ℝ) (nonneg : 0 ≤ rate) (atMostOne : rate ≤ 1) :
    (carriedMemoryStep (model fullPrior) refreshControlPlays (carriedBitProfile false) 0
      (mixedCarriedStage (model fullPrior) refreshControlPlays
        (wrongPublicResolver (CarriedResolveMemory (model fullPrior) Unit))
        0 rate nonneg atMostOne) refreshControlState).expect
      (fun next => (carriedSelectedTail (model fullPrior) refreshControlPlays
        (carriedBitProfile false) 0 1 next).expect (cfrPayoff 0)) =
    (carriedSelectedTail (model fullPrior) refreshControlPlays (carriedBitProfile false) 0
      1 refreshControlState).expect (cfrPayoff 0) := by
  rw [carriedMemoryStep_selected_expect]
  simp only [mixedCarriedStage, cfrDCutLive_zero, Bool.false_eq_true, if_false, Nat.zero_add]

/-- The two refresh stages consume the same three-transition game horizon. -/
theorem finiteRefresh_two_stage_fuel :
    carriedResolveFuel (model fullPrior) 1
      (finiteRefreshStages (model fullPrior) refreshControlPlays decisionClock cfrFallback
        (fun h who => cfrPayoff who h) 2 (1 / 4) (1 / 100)
        (by norm_num) (by norm_num) 1 [1, 1]) = 3 := by
  rw [finiteRefreshStages_fuel]
  norm_num

/-- All reached-state comparison premises for a two-stage execution are
derived, including arbitrary unknown opponents and arbitrary carried beliefs. -/
theorem finiteRefresh_two_stage_bounds
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (states : FinDist (PrivateIterationState (model fullPrior)
      (CarriedResolveMemory (model fullPrior) Unit))) :
    CarriedResolveStepBounds (model fullPrior) refreshControlPlays unknown who 1
      (cfrPayoff who) (fun _ => 2 * (2 : ℝ) * (1 / 100))
      (finiteRefreshStages (model fullPrior) refreshControlPlays decisionClock cfrFallback
        (fun h player => cfrPayoff player h) 2 (1 / 4) (1 / 100)
        (by norm_num) (by norm_num) 1 [1, 1]) states :=
  finiteRefreshStages_stepBounds (model fullPrior) refreshControlPlays decisionClock cfrFallback
    (fun h player => cfrPayoff player h) 2 (1 / 4) (1 / 100)
    (by norm_num) (by norm_num) 1 [1, 1] unknown who (by norm_num)
    (cfrPayoff_abs_le_two who) states

end GameTheory.ReBeL.Examples.HiddenTypes
