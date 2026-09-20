/-
# Bounded private refresh of a carried continuation

A fresh public resolver is mixed with the currently retained complete profile.
The mixture selects a profile once, not one action at a time. Canonical memory
and belief updates retain that selection. The resulting local replacement
loss follows from bounded utility; no continuation comparison is supplied.
This is a bounded-refresh variant, not a lossless arbitrary Nash replacement.
-/

import GameTheory.Analysis.ReBeL.CFRDRecursivePlay

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*}

/-- After one actual memory step, retaining the new selection for the tail
is exactly one complete continuation under that selection. Bayesian model
updates do not insert the unknown opponent into the selected policy. -/
theorem carriedMemoryStep_selected_expect
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K)
    (state : PrivateIterationState M (CarriedResolveMemory M K))
    (remaining : Nat) (payoff : E.History → ℝ) :
    (carriedMemoryStep M initial unknown who stage state).expect (fun next =>
      (carriedSelectedTail M initial unknown who remaining next).expect payoff) =
    if cfrDCutLive stage.fuel state.history = true then
      (stage.resolver state.iteration (publicTrace M.toInfoSignals state.history.trace)
        state.belief).expect (fun chosen =>
          (M.runBehavioralFrom (Profile.update unknown who (chosen who))
            (stage.fuel + remaining) state.history).expect payoff)
    else
      (carriedSelectedTail M initial unknown who (stage.fuel + remaining) state).expect
        payoff := by
  classical
  by_cases live : cfrDCutLive stage.fuel state.history = true
  · simp only [carriedMemoryStep, carriedResolvedStep, if_pos live,
      FinDist.expect_map, FinDist.expect_bind, carriedSelectedTail,
      storeCarriedDraw, resolvedNextState, carriedMemoryProfile, List.headD_cons]
    apply FinDist.expect_congr
    intro chosen _
    rw [M.runBehavioralFrom_add, FinDist.expect_bind]
  · simp only [carriedMemoryStep, carriedResolvedStep, if_neg live,
      FinDist.expect_map, FinDist.expect_pure, carriedSelectedTail,
      storeCarriedDraw, carriedMemoryProfile, List.headD_cons]
    by_cases zero : stage.fuel = 0
    · simp only [zero, Nat.zero_add]
    · have terminal : E.terminal state.history.state := by
        by_contra notTerminal
        apply live
        simp only [cfrDCutLive, decide_eq_true_eq]
        exact ⟨zero, notTerminal⟩
      rw [M.runBehavioralFrom_of_terminal _ remaining terminal,
        M.runBehavioralFrom_of_terminal _ (stage.fuel + remaining) terminal]

/-- The fresh draw and the retain-old branch share one private mixture.
Neither the actual hidden history nor the unknown opponent is an input. -/
def mixedCarriedResolver (initial : K → Profile M.behavioralSignature)
    (fresh : CarriedPublicResolver M (CarriedResolveMemory M K))
    (rate : ℝ) (nonneg : 0 ≤ rate) (atMostOne : rate ≤ 1) :
    CarriedPublicResolver M (CarriedResolveMemory M K) := fun memory obs belief =>
  FinDist.mix rate nonneg atMostOne (fresh memory obs belief)
    (FinDist.pure (carriedMemoryProfile M initial memory))

/-- A stage uses the canonical resolver execution and stores the private draw. -/
def mixedCarriedStage (initial : K → Profile M.behavioralSignature)
    (fresh : CarriedPublicResolver M (CarriedResolveMemory M K))
    (fuel : Nat) (rate : ℝ) (nonneg : 0 ≤ rate) (atMostOne : rate ≤ 1) :
    CarriedResolveStage M K where
  fuel := fuel
  resolver := mixedCarriedResolver M initial fresh rate nonneg atMostOne

/-- Zero refresh probability retains the exact current complete profile. -/
theorem mixedCarriedResolver_zero (initial : K → Profile M.behavioralSignature)
    (fresh : CarriedPublicResolver M (CarriedResolveMemory M K))
    (memory : CarriedResolveMemory M K) (obs : List M.PublicSignal)
    (belief : Option (PublicBelief M.toInfoSignals obs)) :
    mixedCarriedResolver M initial fresh 0 le_rfl (by norm_num) memory obs belief =
      FinDist.pure (carriedMemoryProfile M initial memory) := by
  exact FinDist.mix_zero _ _

/-- Full refresh is the fresh public resolver, with no claimed zero-loss rule. -/
theorem mixedCarriedResolver_one (initial : K → Profile M.behavioralSignature)
    (fresh : CarriedPublicResolver M (CarriedResolveMemory M K))
    (memory : CarriedResolveMemory M K) (obs : List M.PublicSignal)
    (belief : Option (PublicBelief M.toInfoSignals obs)) :
    mixedCarriedResolver M initial fresh 1 (by norm_num) le_rfl memory obs belief =
      fresh memory obs belief := by
  exact FinDist.mix_one _ _

/-- A bounded refresh loses at most 2*bound*rate at EVERY carried state and
against EVERY fixed unknown opponent. This includes off-model histories and
arbitrary fresh candidate quality. Terminals and zero-fuel stages lose zero. -/
theorem mixedCarriedStage_loss_le (initial : K → Profile M.behavioralSignature)
    (fresh : CarriedPublicResolver M (CarriedResolveMemory M K))
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (fuel remaining : Nat)
    (rate : ℝ) (nonneg : 0 ≤ rate) (atMostOne : rate ≤ 1)
    (payoff : E.History → ℝ) (bound : ℝ) (boundNonneg : 0 ≤ bound)
    (bounded : ∀ history, |payoff history| ≤ bound)
    (state : PrivateIterationState M (CarriedResolveMemory M K)) :
    (carriedSelectedTail M initial unknown who (fuel + remaining) state).expect payoff -
      (carriedMemoryStep M initial unknown who
        (mixedCarriedStage M initial fresh fuel rate nonneg atMostOne) state).expect
        (fun next => (carriedSelectedTail M initial unknown who remaining next).expect payoff) ≤
      2 * bound * rate := by
  rw [carriedMemoryStep_selected_expect]
  by_cases live : cfrDCutLive fuel state.history = true
  · simp only [mixedCarriedStage, if_pos live, mixedCarriedResolver,
      FinDist.expect_mix, FinDist.expect_pure]
    have oldBound := FinDist.abs_expect_le_of_abs_bound
      (carriedSelectedTail M initial unknown who (fuel + remaining) state) payoff
      (fun history _ => bounded history)
    have newBound := FinDist.abs_expect_le_of_abs_bound
      (fresh state.iteration (publicTrace M.toInfoSignals state.history.trace) state.belief)
      (fun chosen => (M.runBehavioralFrom (Profile.update unknown who (chosen who))
        (fuel + remaining) state.history).expect payoff)
      (fun chosen _ => FinDist.abs_expect_le_of_abs_bound _ payoff
        (fun history _ => bounded history))
    simp only [carriedSelectedTail] at oldBound ⊢
    have gap := sub_le_sub (abs_le.mp oldBound).2 (abs_le.mp newBound).1
    have scaled := mul_le_mul_of_nonneg_left gap nonneg
    nlinarith only [scaled]
  · dsimp only [mixedCarriedStage]
    rw [if_neg live, sub_self]
    exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) boundNonneg) nonneg

end GameTheory.ReBeL
