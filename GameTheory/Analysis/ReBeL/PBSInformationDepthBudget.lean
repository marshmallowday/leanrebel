/-
# Constructive accuracy budgets for noisy depth-limited PBS solving

The requested accuracy determines an explicit positive finite iteration count.
Numerical error and child loss consume part of that budget before the finite
iteration term is bounded. Positive allocations also give a solver at every
positive target accuracy, including a joint-law mass-scaled conditional target.
The actual depth-limited recurrence is used, not a supplied Nash certificate.
-/

import GameTheory.Analysis.ReBeL.PBSInformationDepthCFR
import GameTheory.Analysis.ReBeL.PBSInformationBudget

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

/-- Bound the inverse-square-root term by a computed nonempty finite budget. -/
private theorem depthBudget_inverseSqrt (coefficient tolerance : ℝ)
    (positive : 0 < tolerance) :
    coefficient / Real.sqrt (⌊(|coefficient| / tolerance) ^ 2⌋₊ + 1 : Nat) ≤ tolerance := by
  let n := ⌊(|coefficient| / tolerance) ^ 2⌋₊ + 1
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_succ _
  have budget : (|coefficient| / tolerance) ^ 2 ≤ (n : ℝ) := by
    simpa only [n, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one ((|coefficient| / tolerance) ^ 2)).le
  rw [div_pow] at budget
  have square : |coefficient| ^ 2 ≤ (n : ℝ) * tolerance ^ 2 :=
    (div_le_iff₀ (pow_pos positive 2)).mp budget
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn
  have rootSquare : (tolerance * Real.sqrt n) ^ 2 = (n : ℝ) * tolerance ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hn.le]
    ring
  have linear : |coefficient| ≤ tolerance * Real.sqrt n := by
    have squared : |coefficient| ^ 2 ≤ (tolerance * Real.sqrt n) ^ 2 := by
      rw [rootSquare]
      exact square
    nlinarith [mul_pos positive hs]
  exact (div_le_div_of_nonneg_right (le_abs_self coefficient) hs.le).trans
    ((div_le_iff₀ hs).mpr linear)

/-- A nonzero numerical allowance controlled by the actual error coefficient. -/
def pbsDepthAllocationError (coefficient tolerance : ℝ) : ℝ :=
  tolerance / (4 * (|coefficient| + 1))

/-- Positive target accuracy leaves a strictly positive numerical allowance. -/
theorem pbsDepthAllocationError_pos (coefficient tolerance : ℝ)
    (positive : 0 < tolerance) : 0 < pbsDepthAllocationError coefficient tolerance := by
  unfold pbsDepthAllocationError
  positivity

/-- Reserve positive child loss and a strictly positive finite-iteration budget.
No assumption on the sign of the computed coefficient is needed for allocation. -/
theorem pbsDepthAllocation_feasible (coefficient tolerance : ℝ)
    (positive : 0 < tolerance) :
    coefficient * pbsDepthAllocationError coefficient tolerance +
      2 * (tolerance / 8) < tolerance := by
  have he := pbsDepthAllocationError_pos coefficient tolerance positive
  have hc : coefficient < |coefficient| + 1 := by linarith [le_abs_self coefficient]
  have multiplied := mul_lt_mul_of_pos_right hc he
  have denominator : |coefficient| + 1 ≠ 0 := ne_of_gt (by positivity)
  have cancelled : (|coefficient| + 1) * pbsDepthAllocationError coefficient tolerance =
      tolerance / 4 := by
    unfold pbsDepthAllocationError
    field_simp [denominator] <;> ring
  rw [cancelled] at multiplied
  linarith

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable (roots : FinDist E.History)

/-- Use the canonical finite rooted-history enumeration. -/
local instance depthBudgetHistoryFintype : Fintype (pbsRootProtocol roots).History :=
  pbsRootHistoryFintype roots

/-- Decidable equality remains confined to this real-valued reference solver. -/
local instance depthBudgetInfoDecidableEq (who : Fin 2) :
    DecidableEq ((pbsRootFullInformation M roots).InfoState who) := Classical.decEq _

/-- The rooted local choices are precisely the inherited finite legal actions. -/
local instance depthBudgetChoiceFintype (who : Fin 2)
    (info : (pbsRootFullInformation M roots).InfoState who) :
    Fintype ((pbsRootFullInformation M roots).Choice who info) := by
  classical
  infer_instance

/-- Sum the two existing error coefficients, retaining the administrative root step. -/
def pbsRootDepthErrorFactor (fallback : Profile M.strategicSignature)
    (cut remaining : Nat) : ℝ :=
  cfrDDepthErrorConstant (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (pbsRootFallback M roots fallback) (cut + 1) remaining 0 +
  cfrDDepthErrorConstant (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (pbsRootFallback M roots fallback) (cut + 1) remaining 1

/-- Sum the existing finite-time coefficients without depending on iteration count. -/
def pbsRootDepthFiniteFactor (fallback : Profile M.strategicSignature)
    (cut remaining : Nat) (bound : ℝ) : ℝ :=
  cfrDDepthFiniteConstant (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (pbsRootFallback M roots fallback) (cut + 1) remaining bound 0 +
  cfrDDepthFiniteConstant (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (pbsRootFallback M roots fallback) (cut + 1) remaining bound 1

/-- The computed rooted regret bound separates all three sources of error. -/
theorem pbsRootDepthBudget_le_factors (fallback : Profile M.strategicSignature)
    (cut remaining : Nat) (bound error loss : ℝ) (he : 0 ≤ error)
    (t : Nat) [NeZero t] :
    pbsRootDepthBudget M roots fallback cut remaining bound error loss t ≤
      pbsRootDepthErrorFactor M roots fallback cut remaining * error +
        pbsRootDepthFiniteFactor M roots fallback cut remaining bound / Real.sqrt t +
        2 * loss := by
  have first := cfrDDepthMeanBudget_le_constants (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (pbsRootFallback M roots fallback) (cut + 1) remaining bound error loss he 0 t
  have second := cfrDDepthMeanBudget_le_constants (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (pbsRootFallback M roots fallback) (cut + 1) remaining bound error loss he 1 t
  unfold pbsRootDepthBudget pbsRootDepthErrorFactor pbsRootDepthFiniteFactor
  linarith

/-- Compute finite parent rounds from the budget remaining AFTER numerical and
child errors. The total definition makes no accuracy claim for an infeasible target. -/
def pbsRootDepthBudgetRounds (fallback : Profile M.strategicSignature)
    (cut remaining : Nat) (bound error loss tolerance : ℝ) : Nat :=
  ⌊(|pbsRootDepthFiniteFactor M roots fallback cut remaining bound| /
    (tolerance - (pbsRootDepthErrorFactor M roots fallback cut remaining * error +
      2 * loss))) ^ 2⌋₊ + 1

/-- Even an infeasible request never creates an empty iteration carrier. -/
instance pbsRootDepthBudgetRounds_neZero (fallback : Profile M.strategicSignature)
    (cut remaining : Nat) (bound error loss tolerance : ℝ) :
    NeZero (pbsRootDepthBudgetRounds M roots fallback cut remaining bound error loss tolerance) :=
  ⟨Nat.succ_ne_zero _⟩

/-- A feasible requested budget bounds the actual finite parent regret expression.
The numerical and child terms cannot be made small merely by increasing iterations. -/
theorem pbsRootDepthBudgetRounds_error (fallback : Profile M.strategicSignature)
    (cut remaining : Nat) (bound error loss tolerance : ℝ) (he : 0 ≤ error)
    (feasible : pbsRootDepthErrorFactor M roots fallback cut remaining * error +
      2 * loss < tolerance) :
    pbsRootDepthBudget M roots fallback cut remaining bound error loss
      (pbsRootDepthBudgetRounds M roots fallback cut remaining bound error loss tolerance) ≤
        tolerance := by
  have finite := depthBudget_inverseSqrt
    (pbsRootDepthFiniteFactor M roots fallback cut remaining bound)
    (tolerance - (pbsRootDepthErrorFactor M roots fallback cut remaining * error + 2 * loss))
    (sub_pos.mpr feasible)
  have total := pbsRootDepthBudget_le_factors M roots fallback cut remaining bound error loss he
    (pbsRootDepthBudgetRounds M roots fallback cut remaining bound error loss tolerance)
  linarith

variable {observations : List M.PublicSignal}

/-- Run the existing noisy depth-limited solver for the computed finite count.
The noise and child accuracy supplied to that recurrence are not overwritten. -/
def pbsInformationDepthBudgetProfile
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound error loss tolerance : ℝ)
    (noise : PBSRootDepthNoise M belief.law) :
    Profile (fullInformation M).behavioralSignature :=
  pbsInformationDepthCFR M belief fallback payoff cut remaining bound loss noise
    (pbsRootDepthBudgetRounds M belief.law fallback cut remaining bound error loss tolerance)

/-- Every unilateral deviation satisfies the requested accuracy in the original
PBS continuation game, derived from the actual finite recurrence and its children. -/
theorem pbsInformationDepthBudgetProfile_isNash
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun history who => payoff who history)) (cut remaining : Nat)
    (bound error loss tolerance : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (feasible : pbsRootDepthErrorFactor M belief.law fallback cut remaining * error +
      2 * loss < tolerance)
    (noise : PBSRootDepthNoise M belief.law)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error) :
    IsNash (behavioralBeliefForm (fullInformation M) belief (cut + remaining))
      (euPreferenceWithin tolerance (fun history who => payoff who history))
      (pbsInformationDepthBudgetProfile M belief fallback payoff cut remaining bound error
        loss tolerance noise) := by
  have equilibrium := pbsInformationDepthCFR_isNash M belief fallback payoff zeroSum
    cut remaining bound error loss hb he hl bounded noise noiseBound
    (pbsRootDepthBudgetRounds M belief.law fallback cut remaining bound error loss tolerance)
  rw [isNash_iff] at equilibrium ⊢
  intro who replacement
  have gain := equilibrium who replacement
  rw [euPreferenceWithin_apply] at gain ⊢
  exact gain.trans (add_le_add (le_refl _)
    (pbsRootDepthBudgetRounds_error M belief.law fallback cut remaining bound error loss
      tolerance he feasible))

/-- Allocate strictly positive numerical and child errors from a requested target.
The finite parent count is then computed, not supplied as an accuracy witness. -/
def pbsInformationAllocatedDepthProfile
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound tolerance : ℝ) (noise : PBSRootDepthNoise M belief.law) :
    Profile (fullInformation M).behavioralSignature :=
  pbsInformationDepthBudgetProfile M belief fallback payoff cut remaining bound
    (pbsDepthAllocationError (pbsRootDepthErrorFactor M belief.law fallback cut remaining)
      tolerance) (tolerance / 8) tolerance noise

/-- Every positive target admits the explicitly budgeted depth solver when its
predictor meets the explicit positive allocation. No equilibrium is an input. -/
theorem pbsInformationAllocatedDepthProfile_isNash
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun history who => payoff who history)) (cut remaining : Nat)
    (bound tolerance : ℝ) (hb : 0 ≤ bound) (positive : 0 < tolerance)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (noise : PBSRootDepthNoise M belief.law)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤
      pbsDepthAllocationError (pbsRootDepthErrorFactor M belief.law fallback cut remaining)
        tolerance) :
    IsNash (behavioralBeliefForm (fullInformation M) belief (cut + remaining))
      (euPreferenceWithin tolerance (fun history who => payoff who history))
      (pbsInformationAllocatedDepthProfile M belief fallback payoff cut remaining bound
        tolerance noise) := by
  apply pbsInformationDepthBudgetProfile_isNash M belief fallback payoff zeroSum
    cut remaining bound _ _ tolerance hb
  · exact (pbsDepthAllocationError_pos _ tolerance positive).le
  · positivity
  · exact bounded
  · exact pbsDepthAllocation_feasible _ tolerance positive
  · exact noiseBound

/-- A depth-limited solve with the actual joint law's mass-proportional budget.
This is a composable child backend; installing arbitrary-depth recursion remains separate. -/
def pbsInformationConditionalDepthProfile
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : PBSRootDepthNoise M belief.law) :
    Profile (fullInformation M).behavioralSignature :=
  pbsInformationAllocatedDepthProfile M belief fallback payoff cut remaining bound
    (belief.law.positiveMassFloor * loss) noise

/-- The conditional budget uses the derived mass floor, not an externally
asserted minimum probability and not a Nash certificate passed to the solver. -/
theorem pbsInformationConditionalDepthProfile_isNash
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun history who => payoff who history)) (cut remaining : Nat)
    (bound loss : ℝ) (hb : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (noise : PBSRootDepthNoise M belief.law)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤
      pbsDepthAllocationError (pbsRootDepthErrorFactor M belief.law fallback cut remaining)
        (belief.law.positiveMassFloor * loss)) :
    IsNash (behavioralBeliefForm (fullInformation M) belief (cut + remaining))
      (euPreferenceWithin (belief.law.positiveMassFloor * loss)
        (fun history who => payoff who history))
      (pbsInformationConditionalDepthProfile M belief fallback payoff cut remaining bound
        loss noise) :=
  pbsInformationAllocatedDepthProfile_isNash M belief fallback payoff zeroSum cut remaining
    bound _ hb (mul_pos (FinDist.positiveMassFloor_pos belief.law) positive) bounded
    noise noiseBound

end GameTheory.ReBeL
