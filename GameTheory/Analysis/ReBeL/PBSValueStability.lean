/-
# Scalar value stability of two finite solves at the same public belief

The cross-profile argument compares canonical approximate Nash values. The
solver-facing results derive their Nash premises from actual information-set
CFR, including the budgeted noisy depth-limited construction. No small outcome
variation or directed coupling cost is supplied. These are SAME-PBS scalar
statements, not conditional value-vector or native-iteration sampling bounds.
-/

import GameTheory.Analysis.ReBeL.EquilibriumValue
import GameTheory.Analysis.ReBeL.PBSInformationDepthBudget

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

/-- Cross deviations compare two approximate equilibrium values without an
exact equilibrium witness. The two deviation allowances both remain visible. -/
theorem approxNash_value_sub_le (form : GameForm (Fin 2))
    (utility : form.sig.Outcome → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (first second : Profile form.sig) (firstError secondError : ℝ)
    (firstNash : IsNash form (euPreferenceWithin firstError utility) first)
    (secondNash : IsNash form (euPreferenceWithin secondError utility) second) :
    expectedUtility utility 0 (form.play first) -
      expectedUtility utility 0 (form.play second) ≤ firstError + secondError := by
  have cross : Profile.update first 1 (second 1) = Profile.update second 0 (first 0) := by
    funext who
    rcases (by decide : ∀ who : Fin 2, who = 0 ∨ who = 1) who with rfl | rfl
    · rw [Profile.update_of_ne _ _ (by decide), Profile.update_same]
    · rw [Profile.update_same, Profile.update_of_ne _ _ (by decide)]
  have column := (isNash_iff first).mp firstNash 1 (second 1)
  have row := (isNash_iff second).mp secondNash 0 (first 0)
  rw [euPreferenceWithin_apply] at column row
  rw [zeroSum.expectedUtility_one, zeroSum.expectedUtility_one, cross] at column
  linarith only [column, row]

/-- Reversing the same cross-profile comparison bounds the absolute scalar
change. Neither equality of strategies nor convergence of their laws is used. -/
theorem approxNash_value_abs_sub_le (form : GameForm (Fin 2))
    (utility : form.sig.Outcome → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (first second : Profile form.sig) (firstError secondError : ℝ)
    (firstNash : IsNash form (euPreferenceWithin firstError utility) first)
    (secondNash : IsNash form (euPreferenceWithin secondError utility) second) :
    |expectedUtility utility 0 (form.play first) -
      expectedUtility utility 0 (form.play second)| ≤ firstError + secondError := by
  rw [abs_le]
  constructor
  · have reverse := approxNash_value_sub_le form utility zeroSum second first
      secondError firstError secondNash firstNash
    linarith only [reverse]
  · exact approxNash_value_sub_le form utility zeroSum first second
      firstError secondError firstNash secondNash

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {observations : List M.PublicSignal}

/-- Two independently recomputed finite information-set CFR OUTPUTS at the
same joint PBS have a scalar value gap bounded by both finite-time residuals.
The fallbacks and positive iteration counts may differ. Individual iterates
and conditional information fibers are not covered by this statement. -/
theorem pbsInformationCFR_value_abs_sub_le
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (firstFallback secondFallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h))
    (bound : Fin 2 → ℝ) (nonneg : ∀ who, 0 ≤ bound who)
    (bounded : ∀ who h, |payoff who h| ≤ bound who)
    (fuel firstTime secondTime : Nat) [NeZero firstTime] [NeZero secondTime] :
    |(PublicBelief.continuationLaw (fullInformation M)
        (pbsInformationCFR M belief firstFallback payoff fuel firstTime) fuel belief).expect
          (payoff 0) -
      (PublicBelief.continuationLaw (fullInformation M)
        (pbsInformationCFR M belief secondFallback payoff fuel secondTime) fuel belief).expect
          (payoff 0)| ≤
      pbsRootCFRBound M belief.law bound fuel firstTime +
        pbsRootCFRBound M belief.law bound fuel secondTime :=
  approxNash_value_abs_sub_le (behavioralBeliefForm (fullInformation M) belief fuel)
    (fun h who => payoff who h) zeroSum _ _ _ _
    (pbsInformationCFR_isNash M belief firstFallback payoff zeroSum bound nonneg bounded
      fuel firstTime)
    (pbsInformationCFR_isNash M belief secondFallback payoff zeroSum bound nonneg bounded
      fuel secondTime)

/-- Positive requested budgets are met by actual computed finite child solves.
No caller supplies a Nash witness, root value comparison or coupling. -/
theorem pbsInformationBudgetProfile_value_abs_sub_le
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (firstFallback secondFallback : (who : Fin 2) → M.Policy who) (fuel : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ h who, |utility h who| ≤ bound)
    (firstError secondError : ℝ) (firstPositive : 0 < firstError)
    (secondPositive : 0 < secondError) :
    |(PublicBelief.continuationLaw (fullInformation M)
        (pbsInformationBudgetProfile M belief firstFallback fuel utility bound firstError)
        fuel belief).expect (fun h => utility h 0) -
      (PublicBelief.continuationLaw (fullInformation M)
        (pbsInformationBudgetProfile M belief secondFallback fuel utility bound secondError)
        fuel belief).expect (fun h => utility h 0)| ≤ firstError + secondError :=
  approxNash_value_abs_sub_le (behavioralBeliefForm (fullInformation M) belief fuel)
    utility zeroSum _ _ firstError secondError
    (pbsInformationBudgetProfile_isNash M belief firstFallback fuel utility zeroSum
      bound nonneg bounded firstError firstPositive)
    (pbsInformationBudgetProfile_isNash M belief secondFallback fuel utility zeroSum
      bound nonneg bounded secondError secondPositive)

/-- Two actual noisy depth-limited solves at the SAME joint PBS have a small
scalar value-change bound from their allocated numerical, child and finite-T
budgets. Their predictors may differ. Neither a per-history rate nor the
carried-prefix safety conclusion is assumed or concluded here. -/
theorem pbsInformationAllocatedDepthProfile_value_abs_sub_le
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (firstFallback secondFallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (bound firstTolerance secondTolerance : ℝ) (nonneg : 0 ≤ bound)
    (firstPositive : 0 < firstTolerance) (secondPositive : 0 < secondTolerance)
    (bounded : ∀ who h, |payoff who h| ≤ bound)
    (firstNoise secondNoise : PBSRootDepthNoise M belief.law)
    (firstNoiseBound : ∀ n trunk who info, |firstNoise n trunk who info| ≤
      pbsDepthAllocationError
        (pbsRootDepthErrorFactor M belief.law firstFallback cut remaining) firstTolerance)
    (secondNoiseBound : ∀ n trunk who info, |secondNoise n trunk who info| ≤
      pbsDepthAllocationError
        (pbsRootDepthErrorFactor M belief.law secondFallback cut remaining) secondTolerance) :
    |(PublicBelief.continuationLaw (fullInformation M)
        (pbsInformationAllocatedDepthProfile M belief firstFallback payoff cut remaining
          bound firstTolerance firstNoise) (cut + remaining) belief).expect (payoff 0) -
      (PublicBelief.continuationLaw (fullInformation M)
        (pbsInformationAllocatedDepthProfile M belief secondFallback payoff cut remaining
          bound secondTolerance secondNoise) (cut + remaining) belief).expect (payoff 0)| ≤
      firstTolerance + secondTolerance :=
  approxNash_value_abs_sub_le
    (behavioralBeliefForm (fullInformation M) belief (cut + remaining))
    (fun h who => payoff who h) zeroSum _ _ firstTolerance secondTolerance
    (pbsInformationAllocatedDepthProfile_isNash M belief firstFallback payoff zeroSum
      cut remaining bound firstTolerance nonneg firstPositive bounded firstNoise firstNoiseBound)
    (pbsInformationAllocatedDepthProfile_isNash M belief secondFallback payoff zeroSum
      cut remaining bound secondTolerance nonneg secondPositive bounded
      secondNoise secondNoiseBound)

/-- The computed budget is a threshold: every larger iteration count meets
it too. The finite schedule coefficient and error are explicit; no monotone
sequence of policies or convergent individual iterates is assumed. -/
theorem pbsInformationBudgetRounds_error_of_le (roots : FinDist E.History)
    (bound : Fin 2 → ℝ) (fuel t : Nat) (error : ℝ) (positive : 0 < error)
    (large : pbsInformationBudgetRounds M roots bound fuel error ≤ t) :
    pbsRootCFRBound M roots bound fuel t ≤ error := by
  let c := |pbsRootCFRBound M roots bound fuel 1|
  have hc : 0 ≤ c := abs_nonneg _
  have hn : (0 : ℝ) < t := by
    have roundsPositive : 0 < pbsInformationBudgetRounds M roots bound fuel error :=
      Nat.pos_of_ne_zero (NeZero.ne _)
    exact_mod_cast roundsPositive.trans_le large
  have floor : (c / error) ^ 2 < (⌊(c / error) ^ 2⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have budget : (c / error) ^ 2 ≤ (t : ℝ) := by
    calc
      (c / error) ^ 2 ≤ (pbsInformationBudgetRounds M roots bound fuel error : ℝ) := by
        simpa only [pbsInformationBudgetRounds, c, Nat.cast_add, Nat.cast_one] using floor.le
      _ ≤ (t : ℝ) := by exact_mod_cast large
  rw [div_pow] at budget
  have square : c ^ 2 ≤ (t : ℝ) * error ^ 2 :=
    (div_le_iff₀ (pow_pos positive 2)).mp budget
  have multiplied : (c * Real.sqrt t) ^ 2 ≤ (error * t) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hn.le]
    nlinarith [mul_le_mul_of_nonneg_right square hn.le]
  have linear : c * Real.sqrt t ≤ error * t := by
    nlinarith [mul_nonneg hc (Real.sqrt_nonneg (t : ℝ)), mul_pos positive hn]
  rw [pbsInformationCFRBound_factor]
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg (t : ℝ))) hn.le).trans
      ((div_le_iff₀ hn).mpr linear)

/-- An explicit late-iteration scalar rate for the ACTUAL reach-weighted CFR
outputs at one fixed joint PBS. For any positive tolerance, both counts above
the computed half-tolerance budget suffice, even with different fallbacks.
This is not a rate for individual native iterates or conditional value vectors. -/
theorem pbsInformationCFR_late_value_abs_sub_le
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (firstFallback secondFallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h))
    (bound : Fin 2 → ℝ) (nonneg : ∀ who, 0 ≤ bound who)
    (bounded : ∀ who h, |payoff who h| ≤ bound who)
    (fuel firstTime secondTime : Nat) [NeZero firstTime] [NeZero secondTime]
    (tolerance : ℝ) (positive : 0 < tolerance)
    (firstLarge : pbsInformationBudgetRounds M belief.law bound fuel (tolerance / 2) ≤
      firstTime)
    (secondLarge : pbsInformationBudgetRounds M belief.law bound fuel (tolerance / 2) ≤
      secondTime) :
    |(PublicBelief.continuationLaw (fullInformation M)
        (pbsInformationCFR M belief firstFallback payoff fuel firstTime) fuel belief).expect
          (payoff 0) -
      (PublicBelief.continuationLaw (fullInformation M)
        (pbsInformationCFR M belief secondFallback payoff fuel secondTime) fuel belief).expect
          (payoff 0)| ≤ tolerance := by
  have halfPositive : 0 < tolerance / 2 := by linarith
  calc
    _ ≤ pbsRootCFRBound M belief.law bound fuel firstTime +
        pbsRootCFRBound M belief.law bound fuel secondTime :=
      pbsInformationCFR_value_abs_sub_le M belief firstFallback secondFallback payoff
        zeroSum bound nonneg bounded fuel firstTime secondTime
    _ ≤ tolerance / 2 + tolerance / 2 := add_le_add
      (pbsInformationBudgetRounds_error_of_le M belief.law bound fuel firstTime
        (tolerance / 2) halfPositive firstLarge)
      (pbsInformationBudgetRounds_error_of_le M belief.law bound fuel secondTime
        (tolerance / 2) halfPositive secondLarge)
    _ = tolerance := by ring

end GameTheory.ReBeL
