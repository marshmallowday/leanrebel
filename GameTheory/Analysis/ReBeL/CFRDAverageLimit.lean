/-
# Fixed-trace convergence of the CFR-D own-reach average

An explicit iteration threshold bounds every later average, with the oracle
and its whole learning trace fixed. Numerical and continuation errors remain
as an error floor. Exact constructed children give convergence in Nash error,
not convergence of the final iterate or to a specified equilibrium profile.
-/

import GameTheory.Analysis.ReBeL.CFRDExactSafety
import GameTheory.Analysis.ReBeL.CFRDInformationDriver

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

/-- A positive finite threshold for an inverse-square-root remainder. -/
def cfrDAverageThreshold (coefficient epsilon : ℝ) : Nat :=
  ⌊(|coefficient| / epsilon) ^ 2⌋₊ + 1

/-- The threshold never introduces an empty average, even for invalid tolerances. -/
theorem cfrDAverageThreshold_pos (coefficient epsilon : ℝ) :
    0 < cfrDAverageThreshold coefficient epsilon := Nat.zero_lt_succ _

/-- Every later count, not merely one chosen count, meets the remainder bound.
An absolute coefficient avoids needing an extra sign premise. -/
theorem cfrDAverageRate_after (coefficient epsilon : ℝ) (positive : 0 < epsilon)
    (t : Nat) (large : cfrDAverageThreshold coefficient epsilon ≤ t) :
    coefficient / Real.sqrt t ≤ epsilon := by
  have ht : 0 < (t : ℝ) := by
    exact_mod_cast (cfrDAverageThreshold_pos coefficient epsilon).trans_le large
  have budget : (|coefficient| / epsilon) ^ 2 ≤ (t : ℝ) := by
    have first : (|coefficient| / epsilon) ^ 2 ≤
        (cfrDAverageThreshold coefficient epsilon : ℝ) := by
      simpa only [cfrDAverageThreshold, Nat.cast_add, Nat.cast_one] using
        (Nat.lt_floor_add_one ((|coefficient| / epsilon) ^ 2)).le
    exact first.trans (by exact_mod_cast large)
  rw [div_pow] at budget
  have square : |coefficient| ^ 2 ≤ (t : ℝ) * epsilon ^ 2 :=
    (div_le_iff₀ (pow_pos positive 2)).mp budget
  have hs : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr ht
  have rootSquare : (epsilon * Real.sqrt t) ^ 2 = (t : ℝ) * epsilon ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ht.le]
    ring
  have linear : |coefficient| ≤ epsilon * Real.sqrt t := by
    have squared : |coefficient| ^ 2 ≤ (epsilon * Real.sqrt t) ^ 2 := by
      rw [rootSquare]
      exact square
    nlinarith [mul_pos positive hs]
  exact (div_le_div_of_nonneg_right (le_abs_self coefficient) hs.le).trans
    ((div_le_iff₀ hs).mpr linear)

section General

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History]
variable [∀ who info, Fintype (M.Choice who info)]
variable [∀ who, DecidableEq (M.InfoState who)]

/-- Fixed numerical and continuation errors are not removed by more iterations. -/
def cfrDDepthAverageErrorFloor (clock : ObservationClock M)
    (fallback : (who : Fin 2) → M.Policy who) (cut remaining : Nat)
    (error loss : ℝ) : ℝ :=
  (cfrDDepthErrorConstant M clock fallback cut remaining 0 +
    cfrDDepthErrorConstant M clock fallback cut remaining 1) * error + 2 * loss

/-- Finite-game coefficient independent of the oracle and completed-round count. -/
def cfrDDepthAverageFiniteFactor (clock : ObservationClock M)
    (fallback : (who : Fin 2) → M.Policy who) (cut remaining : Nat) (bound : ℝ) : ℝ :=
  cfrDDepthFiniteConstant M clock fallback cut remaining bound 0 +
    cfrDDepthFiniteConstant M clock fallback cut remaining bound 1

omit [∀ who, DecidableEq (M.InfoState who)] in
/-- Sum both original regret budgets before comparing them with the threshold. -/
theorem cfrDDepthAverageBudget_after (clock : ObservationClock M)
    (fallback : (who : Fin 2) → M.Policy who) (cut remaining : Nat)
    (bound error loss epsilon : ℝ) (he : 0 ≤ error) (positive : 0 < epsilon)
    (t : Nat) [NeZero t]
    (large : cfrDAverageThreshold
      (cfrDDepthAverageFiniteFactor M clock fallback cut remaining bound) epsilon ≤ t) :
    cfrDDepthMeanBudget M clock fallback cut remaining bound error loss 0 t +
        cfrDDepthMeanBudget M clock fallback cut remaining bound error loss 1 t ≤
      cfrDDepthAverageErrorFloor M clock fallback cut remaining error loss + epsilon := by
  have first := cfrDDepthMeanBudget_le_constants M clock fallback
    cut remaining bound error loss he 0 t
  have second := cfrDDepthMeanBudget_le_constants M clock fallback
    cut remaining bound error loss he 1 t
  have rate := cfrDAverageRate_after
    (cfrDDepthAverageFiniteFactor M clock fallback cut remaining bound) epsilon positive t large
  dsimp only [cfrDDepthAverageErrorFloor, cfrDDepthAverageFiniteFactor] at rate ⊢
  simp only [add_mul, add_div] at rate ⊢
  linarith only [first, second, rate]

/-- One fixed oracle generates every average in this statement. At any later
count the whole profile, against every behavioral deviation, meets the floor
plus epsilon. No monotonicity of the actual exploitability is asserted. -/
theorem cfrDDepthAverage_after (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (oracle : CFRDValueOracle M) (bound error loss epsilon : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 ≤ loss) (positive : 0 < epsilon)
    (bounded : ∀ who h, |payoff who h| ≤ bound)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error)
    (optimal : CFRDDepthLeafOptimal M clock fallback payoff cut remaining oracle loss)
    (t : Nat) [NeZero t]
    (large : cfrDAverageThreshold
      (cfrDDepthAverageFiniteFactor M clock fallback cut remaining bound) epsilon ≤ t) :
    IsNash (M.toBehavioralGameForm (cut + remaining))
      (euPreferenceWithin
        (cfrDDepthAverageErrorFloor M clock fallback cut remaining error loss + epsilon)
        (fun h who => payoff who h))
      (cfrDDepthAveragedProfile M clock fallback payoff cut remaining oracle t) := by
  have finite := cfrDDepthAveragedProfile_isNash M clock hrecall fallback payoff zeroSum
    cut remaining oracle bound error loss hb he hl bounded accurate optimal t
  have budget := cfrDDepthAverageBudget_after M clock fallback cut remaining bound error loss
    epsilon he positive t large
  rw [isNash_iff] at finite ⊢
  intro who replacement
  have gain := finite who replacement
  rw [euPreferenceWithin_apply] at gain ⊢
  exact gain.trans (add_le_add_left budget _)

/-- Epsilon-N convergence to the fixed error floor. Positive counts are indexed
as t+1, covering the same infinite trace without a total empty-average convention. -/
theorem cfrDDepthAverage_approaches (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (oracle : CFRDValueOracle M) (bound error loss : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 ≤ loss)
    (bounded : ∀ who h, |payoff who h| ≤ bound)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error)
    (optimal : CFRDDepthLeafOptimal M clock fallback payoff cut remaining oracle loss) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ threshold : Nat, 0 < threshold ∧
      ∀ t : Nat, threshold ≤ t →
        IsNash (M.toBehavioralGameForm (cut + remaining))
          (euPreferenceWithin
            (cfrDDepthAverageErrorFloor M clock fallback cut remaining error loss + epsilon)
            (fun h who => payoff who h))
          (cfrDDepthAveragedProfile M clock fallback payoff cut remaining oracle (t + 1)) := by
  intro epsilon positive
  refine ⟨cfrDAverageThreshold
    (cfrDDepthAverageFiniteFactor M clock fallback cut remaining bound) epsilon,
    cfrDAverageThreshold_pos _ _, ?_⟩
  intro t large
  exact cfrDDepthAverage_after M clock hrecall fallback payoff zeroSum cut remaining
    oracle bound error loss epsilon hb he hl positive bounded accurate optimal (t + 1)
    (large.trans (Nat.le_succ t))

end General

section Constructed

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]
variable [∀ who, DecidableEq ((fullInformation M).InfoState who)]

/-- Ideal constructed CFR-D converges in Nash error along ONE infinite trace.
Its factual child equilibria and off-path completion are constructed internally;
no supplied child certificate or final-iterate claim appears in the conclusion. -/
theorem cfrDConstructedExactAverage_converges
    (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (bound : ℝ) (hb : 0 ≤ bound) (bounded : ∀ who h, |payoff who h| ≤ bound) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ threshold : Nat, 0 < threshold ∧
      ∀ t : Nat, threshold ≤ t →
        IsNash ((fullInformation M).toBehavioralGameForm (cut + remaining))
          (euPreferenceWithin epsilon (fun h who => payoff who h))
          (cfrDDepthAveragedProfile (fullInformation M) (fullObservationClock M)
            fallback payoff cut remaining
            (cfrDConstructedExactOracle M fallback payoff cut remaining) (t + 1)) := by
  have result := cfrDDepthAverage_approaches (fullInformation M) (fullObservationClock M)
    (fullSignals_perfectRecall M.toInfoSignals) fallback payoff zeroSum cut remaining
    (cfrDConstructedExactOracle M fallback payoff cut remaining) bound 0 0 hb
    (le_refl _) (le_refl _) bounded
    (cfrDConstructedExactOracle_accurate M fallback payoff cut remaining)
    (cfrDConstructedExactOracle_leafOptimal M fallback payoff cut remaining)
  simpa only [cfrDDepthAverageErrorFloor, mul_zero, zero_add] using result

/-- For the implemented finite-child backend, fixed nonzero noise and child
tolerance leave a floor. Increasing the parent count does not replace its oracle
or its actual learning trace and cannot remove that floor. -/
theorem cfrDInformationAverage_after (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (bound error loss epsilon : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error)
    (hl : 0 < loss) (positive : 0 < epsilon)
    (bounded : ∀ who h, |payoff who h| ≤ bound)
    (noise : CFRDPredictionNoise M)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (t : Nat) [NeZero t]
    (large : cfrDAverageThreshold
      (cfrDDepthAverageFiniteFactor (fullInformation M) (fullObservationClock M)
        (cfrDInformationFallback M fallback) cut remaining bound) epsilon ≤ t) :
    IsNash ((fullInformation M).toBehavioralGameForm (cut + remaining))
      (euPreferenceWithin
        (cfrDDepthAverageErrorFloor (fullInformation M) (fullObservationClock M)
          (cfrDInformationFallback M fallback) cut remaining error loss + epsilon)
        (fun h who => payoff who h))
      (cfrDDepthAveragedProfile (fullInformation M) (fullObservationClock M)
        (cfrDInformationFallback M fallback) payoff cut remaining
        (cfrDConstructedInformationOracle M fallback payoff cut remaining bound loss noise) t) :=
  cfrDDepthAverage_after (fullInformation M) (fullObservationClock M)
    (fullSignals_perfectRecall M.toInfoSignals) (cfrDInformationFallback M fallback)
    payoff zeroSum cut remaining
    (cfrDConstructedInformationOracle M fallback payoff cut remaining bound loss noise)
    bound error loss epsilon hb he hl.le positive bounded
    (cfrDConstructedInformationOracle_accurate M fallback payoff cut remaining
      bound loss noise error noiseBound)
    (cfrDConstructedInformationOracle_leafOptimal M fallback payoff zeroSum cut remaining
      bound loss hb hl bounded noise) t large

end Constructed

end GameTheory.ReBeL
