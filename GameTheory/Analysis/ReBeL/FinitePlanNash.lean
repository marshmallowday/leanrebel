/-
# Finite structural regret matching and canonical two-player Nash

The payoff matrix is evaluated from the supplied canonical GameForm, including
its chance law. Only the players' independently averaged plan marginals enter
the returned profile. The correlated time-average law is not played as a shared
seed. The normal-form reference is separate from information-set CFR.
-/

import GameTheory.Analysis.ReBeL.FinitePlanLearning
import GameTheory.Analysis.ZeroSumLearning
import Mathlib.Tactic.FinCases

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Math.Probability

universe us uo
variable (F : GameForm.{0, us, uo} (Fin 2))

/-- Assemble two pure strategies without changing either player's carrier. -/
def finiteGamePurePair (row : F.sig.Strategy 0) (column : F.sig.Strategy 1) : Profile F.sig :=
  Fin.cons row (Fin.cons column fun k : Fin 0 => k.elim0)

/-- Assemble independent laws in the original mixed signature. -/
def finiteGameMixedPair (row : FinDist (F.sig.Strategy 0))
    (column : FinDist (F.sig.Strategy 1)) : Profile F.sig.mixed :=
  Fin.cons row (Fin.cons column fun k : Fin 0 => k.elim0)

/-- The matrix payoff is the canonical expected utility of a pure profile. -/
def finiteGameMatrix (utility : F.sig.Outcome → Fin 2 → ℝ)
    (row : F.sig.Strategy 0) (column : F.sig.Strategy 1) : ℝ :=
  expectedUtility utility 0 (F.play (finiteGamePurePair F row column))

/-- Matrix extraction preserves mixed payoffs, hence all mixed deviations. -/
theorem finiteGameMixedPair_payoff (utility : F.sig.Outcome → Fin 2 → ℝ)
    (row : FinDist (F.sig.Strategy 0)) (column : FinDist (F.sig.Strategy 1)) :
    expectedUtility utility 0 (F.mixed.play (finiteGameMixedPair F row column)) =
      MatrixGame.expectedPayoff (finiteGameMatrix F utility) row column := by
  rw [MatrixGame.expectedPayoff_eq_expect_rows]
  simp_rw [MatrixGame.expectedPayoff_pure_row]
  rw [expectedUtility_bind, ← FinDist.piFin_eq_pi]
  simp only [FinDist.piFin, FinDist.expect_map, FinDist.expect_product, FinDist.expect_pure]
  rfl

/-- Replacing the first mixed coordinate is the original profile update. -/
theorem finiteGameMixedPair_update_zero (row replacement : FinDist (F.sig.Strategy 0))
    (column : FinDist (F.sig.Strategy 1)) :
    Profile.update (finiteGameMixedPair F row column) 0 replacement =
      finiteGameMixedPair F replacement column := by
  funext who
  fin_cases who <;> rfl

/-- Replacing the second mixed coordinate is the original profile update. -/
theorem finiteGameMixedPair_update_one (row : FinDist (F.sig.Strategy 0))
    (column replacement : FinDist (F.sig.Strategy 1)) :
    Profile.update (finiteGameMixedPair F row column) 1 replacement =
      finiteGameMixedPair F row replacement := by
  funext who
  fin_cases who <;> rfl

/-- Canonical matrix approximate Nash transfers to the original stochastic
form. No root-outcome or player-randomization independence is manufactured. -/
theorem finiteGameMatrix_nash_transfer (utility : F.sig.Outcome → Fin 2 → ℝ)
    (zeroSum : IsZeroSum utility) (error : ℝ)
    (row : FinDist (F.sig.Strategy 0)) (column : FinDist (F.sig.Strategy 1))
    (equilibrium : IsεNash (MatrixGame.form (F.sig.Strategy 0) (F.sig.Strategy 1)).mixed
      (MatrixGame.utility (finiteGameMatrix F utility)) error
        (MatrixGame.mixedProfile row column)) :
    IsNash F.mixed (euPreferenceWithin error utility) (finiteGameMixedPair F row column) := by
  rw [isεNash_iff] at equilibrium
  rw [isNash_iff]
  intro who replacement
  rcases (by decide : ∀ player : Fin 2, player = 0 ∨ player = 1) who with rfl | rfl
  · have bound := equilibrium 0 replacement
    rw [MatrixGame.mixedProfile_update_zero, MatrixGame.expectedUtility_zero_mixedProfile,
      MatrixGame.expectedUtility_zero_mixedProfile] at bound
    rw [euPreferenceWithin_apply, finiteGameMixedPair_update_zero,
      finiteGameMixedPair_payoff, finiteGameMixedPair_payoff]
    exact bound
  · have bound := equilibrium 1 replacement
    rw [MatrixGame.mixedProfile_update_one, MatrixGame.expectedUtility_one_mixedProfile,
      MatrixGame.expectedUtility_one_mixedProfile] at bound
    rw [euPreferenceWithin_apply, finiteGameMixedPair_update_one,
      zeroSum.expectedUtility_one, zeroSum.expectedUtility_one,
      finiteGameMixedPair_payoff, finiteGameMixedPair_payoff]
    exact bound

variable [∀ who, Fintype (F.sig.Strategy who)]

/-- Finite row/column carriers are inherited from the original form. -/
local instance finiteGameMatrixFintype (who : Fin 2) :
    Fintype ((MatrixGame.form (F.sig.Strategy 0) (F.sig.Strategy 1)).sig.Strategy who) :=
  Fin.cases (inferInstanceAs (Fintype (F.sig.Strategy 0)))
    (fun tail : Fin 1 => Fin.cases (inferInstanceAs (Fintype (F.sig.Strategy 1)))
      (fun empty : Fin 0 => empty.elim0) tail) who

/-- Explicit game-dependent coefficient for the two players' total error. -/
def finiteGameSolutionCoefficient (bound : ℝ) : ℝ :=
  4 * bound * (Real.sqrt (Fintype.card (F.sig.Strategy 0)) +
    Real.sqrt (Fintype.card (F.sig.Strategy 1)))

/-- Finite iteration error; no error-zero exactness is asserted at finite n. -/
def finiteGameSolutionError (bound : ℝ) (n : ℕ) : ℝ :=
  finiteGameSolutionCoefficient F bound * Real.sqrt n / n

/-- Finite-time normal-form solve: independently average each player's plans
from its actually computed simultaneous regret-matching trajectory. -/
def finiteGameMixedSolution (utility : F.sig.Outcome → Fin 2 → ℝ)
    (fallback : Profile F.sig) (n : ℕ) [NeZero n] : Profile F.sig.mixed :=
  let game := MatrixGame.utilityGame (finiteGameMatrix F utility)
  let seed := finiteGameRegretAverage game (MatrixGame.pureProfile (fallback 0) (fallback 1)) n
  finiteGameMixedPair F (MatrixGame.rowMarginal seed) (MatrixGame.columnMarginal seed)

/-- A derived finite-time Nash guarantee for the structural solver. Bounded
canonical utilities, not supplied equilibrium or regret bounds, are the input. -/
theorem finiteGameMixedSolution_isNash (utility : F.sig.Outcome → Fin 2 → ℝ)
    (zeroSum : IsZeroSum utility) (fallback : Profile F.sig)
    (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ outcome who, |utility outcome who| ≤ bound) (n : ℕ) [NeZero n] :
    IsNash F.mixed (euPreferenceWithin (finiteGameSolutionError F bound n) utility)
      (finiteGameMixedSolution F utility fallback n) := by
  let game := MatrixGame.utilityGame (finiteGameMatrix F utility)
  let initial := MatrixGame.pureProfile (fallback 0) (fallback 1)
  let seed := finiteGameRegretAverage game initial n
  have matrixBound (row : F.sig.Strategy 0) (column : F.sig.Strategy 1) :
      |finiteGameMatrix F utility row column| ≤ bound :=
    FinDist.abs_expect_le_of_abs_bound _ _ (fun outcome _ => bounded outcome 0)
  have boundZero (outcome : F.sig.Strategy 0 × F.sig.Strategy 1) :
      |game.utility outcome 0| ≤ bound := matrixBound outcome.1 outcome.2
  have boundOne (outcome : F.sig.Strategy 0 × F.sig.Strategy 1) :
      |game.utility outcome 1| ≤ bound := by
    simpa only [game, MatrixGame.utilityGame, MatrixGame.utility_one, abs_neg] using
      matrixBound outcome.1 outcome.2
  have result := MatrixGame.marginalProfile_isεNash_of_externalRegret_le
    (finiteGameMatrix F utility) seed
    (finiteGameRegretAverage_bound game initial 0 bound nonneg boundZero n)
    (finiteGameRegretAverage_bound game initial 1 bound nonneg boundOne n)
  have total : finiteGameRegretBound game 0 bound n + finiteGameRegretBound game 1 bound n =
      finiteGameSolutionError F bound n := by
    have cardZero : Fintype.card (game.form.sig.Strategy 0) =
        Fintype.card (F.sig.Strategy 0) := Fintype.card_congr (Equiv.refl _)
    have cardOne : Fintype.card (game.form.sig.Strategy 1) =
        Fintype.card (F.sig.Strategy 1) := Fintype.card_congr (Equiv.refl _)
    simp only [finiteGameRegretBound, finiteGameSolutionError, finiteGameSolutionCoefficient,
      cardZero, cardOne]
    ring
  rw [total] at result
  exact finiteGameMatrix_nash_transfer F utility zeroSum _ _ _ result

end GameTheory.ReBeL
