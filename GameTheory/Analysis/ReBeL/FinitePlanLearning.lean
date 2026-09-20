/-
# Finite-plan regret matching for PBS child solves

A finite structural recurrence, not a selection of a Nash witness. Every
player updates from one shared previous-round profile. It reuses the existing
regret matcher, finite-law averaging and canonical external regret. This
normal-form reference solver enumerates complete plans; it is not claimed to
be the paper's information-set CFR implementation or a numeric executable.
-/

import GameTheory.Analysis.ReBeL.PayoffBounds
import GameTheory.Core.Learning

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Math.Probability GameTheory.Analysis.Approachability
open GameTheory.Math.Approachability GameTheory.Math.OrthantProjection

universe uι us uo
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable (G : UtilityGame.{uι, us, uo} ι)
variable [∀ who, Fintype (G.form.sig.Strategy who)]

/-- One average-regret vector for every finite-plan player. -/
abbrev FiniteGameRegretState := ∀ who, EuclideanSpace ℝ (G.form.sig.Strategy who)

/-- A pure plan's actual expected utility against the current opponents. -/
def finiteGameActionValue (who : ι) (action : G.form.sig.Strategy who)
    (profile : Profile G.form.sig.mixed) : ℝ :=
  expectedUtility G.utility who
    (G.form.mixed.play (Profile.update profile who (FinDist.pure action)))

/-- Independent private plan laws with specified zero-regret fallbacks. -/
def finiteGameRegretProfile (fallback : Profile G.form.sig) (state : FiniteGameRegretState G) :
    Profile G.form.sig.mixed := fun who => regretMatchWith (fallback who) (state who)

/-- All tables read the same preceding snapshot. The recursion uses neither
an equilibrium witness nor a supplied regret or continuation certificate. -/
def finiteGameRegretState (fallback : Profile G.form.sig) : ℕ → FiniteGameRegretState G
  | 0 => fun _ => 0
  | n + 1 =>
      let previous := finiteGameRegretState fallback n
      let profile := finiteGameRegretProfile G fallback previous
      fun who => ((n : ℝ) / ((n : ℝ) + 1)) • previous who +
        (1 / ((n : ℝ) + 1)) • regretPayoff (finiteGameActionValue G who) (profile who) profile

/-- The unique trace computed by the finite-plan recurrence. -/
def finiteGameRegretPlay (fallback : Profile G.form.sig) (n : ℕ) :
    Profile G.form.sig.mixed :=
  finiteGameRegretProfile G fallback (finiteGameRegretState G fallback n)

/-- No warm start or extra round is inserted before the first update. -/
theorem finiteGameRegretPlay_zero (fallback : Profile G.form.sig) :
    finiteGameRegretPlay G fallback 0 = G.form.purify fallback := by
  funext who
  exact regretMatchWith_zero (fallback who)

/-- Canonical reactive averaging equals each table on its own coupled trace. -/
theorem finiteGameRegretState_eq_avgVec (fallback : Profile G.form.sig) (who : ι) (n : ℕ) :
    finiteGameRegretState G fallback n who =
      avgVec (regretPayoff (finiteGameActionValue G who)) (regretMatchWith (fallback who))
        (finiteGameRegretPlay G fallback) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [finiteGameRegretState, avgVec, ← ih]
      rfl

/-- Every coordinate is the average of the actual unilateral payoff gains. -/
theorem finiteGameRegretState_coordinate_sum (fallback : Profile G.form.sig)
    (who : ι) (action : G.form.sig.Strategy who) (n : ℕ) :
    (n : ℝ) * (finiteGameRegretState G fallback n who).ofLp action =
      ∑ t ∈ Finset.range n,
        (finiteGameActionValue G who action (finiteGameRegretPlay G fallback t) -
          expectedUtility G.utility who
            (G.form.mixed.play (finiteGameRegretPlay G fallback t))) := by
  have h := congrArg (fun x : EuclideanSpace ℝ (G.form.sig.Strategy who) => x.ofLp action)
    (avgVec_smul_eq_sum (regretPayoff (finiteGameActionValue G who))
      (regretMatchWith (fallback who)) (finiteGameRegretPlay G fallback) n)
  simp only [WithLp.ofLp_smul, WithLp.ofLp_sum, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul, regretPayoff_ofLp] at h
  simp_rw [← finiteGameRegretState_eq_avgVec G fallback who] at h
  have mean (t : ℕ) :
      (regretMatchWith (fallback who) (finiteGameRegretState G fallback t who)).expect
          (fun a => finiteGameActionValue G who a (finiteGameRegretPlay G fallback t)) =
        expectedUtility G.utility who (G.form.mixed.play (finiteGameRegretPlay G fallback t)) :=
    G.expect_expectedUtility_update (finiteGameRegretPlay G fallback t) who
  simp_rw [mean] at h
  exact h

/-- Uniform average over exactly the n completed rounds. -/
def finiteGameRegretAverage (fallback : Profile G.form.sig) (n : ℕ) [NeZero n] :
    FinDist (Profile G.form.sig) :=
  G.form.timeAverage fun t : Fin n => FinDist.pi (finiteGameRegretPlay G fallback t.val)

/-- The canonical external regret of the computed trace equals its table. -/
theorem finiteGameRegretAverage_externalRegret (fallback : Profile G.form.sig)
    (who : ι) (action : G.form.sig.Strategy who) (n : ℕ) [NeZero n] :
    G.externalRegret (finiteGameRegretAverage G fallback n) who action =
      (finiteGameRegretState G fallback n who).ofLp action := by
  rw [finiteGameRegretAverage, G.externalRegret_timeAverage]
  simp_rw [G.externalRegret_pi]
  rw [Fin.sum_univ_eq_sum_range (fun t =>
    finiteGameActionValue G who action (finiteGameRegretPlay G fallback t) -
      expectedUtility G.utility who (G.form.mixed.play (finiteGameRegretPlay G fallback t))) n]
  rw [← finiteGameRegretState_coordinate_sum G fallback who action n]
  have nonzero : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp

/-- Explicit per-player average regret, derived from a payoff bound and the
number of plans. It is not an assumed property of the generated sequence. -/
def finiteGameRegretBound (who : ι) (bound : ℝ) (n : ℕ) : ℝ :=
  2 * (Real.sqrt (Fintype.card (G.form.sig.Strategy who)) * (2 * bound)) * Real.sqrt n / n

/-- Finite-time regret holds for every pure plan against the actual trace. -/
theorem finiteGameRegretAverage_bound (fallback : Profile G.form.sig) (who : ι)
    (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ outcome, |G.utility outcome who| ≤ bound)
    (n : ℕ) [NeZero n] (action : G.form.sig.Strategy who) :
    G.externalRegret (finiteGameRegretAverage G fallback n) who action ≤
      finiteGameRegretBound G who bound n := by
  let x := finiteGameRegretState G fallback n who
  let d := Metric.infDist x nonposOrthant
  let c := Real.sqrt (Fintype.card (G.form.sig.Strategy who)) * (2 * bound)
  have hc : 0 ≤ c := by positivity
  have hd : 0 ≤ d := Metric.infDist_nonneg
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have values (a : G.form.sig.Strategy who) (profile : Profile G.form.sig.mixed) :
      |finiteGameActionValue G who a profile| ≤ bound :=
    FinDist.abs_expect_le_of_abs_bound _ _ (fun outcome _ => bounded outcome)
  have hs : d ^ 2 * (n : ℝ) ≤ (2 * c) ^ 2 := by
    dsimp only [d, x]
    rw [finiteGameRegretState_eq_avgVec G fallback who]
    exact regretMatchWith_sq_infDist_avg_le (fallback who) _ hc
      (regretPayoff_norm_le_of_abs_bound _ nonneg values) _ n
  have hsquared : ((n : ℝ) * d) ^ 2 ≤ (2 * c * Real.sqrt n) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hn.le]
    nlinarith [mul_le_mul_of_nonneg_right hs hn.le]
  have linear : (n : ℝ) * d ≤ 2 * c * Real.sqrt n := by
    have rightNonneg : 0 ≤ 2 * c * Real.sqrt n := by positivity
    nlinarith [mul_nonneg hn.le hd]
  rw [finiteGameRegretAverage_externalRegret]
  apply (le_div_iff₀ hn).mpr
  have coordinate : x.ofLp action ≤ d :=
    (le_max_left _ _).trans (positivePart_le_infDist x action)
  calc
    _ ≤ d * n := mul_le_mul_of_nonneg_right coordinate hn.le
    _ ≤ _ := by simpa only [mul_comm d] using linear

end GameTheory.ReBeL
