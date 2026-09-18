/-
# From actual two-player regret to canonical Nash

This bridge preserves all behavioral deviations through own-reach averaging.
The intermediate theorem explicitly takes regret bounds; the concrete CFR
corollary supplies them from the constructed simultaneous full-game trace.
No parallel equilibrium predicate or assumed averaging identity is introduced.
-/

import GameTheory.Analysis.ReBeL.UnilateralAverage
import GameTheory.Analysis.ReBeL.RootRegretBounds
import GameTheory.Core.ZeroSum
import Mathlib.Tactic.FinCases

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*} [Fintype K]

/-- Any two-player zero-sum sequence with uniform unilateral regret bounds
has a reach-weighted behavioral average satisfying the canonical Nash predicate
with the sum of the two error allowances. Averaging preservation is proved,
not assumed, and deviations are arbitrary complete behavioral policies. -/
theorem ownReachAverage_isNash_of_regret (hrecall : M.PerfectRecall)
    (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (fallback : (who : Fin 2) → M.Policy who) (horizon : ℕ)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history)) (error : Fin 2 → ℝ)
    (hregret : ∀ who (target : M.BehavioralPolicy who),
      seed.expect (fun k =>
        (M.runBehavioral (Profile.update (plays k) who target) horizon).expect (payoff who) -
          (M.runBehavioral (plays k) horizon).expect (payoff who)) ≤ error who) :
    IsNash (M.toBehavioralGameForm horizon)
      (euPreferenceWithin (error 0 + error 1) (fun history who => payoff who history))
      (ownReachAverageProfile M (fun _ => seed) plays fallback) := by
  let average := ownReachAverageProfile M (fun _ => seed) plays fallback
  let value (strategy : Profile M.behavioralSignature) :=
    (M.runBehavioral strategy horizon).expect (payoff 0)
  let mean := seed.expect (fun k => value (plays k))
  have hone (strategy : Profile M.behavioralSignature) :
      (M.runBehavioral strategy horizon).expect (payoff 1) = -value strategy :=
    hzero.expectedUtility_one (M.runBehavioral strategy horizon)
  have hrowLaw (target : M.BehavioralPolicy 0) :
      value (Profile.update average 0 target) =
        seed.expect (fun k => value (Profile.update (plays k) 0 target)) := by
    have h := deviation_against_average M hrecall (fun _ => seed) plays fallback 0 1
      (by decide) (by intro player; fin_cases player <;> simp) target horizon
    exact (congrArg (fun law : FinDist E.History => law.expect (payoff 0)) h).trans
      (FinDist.expect_bind _ _ _)
  have hcolumnLaw (target : M.BehavioralPolicy 1) :
      value (Profile.update average 1 target) =
        seed.expect (fun k => value (Profile.update (plays k) 1 target)) := by
    have h := deviation_against_average M hrecall (fun _ => seed) plays fallback 1 0
      (by decide) (by intro player; fin_cases player <;> simp) target horizon
    exact (congrArg (fun law : FinDist E.History => law.expect (payoff 0)) h).trans
      (FinDist.expect_bind _ _ _)
  have hrow (target : M.BehavioralPolicy 0) :
      value (Profile.update average 0 target) - mean ≤ error 0 := by
    have h := hregret 0 target
    rw [FinDist.expect_sub] at h
    rw [hrowLaw]
    exact h
  have hcolumn (target : M.BehavioralPolicy 1) :
      mean - value (Profile.update average 1 target) ≤ error 1 := by
    have h := hregret 1 target
    simp_rw [hone] at h
    rw [FinDist.expect_sub, FinDist.expect_neg, FinDist.expect_neg] at h
    rw [hcolumnLaw]
    linarith
  have hbaseRow : value average - mean ≤ error 0 := by
    simpa only [Profile.update_eq_self] using hrow (average 0)
  have hbaseColumn : mean - value average ≤ error 1 := by
    simpa only [Profile.update_eq_self] using hcolumn (average 1)
  apply (isNash_iff _).mpr
  intro who target
  fin_cases who
  · have h := hrow target
    show value (Profile.update average 0 target) ≤ value average + (error 0 + error 1)
    linarith
  · show (M.runBehavioral (Profile.update average 1 target) horizon).expect (payoff 1) ≤
      (M.runBehavioral average horizon).expect (payoff 1) + (error 0 + error 1)
    rw [hone, hone]
    have h := hcolumn target
    linarith

end GameTheory.ReBeL
