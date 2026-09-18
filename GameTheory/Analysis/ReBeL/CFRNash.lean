/-
# Canonical approximate Nash for the constructed CFR solver

The finite iteration law is uniform over exactly rounds 0 through T-1. Each
player privately averages its own reach with those weights. The final theorem
supplies, rather than assumes, every local-learning and root-regret obligation.
-/

import GameTheory.Analysis.ReBeL.AverageNash

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

/-- The uniform law on the completed iteration indices. A zero-sized sample
has no probability law; zero-round output is separately the initial fallback. -/
def cfrIterationLaw (t : ℕ) [NeZero t] : FinDist (Fin t) :=
  FinDist.ofWeights (fun _ => (t : ℝ)⁻¹)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg t))
    (by
      have ht : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
      simp [ht])

/-- The iteration law is exactly the finite average over completed rounds,
not a last-iterate law, linear weighting or shared-player randomization. -/
theorem cfrIterationLaw_expect (t : ℕ) [NeZero t] (f : ℕ → ℝ) :
    (cfrIterationLaw t).expect (fun n => f n.val) =
      (∑ n ∈ Finset.range t, f n) / t := by
  rw [FinDist.expect_eq_sum]
  simp only [cfrIterationLaw, FinDist.prob_ofWeights]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range]
  ring

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History]
variable [∀ who, DecidableEq (M.InfoState who)]
variable [∀ who info, Fintype (M.Choice who info)]

/-- The full-game CFR output after a positive number of completed rounds.
Each local law uses own-reach weights, with the specified zero-reach fallback. -/
def cfrAveragedProfile (clock : ObservationClock M)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (horizon t : ℕ) [NeZero t] : Profile M.behavioralSignature :=
  ownReachAverageProfile M (fun _ => cfrIterationLaw t)
    (fun n : Fin t => cfrPlay M clock fallback payoff horizon n.val) fallback

/-- The public two-player guarantee for actual simultaneous full-game CFR.
Only finite legal menus/histories, an information-local clock, perfect recall,
zero-sum game payoffs and their absolute bounds are inputs. Every complete
behavioral deviation is bounded in the canonical game and Nash predicate. -/
theorem cfrAveragedProfile_isNash (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (bound : Fin 2 → ℝ) (hbound0 : ∀ who, 0 ≤ bound who)
    (hbound : ∀ who history, |payoff who history| ≤ bound who)
    (horizon t : ℕ) [NeZero t] :
    IsNash (M.toBehavioralGameForm horizon)
      (euPreferenceWithin
        (cfrCumulativeBound M clock horizon 0 (bound 0) t / t +
          cfrCumulativeBound M clock horizon 1 (bound 1) t / t)
        (fun history who => payoff who history))
      (cfrAveragedProfile M clock fallback payoff horizon t) := by
  apply ownReachAverage_isNash_of_regret M hrecall (cfrIterationLaw t)
    (fun n : Fin t => cfrPlay M clock fallback payoff horizon n.val) fallback horizon
    payoff hzero (fun who => cfrCumulativeBound M clock horizon who (bound who) t / t)
  intro who target
  rw [cfrIterationLaw_expect]
  exact cfr_average_root_regret_le M clock hrecall fallback payoff horizon who
    (hbound0 who) (hbound who) target (Nat.pos_of_ne_zero (NeZero.ne t))

end GameTheory.ReBeL
