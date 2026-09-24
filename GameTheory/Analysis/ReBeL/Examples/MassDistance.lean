/-
# Mass-distance controls for support changes and nonzero perturbations

A biased two-point law saturates the bounded-observable inequality. Equal
observations do not hide a change of hidden support. These are finite-law
regressions, not claims about the paper's full recursive safety theorem.
-/

import GameTheory.Math.Probability.FinDistMassDistance

noncomputable section

namespace GameTheory.ReBeL.Examples.MassDistance

open GameTheory.Math.Probability

/-- A nondegenerate two-point law, with mass one quarter at the first point. -/
def firstLaw : FinDist (Fin 2) :=
  FinDist.mix (1 / 4) (by norm_num) (by norm_num) (FinDist.pure 0) (FinDist.pure 1)

/-- Reverse the bias without changing the support. -/
def secondLaw : FinDist (Fin 2) :=
  FinDist.mix (3 / 4) (by norm_num) (by norm_num) (FinDist.pure 0) (FinDist.pure 1)

/-- Both probabilities change by one half, so the unnormalized distance is one. -/
theorem positive_distance : FinDist.massDistance firstLaw secondLaw = 1 := by
  norm_num [FinDist.massDistance_eq_sum, Fin.sum_univ_two, firstLaw, secondLaw,
    FinDist.prob_mix, FinDist.prob_pure_eq_ite]

/-- The coefficient in the bounded-observable inequality is sharp. -/
theorem observable_bound_is_sharp :
    |firstLaw.expect (fun i => if i = 0 then (1 : ℝ) else -1) -
      secondLaw.expect (fun i => if i = 0 then (1 : ℝ) else -1)| =
        FinDist.massDistance firstLaw secondLaw := by
  rw [positive_distance]
  norm_num [firstLaw, secondLaw, FinDist.expect_mix, FinDist.expect_pure]

/-- New support is charged even though the public observation law is identical. -/
theorem observation_equality_does_not_erase_distance :
    (FinDist.pure (0 : Fin 2)).map (fun _ => ()) =
        (FinDist.pure (1 : Fin 2)).map (fun _ => ()) ∧
      FinDist.massDistance (FinDist.pure (0 : Fin 2)) (FinDist.pure 1) = 2 := by
  constructor
  · simp only [FinDist.map_pure]
  · norm_num [FinDist.massDistance_eq_sum, Fin.sum_univ_two, FinDist.prob_pure_eq_ite]

/-- The finite-support API does not require the ambient carrier to be finite. -/
theorem infinite_carrier_self (law : FinDist Nat) : FinDist.massDistance law law = 0 :=
  FinDist.massDistance_self law

end GameTheory.ReBeL.Examples.MassDistance
