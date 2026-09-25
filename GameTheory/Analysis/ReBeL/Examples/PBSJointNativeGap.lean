/-
# Joint query controls

The live solver control uses its actual budget and iteration law. Separate
finite-law controls expose a genuinely correlated tagged query with a sharp
factor two, identical marginals that do not determine joint loss, and a new
unsupported type that cannot be hidden in a density. The finite-law negative
examples are not asserted to be solver-generated CFR gap tables.
-/

import GameTheory.Analysis.ReBeL.PBSJointNativeGap
import GameTheory.Analysis.ReBeL.Examples.PBSNativeConditionalGap

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

/-- Include every legal history, including compatible off-path histories. -/
local instance jointNativeHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- A live full-AOH solver's budget-1/8 mean passes through the JOINT interface
with its actual uniform iteration law. The product specialization has factor one. -/
theorem pbsJointNativeGap_live_budget :
    let slice := fullAOHBeliefSlice (reducedModel fullPrior) finiteBudgetControlBelief 0
    let own := fullAOHOwnLaw (reducedModel fullPrior) finiteBudgetControlBelief 0
    let t := pbsInformationBudgetRounds (reducedModel fullPrior)
      (slice.mixture own).law (fun _ => 2) 1 (1 / 8)
    ((cfrIterationLaw t).product own).expect (fun pair =>
      |pbsInformationCFRConditionalDrawGap (reducedModel fullPrior) slice own
        pbsRootControlFallback cfrPayoff 1 t pair.2 pair.1|) ≤ 1 / 8 := by
  classical
  let slice := fullAOHBeliefSlice (reducedModel fullPrior) finiteBudgetControlBelief 0
  let own := fullAOHOwnLaw (reducedModel fullPrior) finiteBudgetControlBelief 0
  let t := pbsInformationBudgetRounds (reducedModel fullPrior)
    (slice.mixture own).law (fun _ => 2) 1 (1 / 8)
  simpa only [one_mul] using pbsInformationBudget_joint_native_mean_abs_le
    (reducedModel fullPrior) slice own pbsRootControlFallback 1
    (fun h player => cfrPayoff player h) (cumulative_zeroSum fullPrior) 2 (by norm_num)
    (fun h player => cfrPayoff_abs_le_two player h) (1 / 8) (by norm_num)
    ((cfrIterationLaw t).product own) (fun _ => 1) 1 (by norm_num)
    (fun pair => by rw [FinDist.prob_product, mul_one]) (fun _ _ => le_rfl)

end GameTheory.ReBeL.Examples.HiddenTypes

namespace GameTheory.ReBeL.Examples.JointNativeGap

open GameTheory.Math.Probability

/-- A uniform private index followed by the type equal to that retained index. -/
def diagonalQuery : FinDist (Fin 2 × Fin 2) :=
  (cfrIterationLaw 2).map (fun n => (n, n))

/-- Nonnegative diagnostic loss, deliberately sensitive to seed/type correlation. -/
def diagonalLoss (pair : Fin 2 × Fin 2) : ℝ := if pair.1 = pair.2 then 1 else 0

/-- The correlated query is exactly the tagged seed-dependent pure kernel. -/
theorem diagonalQuery_tagged :
    (cfrIterationLaw 2).bind (fun n =>
      (FinDist.pure n).map (fun type => (n, type))) = diagonalQuery := by
  simp only [FinDist.map_pure, ← FinDist.map_eq_bind, diagonalQuery]

/-- Its JOINT density is two on the diagonal and zero elsewhere. Both equal
marginals alone would instead suggest the invalid factor-one product comparison. -/
theorem diagonalQuery_density (pair : Fin 2 × Fin 2) :
    diagonalQuery.prob pair =
      (cfrIterationLaw 2).prob pair.1 * (cfrIterationLaw 2).prob pair.2 *
        (if pair.1 = pair.2 then 2 else 0) := by
  rcases pair with ⟨n, type⟩
  fin_cases n <;> fin_cases type <;>
    norm_num [diagonalQuery, FinDist.prob_map, FinDist.expect_eq_sum,
      Fin.sum_univ_two, cfrIterationLaw, FinDist.prob_ofWeights]

/-- The source-law cap in the joint theorem is genuinely realizable by a
correlated query, without positivity or independence of every joint atom. -/
theorem diagonalQuery_density_le_two (pair : Fin 2 × Fin 2) :
    (if pair.1 = pair.2 then (2 : ℝ) else 0) ≤ 2 := by
  split <;> norm_num

/-- Both marginals remain the original uniform law. -/
theorem diagonalQuery_marginals :
    diagonalQuery.map Prod.fst = cfrIterationLaw 2 ∧
      diagonalQuery.map Prod.snd = cfrIterationLaw 2 := by
  constructor <;> unfold diagonalQuery <;> rw [FinDist.map_comp] <;>
    exact FinDist.map_id _

/-- The factor two is SHARP for this nonnegative joint loss, despite identical
seed and type marginals. This is a law-level obstruction, not a CFR counterexample. -/
theorem diagonalQuery_mean_control :
    ((cfrIterationLaw 2).product (cfrIterationLaw 2)).expect diagonalLoss = 1 / 2 ∧
      diagonalQuery.expect diagonalLoss = 1 := by
  constructor
  · rw [FinDist.expect_product]
    norm_num [FinDist.expect_eq_sum, Fin.sum_univ_two, cfrIterationLaw,
      FinDist.prob_ofWeights, diagonalLoss]
  · simp [diagonalQuery, diagonalLoss, FinDist.expect_map]

/-- Marginal equality cannot justify dropping the joint density factor. -/
theorem diagonalQuery_not_product_bound :
    ¬ diagonalQuery.expect diagonalLoss ≤
      ((cfrIterationLaw 2).product (cfrIterationLaw 2)).expect diagonalLoss := by
  rw [diagonalQuery_mean_control.1, diagonalQuery_mean_control.2]
  norm_num

/-- A newly reached type absent from the model has no finite real density.
The model's off-path completion is not assigned fictitious positive mass. -/
theorem unsupportedQuery_no_density :
    ¬ ∃ ratio : Fin 2 × Fin 2 → ℝ, ∀ pair,
      (FinDist.pure ((0 : Fin 2), (1 : Fin 2))).prob pair =
        (cfrIterationLaw 2).prob pair.1 * (FinDist.pure (0 : Fin 2)).prob pair.2 * ratio pair := by
  rintro ⟨ratio, density⟩
  have impossible := density ((0 : Fin 2), (1 : Fin 2))
  norm_num [FinDist.prob_pure_eq_ite] at impossible

end GameTheory.ReBeL.Examples.JointNativeGap
