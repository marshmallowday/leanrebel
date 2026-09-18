/-
# The executed hidden-type evaluator is the canonical behavioral runner

The numeric value function is the one actually used by the rational solver.
Primitive menu, payoff and chance-row correctness supply its equality with
Protocol execution for every fuel budget and every legal history. The proof
retains zero-probability branches and early termination.
-/

import GameTheory.Analysis.ReBeL.Examples.RationalChance

noncomputable section

namespace GameTheory.ReBeL.Rational.HiddenTypes.Canonical

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Protocol.InformationModel GameTheory.Math.Probability
open GameTheory.ReBeL.Examples.HiddenTypes

/-- A canonical local menu is a subtype of the finite optional Boolean carrier. -/
local instance canonicalChoiceFintype (who : Player) (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- The exact rational evaluator equals the original canonical continuation
expectation. No root-value or regret identity is a hypothesis. -/
theorem value_correct (numeric : NumericProfile)
    (semantic : Profile (model fullPrior).behavioralSignature)
    (hreal : RowRealizes numeric semantic) :
    ∀ fuel row who, (table.value numeric fuel row who : ℝ) =
      ((model fullPrior).runBehavioralFrom semantic fuel (decode row)).expect
        (fun history => cumulativeUtility (reward fullPrior) history who) := by
  have shortcut (x y : ℚ) : (if x = 0 then 0 else x * y) = x * y := by
    by_cases h : x = 0 <;> simp [h]
  intro fuel
  induction fuel with
  | zero =>
      intro row who
      simpa only [HistoryTable.value, InformationModel.runBehavioralFrom,
        runRandomizedFor_zero, FinDist.expect_pure] using payoff_correct row who
  | succ fuel ih =>
      intro row who
      by_cases hterm : (protocol fullPrior).terminal (decode row).state
      · rw [HistoryTable.value, if_pos ((terminal_correct row).mpr hterm),
          (model fullPrior).runBehavioralFrom_of_terminal semantic (fuel + 1) hterm,
          FinDist.expect_pure]
        exact payoff_correct row who
      · have hfalse : ¬ table.terminal row = true :=
          fun h => hterm ((terminal_correct row).mp h)
        rw [HistoryTable.value, if_neg hfalse]
        simp only [shortcut]
        rw [show fuel + 1 = 1 + fuel by omega,
          (model fullPrior).runBehavioralFrom_add semantic 1 fuel (decode row),
          run_one_reindexed semantic row hterm, FinDist.expect_bind,
          FinDist.expect_bind, FinDist.expect_eq_sum]
        push_cast
        rw [← (rowJointEquiv row).sum_comp]
        simp only [Equiv.symm_apply_apply]
        apply Finset.sum_congr rfl
        intro draw _
        rw [FinDist.prob_pi]
        have hjoint : (table.jointWeight numeric row draw : ℝ) =
            ∏ player, (semantic player ((model fullPrior).infoOf player (decode row).trace)).prob
              ((rowJointEquiv row draw) player) := by
          unfold HistoryTable.jointWeight
          push_cast
          exact Finset.prod_congr rfl fun player _ => hreal player row (draw player)
        rw [hjoint]
        congr 1
        rw [← children_expect row hterm draw]
        simp only [List.map_map, Function.comp_def, Rat.cast_mul, ih]

/-- In particular the actual numeric root evaluation is the original full-game payoff. -/
theorem root_value_correct (numeric : NumericProfile)
    (semantic : Profile (model fullPrior).behavioralSignature)
    (hreal : RowRealizes numeric semantic) (fuel : ℕ) (who : Player) :
    (table.value numeric fuel .initial who : ℝ) =
      ((model fullPrior).runBehavioral semantic fuel).expect
        (fun history => cumulativeUtility (reward fullPrior) history who) :=
  value_correct numeric semantic hreal fuel .initial who

/-- Two interpretations of the same complete numeric profile have identical
canonical values at every history and every cut. Unreachable observations do
not introduce a second payoff semantics. -/
theorem represented_values_unique (numeric : NumericProfile)
    (first second : Profile (model fullPrior).behavioralSignature)
    (hfirst : RowRealizes numeric first) (hsecond : RowRealizes numeric second)
    (history : (protocol fullPrior).History) (fuel : ℕ) (who : Player) :
    ((model fullPrior).runBehavioralFrom first fuel history).expect
        (fun h => cumulativeUtility (reward fullPrior) h who) =
      ((model fullPrior).runBehavioralFrom second fuel history).expect
        (fun h => cumulativeUtility (reward fullPrior) h who) := by
  obtain ⟨row, rfl⟩ := decode_surjective history
  exact (value_correct numeric first hfirst fuel row who).symm.trans
    (value_correct numeric second hsecond fuel row who)

end GameTheory.ReBeL.Rational.HiddenTypes.Canonical
