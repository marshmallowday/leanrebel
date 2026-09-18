/-
# The executable hidden-type reach factors are canonical

The raw table omits inert no-op factors only after proving that their canonical
probabilities are one. Strategic own reach, chance and opponent reach remain
separate, including legal histories with zero probability under a current policy.
-/

import GameTheory.Analysis.ReBeL.Examples.RationalExecution
import GameTheory.Analysis.ReBeL.RationalReach

noncomputable section

namespace GameTheory.ReBeL.Rational.HiddenTypes.Canonical

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Protocol.InformationModel GameTheory.Math.Probability
open GameTheory.ReBeL.Examples.HiddenTypes

/-- The initial no-op has probability one for every canonical behavioral policy. -/
theorem initial_noop_prob (semantic : Profile (model fullPrior).behavioralSignature)
    (who : Player) :
    (semantic who ((model fullPrior).infoOf who (decode .initial).trace)).prob
      (rowChoiceEquiv who .initial ()) = 1 :=
  idle_choice_prob semantic who .initial rfl _

/-- A chance draw does not contribute a strategic own-action factor. -/
theorem playerReach_drawn (semantic : Profile (model fullPrior).behavioralSignature)
    (who : Player) (x y : Bool) :
    (model fullPrior).playerReachProbability semantic who (decode (.drawn x y)).trace = 1 := by
  calc
    _ = (1 : ℝ) *
        (semantic who ((model fullPrior).infoOf who (decode .initial).trace)).prob
          (rowChoiceEquiv who .initial ()) := rfl
    _ = 1 := by rw [one_mul, initial_noop_prob]

/-- The first strategic factor is read at exactly the original private observation. -/
theorem playerReach_second (semantic : Profile (model fullPrior).behavioralSignature)
    (who : Player) (x y a b : Bool) :
    (model fullPrior).playerReachProbability semantic who (decode (.second x y a b)).trace =
      (semantic who ((model fullPrior).infoOf who (decode (.drawn x y)).trace)).prob
        (rowChoiceEquiv who (.drawn x y) (own who a b)) := by
  calc
    _ = (model fullPrior).playerReachProbability semantic who (decode (.drawn x y)).trace *
        (semantic who ((model fullPrior).infoOf who (decode (.drawn x y)).trace)).prob
          (rowChoiceEquiv who (.drawn x y) (own who a b)) := rfl
    _ = _ := by rw [playerReach_drawn, one_mul]

/-- The final strategic factor is evaluated after remembering the own first action. -/
theorem playerReach_finished (semantic : Profile (model fullPrior).behavioralSignature)
    (who : Player) (x y a b c d : Bool) :
    (model fullPrior).playerReachProbability semantic who
        (decode (.finished x y a b c d)).trace =
      (model fullPrior).playerReachProbability semantic who (decode (.second x y a b)).trace *
        (semantic who ((model fullPrior).infoOf who (decode (.second x y a b)).trace)).prob
          (rowChoiceEquiv who (.second x y a b) (own who c d)) := rfl

/-- The actual numeric own-reach product equals the canonical trace product.
In particular this does not replace own reach by joint reach or a posterior. -/
theorem ownReach_correct (numeric : NumericProfile)
    (semantic : Profile (model fullPrior).behavioralSignature)
    (hreal : RowRealizes numeric semantic) (who : Player) (row : Row) :
    (table.ownReach numeric who row : ℝ) =
      (model fullPrior).playerReachProbability semantic who (decode row).trace := by
  cases row with
  | initial =>
      calc
        _ = (1 : ℝ) := by norm_num [HistoryTable.ownReach, table, ownPath]
        _ = _ := rfl
  | drawn x y =>
      rw [playerReach_drawn]
      norm_num [HistoryTable.ownReach, table, ownPath]
  | second x y a b =>
      calc
        _ = (numeric who (information who (.drawn x y)) (own who a b) : ℝ) := by
          simp only [HistoryTable.ownReach, table, ownPath, firstEntry,
            List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          rfl
        _ = (semantic who ((model fullPrior).infoOf who (decode (.drawn x y)).trace)).prob
            (rowChoiceEquiv who (.drawn x y) (own who a b)) :=
          hreal who (.drawn x y) (own who a b)
        _ = _ := (playerReach_second semantic who x y a b).symm
  | finished x y a b c d =>
      calc
        _ = (numeric who (information who (.second x y a b)) (own who c d) : ℝ) *
            (numeric who (information who (.drawn x y)) (own who a b) : ℝ) := by
          simp only [HistoryTable.ownReach, table, ownPath, firstEntry, secondEntry,
            List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Rat.cast_mul]
          rfl
        _ = (semantic who ((model fullPrior).infoOf who (decode (.second x y a b)).trace)).prob
              (rowChoiceEquiv who (.second x y a b) (own who c d)) *
            (semantic who ((model fullPrior).infoOf who (decode (.drawn x y)).trace)).prob
              (rowChoiceEquiv who (.drawn x y) (own who a b)) :=
          congrArg₂ (fun x y : ℝ => x * y)
            (hreal who (.second x y a b) (own who c d))
            (hreal who (.drawn x y) (own who a b))
        _ = (semantic who ((model fullPrior).infoOf who (decode (.drawn x y)).trace)).prob
              (rowChoiceEquiv who (.drawn x y) (own who a b)) *
            (semantic who ((model fullPrior).infoOf who (decode (.second x y a b)).trace)).prob
              (rowChoiceEquiv who (.second x y a b) (own who c d)) := mul_comm _ _
        _ = _ := by rw [playerReach_finished, playerReach_second]

/-- Each private type pair has exactly one quarter of the original chance mass. -/
theorem initial_chance_prob (x y : Bool) :
    (fullPrior.map State.first).prob (.first (x, y)) = (1 : ℝ) / 4 := by
  rw [FinDist.prob_map_of_injective State.first
    (fun _ _ h => State.first.inj h) fullPrior (x, y)]
  norm_num [fullPrior, FinDist.prob_uniformOfFintype]

/-- Runtime chance factors retain the original prior and all supported transitions. -/
theorem chanceReach_correct (row : Row) :
    ((table.chanceFactors row).prod : ℝ) = chanceReach (decode row).trace := by
  cases row <;>
    simp [table, chanceFactors, decode, finish, firstHistory, fullDraw, drawHistory,
      History.extend, initHistory, chanceReach, protocol, transition,
      initial_chance_prob, FinDist.prob_pure_self]

/-- The actual numeric counterfactual reach includes exactly chance and opponents.
There is no positivity requirement on the focal player's reach. -/
theorem counterfactualReach_correct (numeric : NumericProfile)
    (semantic : Profile (model fullPrior).behavioralSignature)
    (hreal : RowRealizes numeric semantic) (who : Player) (row : Row) :
    (table.counterfactualReach numeric who row : ℝ) =
      (model fullPrior).counterfactualReachProbability semantic who (decode row).trace := by
  unfold HistoryTable.counterfactualReach
  rw [Rat.cast_mul, chanceReach_correct,
    counterfactualReach_eq_chance_prod (model fullPrior) semantic who (decode row).trace]
  congr 1
  push_cast
  exact Finset.prod_congr rfl fun other _ => ownReach_correct numeric semantic hreal other row

end GameTheory.ReBeL.Rational.HiddenTypes.Canonical
