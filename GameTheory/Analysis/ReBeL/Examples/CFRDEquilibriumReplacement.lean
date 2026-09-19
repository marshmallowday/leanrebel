/-
# Equilibrium replacement need not preserve exploitation of a fixed opponent

This control reuses the canonical GameForm, Profile.update and IsNash from
the existing finite equilibrium examples. Two exact zero-sum equilibria
retain the same security value, but one obtains more from a weak fixed
opponent. Thus Nash alone does not prove the stronger pointwise comparison
used by the generic resolver-transfer lemma. This is a counterexample to
that proposed proof step, NOT a counterexample to ReBeL's recursive solver.
-/

import GameTheory.Analysis.ReBeL.Examples.EquilibriumValue

noncomputable section

namespace GameTheory.ReBeL.Examples.EquilibriumReplacement

open GameTheory.Math.Probability
open GameTheory.ReBeL.Examples.EquilibriumValue

/-- Rows zero and one guarantee zero. Row one alone exploits column one;
row two is strictly worse and prevents the game from being a constant table. -/
def replacementPayoff (outcome : Fin 3 × Fin 3) : ℝ :=
  if outcome.1 = 2 then -1 else if outcome.1 = 1 ∧ outcome.2 = 1 then 1 else 0

/-- The opponent's payoff is exactly the negative focal payoff. -/
def replacementUtility (outcome : Fin 3 × Fin 3) (who : Fin 2) : ℝ :=
  if who = 0 then replacementPayoff outcome else -replacementPayoff outcome

/-- The control is genuinely zero sum. -/
theorem replacement_zeroSum : IsZeroSum replacementUtility := by
  intro outcome
  simp [Fin.sum_univ_two, replacementUtility]

/-- Both focal rows are exact Nash strategies against column zero, with
all legal deviations checked in the canonical equilibrium predicate. -/
theorem replacement_isNash (row : Fin 3) (good : row = 0 ∨ row = 1) :
    IsNash form (euPreference replacementUtility) (strategy row) := by
  have zero_ne_two : (0 : Fin 3) ≠ 2 := by decide
  have one_ne_two : (1 : Fin 3) ≠ 2 := by decide
  rcases good with rfl | rfl <;>
    rw [isNash_iff] <;> intro who alternative <;>
    fin_cases who <;> fin_cases alternative <;>
    norm_num [form, strategy, replacementUtility, replacementPayoff,
      zero_ne_two, one_ne_two] <;> split_ifs <;> norm_num

/-- The canonical common-equilibrium-value theorem remains valid. -/
theorem replacement_same_equilibrium_value :
    expectedUtility replacementUtility 0 (form.play (strategy 1)) =
      expectedUtility replacementUtility 0 (form.play (strategy 0)) :=
  nash_value_eq form replacementUtility replacement_zeroSum (strategy 1) (strategy 0)
    (replacement_isNash 1 (Or.inr rfl)) (replacement_isNash 0 (Or.inl rfl))

/-- Both replacement choices still guarantee the common value zero against
EVERY legal opposing action, not only against the equilibrium opponent. -/
theorem replacement_security (row : Fin 3) (good : row = 0 ∨ row = 1)
    (opponent : Fin 3) :
    0 ≤ expectedUtility replacementUtility 0
      (form.play (Profile.update (strategy row) 1 opponent)) := by
  have zero_ne_two : (0 : Fin 3) ≠ 2 := by decide
  have one_ne_two : (1 : Fin 3) ≠ 2 := by decide
  rcases good with rfl | rfl <;> fin_cases opponent <;>
    norm_num [form, strategy, replacementUtility, replacementPayoff,
      zero_ne_two, one_ne_two]

/-- Changing between the exact Nash strategies loses one unit against the
same fixed weak opponent, despite preserving the worst-case guarantee. -/
theorem replacement_loses_one :
    expectedUtility replacementUtility 0
        (form.play (Profile.update (strategy 1) 1 (1 : Fin 3))) -
      expectedUtility replacementUtility 0
        (form.play (Profile.update (strategy 0) 1 (1 : Fin 3))) = 1 := by
  have zero_ne_two : (0 : Fin 3) ≠ 2 := by decide
  have one_ne_two : (1 : Fin 3) ≠ 2 := by decide
  norm_num [form, strategy, replacementUtility, replacementPayoff,
    zero_ne_two, one_ne_two]

/-- An explicit regression guard against inferring pointwise no-loss from
ordinary Nash: both premises hold while the proposed conclusion is false. -/
theorem nash_not_pointwise_replacement :
    IsNash form (euPreference replacementUtility) (strategy 1) ∧
      IsNash form (euPreference replacementUtility) (strategy 0) ∧
      ¬ expectedUtility replacementUtility 0
          (form.play (Profile.update (strategy 1) 1 (1 : Fin 3))) ≤
        expectedUtility replacementUtility 0
          (form.play (Profile.update (strategy 0) 1 (1 : Fin 3))) := by
  refine ⟨replacement_isNash 1 (Or.inr rfl), replacement_isNash 0 (Or.inl rfl), ?_⟩
  linarith [replacement_loses_one]

end GameTheory.ReBeL.Examples.EquilibriumReplacement
