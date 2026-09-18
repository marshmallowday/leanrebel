/-
# Nonunique equilibria and the necessary zero-sum boundary

The positive game has nonconstant payoffs, two distinct equilibria of value
one and a strictly worse third row. The negative coordination game has two
exact equilibria with different values when the zero-sum premise is removed.
Both use the original GameForm, Profile.update and IsNash definitions.
-/

import GameTheory.Analysis.ReBeL.EquilibriumValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section

namespace GameTheory.ReBeL.Examples.EquilibriumValue

open GameTheory.Math.Probability

/-- A finite table used only to test the canonical equilibrium theorem. -/
abbrev signature : GameSignature (Fin 2) where
  Strategy _ := Fin 3
  Outcome := Fin 3 × Fin 3

/-- Deterministic outcomes use the existing canonical game-form constructor. -/
abbrev form : GameForm (Fin 2) :=
  GameForm.deterministic signature fun profile => (profile 0, profile 1)

/-- Two maximizing rows have value one at column zero; the third row loses. -/
def rowPayoff (outcome : Fin 3 × Fin 3) : ℝ :=
  if outcome.1 = 2 then 0 else if outcome.2 = 0 then 1 else 2

/-- The column player's payoff is exactly the negative row payoff. -/
def utility (outcome : Fin 3 × Fin 3) (who : Fin 2) : ℝ :=
  if who = 0 then rowPayoff outcome else -rowPayoff outcome

/-- An actual zero-sum premise, not a supplied equilibrium oracle. -/
theorem zeroSum : IsZeroSum utility := by
  intro outcome
  simp [Fin.sum_univ_two, utility]

/-- A pure profile with the specified row and minimizing column zero. -/
def strategy (row : Fin 3) : Profile form.sig := fun who => if who = 0 then row else 0

/-- Both undominated rows are exact equilibria against every legal deviation. -/
theorem strategy_isNash (row : Fin 3) (hrow : row ≠ 2) :
    IsNash form (euPreference utility) (strategy row) := by
  rw [isNash_iff]
  intro who alternative
  fin_cases who <;> fin_cases alternative <;>
    norm_num [form, strategy, utility, rowPayoff, hrow] <;>
    split_ifs <;> norm_num

/-- Positive control: different equilibrium strategies, the same nonzero value. -/
theorem distinct_equilibria_same_value :
    strategy 0 ≠ strategy 1 ∧
      IsNash form (euPreference utility) (strategy 0) ∧
      IsNash form (euPreference utility) (strategy 1) ∧
      expectedUtility utility 0 (form.play (strategy 0)) = 1 ∧
      expectedUtility utility 0 (form.play (strategy 1)) = 1 := by
  refine ⟨?_, strategy_isNash 0 (by decide), strategy_isNash 1 (by decide), ?_, ?_⟩
  · intro h
    have hrow := congrFun h 0
    norm_num [strategy] at hrow
  · norm_num [form, strategy, utility, rowPayoff]
    decide
  · norm_num [form, strategy, utility, rowPayoff]
    decide

/-- The general value theorem is exercised on the two distinct concrete equilibria. -/
theorem value_theorem_applies :
    expectedUtility utility 0 (form.play (strategy 0)) =
      expectedUtility utility 0 (form.play (strategy 1)) :=
  nash_value_eq form utility zeroSum (strategy 0) (strategy 1)
    (strategy_isNash 0 (by decide)) (strategy_isNash 1 (by decide))

/-- A non-zero-sum coordination payoff: matching zero pays one, matching one pays two. -/
def coordination (outcome : Fin 3 × Fin 3) (_who : Fin 2) : ℝ :=
  if outcome = (0, 0) then 1 else if outcome = (1, 1) then 2 else 0

/-- Both players select the same pure coordinate. -/
def coordinated (action : Fin 3) : Profile form.sig := fun _ => action

/-- Exact Nash does not by itself force a common value outside the zero-sum domain. -/
theorem coordination_isNash (action : Fin 3) (haction : action = 0 ∨ action = 1) :
    IsNash form (euPreference coordination) (coordinated action) := by
  rcases haction with rfl | rfl <;>
    rw [isNash_iff] <;> intro who alternative <;>
    fin_cases who <;> fin_cases alternative <;>
    norm_num [form, coordinated, coordination] <;> split_ifs <;> norm_num

/-- Negative control: removing zero sum admits two different exact equilibrium values. -/
theorem zeroSum_is_necessary :
    ¬ IsZeroSum coordination ∧
      IsNash form (euPreference coordination) (coordinated 0) ∧
      IsNash form (euPreference coordination) (coordinated 1) ∧
      expectedUtility coordination 0 (form.play (coordinated 0)) ≠
        expectedUtility coordination 0 (form.play (coordinated 1)) := by
  refine ⟨?_, coordination_isNash 0 (Or.inl rfl),
    coordination_isNash 1 (Or.inr rfl), ?_⟩
  · intro hzero
    have h := hzero (0, 0)
    norm_num [Fin.sum_univ_two, coordination] at h
  · norm_num [form, coordination, coordinated]

end GameTheory.ReBeL.Examples.EquilibriumValue
