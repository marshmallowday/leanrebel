/-
# Typewise best responses and finite minimax

A type-local plan family is compiled to the existing canonical matrix game.
The row chooses one legal continuation plan per type, not an action depending
on the opponent's hidden state. The opponent's law is held fixed when own
weights vary. Simultaneous best responses are constructed coordinatewise,
including zero-weight types. This is the finite normal-form part of M05;
connection to protocol continuation is a separate, explicit bridge.
-/

import GameTheory.Analysis.MatrixValue
import GameTheory.Analysis.ZeroSumLearning

noncomputable section

namespace GameTheory.ReBeL.TypeGame

open GameTheory.Math.Probability GameTheory.MatrixGame

universe u

variable {T B : Type u} [Fintype T] [Fintype B] [Nonempty B]
variable {Action : T → Type u}
variable [∀ t, Fintype (Action t)] [∀ t, Nonempty (Action t)]
variable (payoff : (t : T) → Action t → B → ℝ)

/-- The canonical matrix indexed by a complete type-local plan and an
opponent plan. Nonnegative weights need not have mass one. -/
def matrix (weight : T → ℝ) (plan : (t : T) → Action t) (opponent : B) : ℝ :=
  ∑ t, weight t * payoff t (plan t) opponent

/-- An attaining type response, chosen from the actual finite legal menu. -/
def typeResponse (opponent : FinDist B) (t : T) : Action t :=
  Classical.choose (Finite.exists_max fun action : Action t =>
    opponent.expect (payoff t action))

/-- Eq. (1) in the finite type-local normal form. It does not divide by the
own type's probability, and hence also defines an off-path best response. -/
def infoValue (opponent : FinDist B) (t : T) : ℝ :=
  opponent.expect (payoff t (typeResponse payoff opponent t))

/-- Every legal action is bounded by the selected type best response. -/
theorem le_infoValue (opponent : FinDist B) (t : T) (action : Action t) :
    opponent.expect (payoff t action) ≤ infoValue payoff opponent t :=
  Classical.choose_spec (Finite.exists_max fun action : Action t =>
    opponent.expect (payoff t action)) action

/-- The best-response affine branch associated with a fixed opponent. -/
def branch (weight : T → ℝ) (opponent : FinDist B) : ℝ :=
  ∑ t, weight t * infoValue payoff opponent t

/-- The scalar value comes from the existing finite minimax theorem. -/
def value (weight : T → ℝ) : ℝ :=
  MatrixGame.value (matrix payoff weight)

/-- Expanding the canonical pure-row payoff leaves the actual conditional
opponent expectation inside each type summand. -/
theorem pure_payoff_eq (weight : T → ℝ) (plan : (t : T) → Action t)
    (opponent : FinDist B) :
    expectedPayoff (matrix payoff weight) (FinDist.pure plan) opponent =
      ∑ t, weight t * opponent.expect (payoff t (plan t)) := by
  rw [expectedPayoff_pure_row]
  unfold matrix
  rw [← FinDist.expect_sum_comm]
  simp only [FinDist.expect_smul]

/-- A single legal type-local plan simultaneously attains every conditional
best response. No positive own-type mass is needed. -/
theorem simultaneous_response (weight : T → ℝ) (opponent : FinDist B) :
    expectedPayoff (matrix payoff weight)
      (FinDist.pure (typeResponse payoff opponent)) opponent =
        branch payoff weight opponent := by
  rw [pure_payoff_eq]
  rfl

/-- Lemma 1's upper bound for every mixed complete plan, not only pure plans. -/
theorem payoff_le_branch (weight : T → ℝ) (nonneg : ∀ t, 0 ≤ weight t)
    (row : FinDist ((t : T) → Action t)) (opponent : FinDist B) :
    expectedPayoff (matrix payoff weight) row opponent ≤ branch payoff weight opponent := by
  rw [expectedPayoff_eq_expect_rows]
  apply FinDist.expect_le_of_forall
  intro plan _
  rw [pure_payoff_eq]
  exact Finset.sum_le_sum fun t _ =>
    mul_le_mul_of_nonneg_left (le_infoValue payoff opponent t (plan t)) (nonneg t)

/-- Lemma 1: the affine branch is an attained maximum over all canonical
mixed row strategies. This includes boundary weights and nonunique maximizers. -/
theorem branch_isGreatest (weight : T → ℝ) (nonneg : ∀ t, 0 ≤ weight t)
    (opponent : FinDist B) :
    IsGreatest (Set.range fun row : FinDist ((t : T) → Action t) =>
      expectedPayoff (matrix payoff weight) row opponent) (branch payoff weight opponent) := by
  constructor
  · exact ⟨FinDist.pure (typeResponse payoff opponent), simultaneous_response payoff _ _⟩
  · rintro candidate ⟨row, rfl⟩
    exact payoff_le_branch payoff weight nonneg row opponent

/-- Any fixed opponent gives an upper affine bound on the minimax value. -/
theorem value_le_branch (weight : T → ℝ) (nonneg : ∀ t, 0 ≤ weight t)
    (opponent : FinDist B) : value payoff weight ≤ branch payoff weight opponent :=
  (valueRow_guarantees (matrix payoff weight) opponent).trans
    (payoff_le_branch payoff weight nonneg _ opponent)

/-- The selected minimax opponent attains the minimum affine branch. -/
theorem branch_valueColumn (weight : T → ℝ) (nonneg : ∀ t, 0 ≤ weight t) :
    branch payoff weight (valueColumn (matrix payoff weight)) = value payoff weight := by
  apply le_antisymm
  · rw [← simultaneous_response]
    exact valueColumn_caps (matrix payoff weight) _
  · exact value_le_branch payoff weight nonneg _

/-- Lemma 2: an attained minimum, derived from finite-game existence. -/
theorem value_isLeast (weight : T → ℝ) (nonneg : ∀ t, 0 ≤ weight t) :
    IsLeast (Set.range (branch payoff weight)) (value payoff weight) := by
  constructor
  · exact ⟨valueColumn (matrix payoff weight), branch_valueColumn payoff weight nonneg⟩
  · rintro candidate ⟨opponent, rfl⟩
    exact value_le_branch payoff weight nonneg opponent

/-- Minimizing opponents are exactly the canonical optimal columns. -/
theorem branch_eq_value_iff_optimal (weight : T → ℝ) (nonneg : ∀ t, 0 ≤ weight t)
    (opponent : FinDist B) :
    branch payoff weight opponent = value payoff weight ↔
      opponent ∈ optimalColumnStrategies (matrix payoff weight) := by
  constructor
  · intro equality row
    exact (payoff_le_branch payoff weight nonneg row opponent).trans_eq equality
  · intro optimal
    apply le_antisymm
    · rw [← simultaneous_response]
      exact optimal _
    · exact value_le_branch payoff weight nonneg opponent

/-- The minimizers are exactly the opponent components of some Nash
profile; no uniqueness of either equilibrium strategy is assumed. -/
theorem branch_eq_value_iff_equilibriumOpponent
    (weight : T → ℝ) (nonneg : ∀ t, 0 ≤ weight t) (opponent : FinDist B) :
    branch payoff weight opponent = value payoff weight ↔
      ∃ row : FinDist ((t : T) → Action t),
        IsNash (form ((t : T) → Action t) B).mixed
          (euPreference (utility (matrix payoff weight))) (mixedProfile row opponent) := by
  rw [branch_eq_value_iff_optimal payoff weight nonneg]
  constructor
  · intro optimal
    exact ⟨valueRow (matrix payoff weight),
      (optimal_pairs_iff_isNash _ _ _).mp
        ⟨valueRow_guarantees (matrix payoff weight), optimal⟩⟩
  · rintro ⟨row, equilibrium⟩
    exact ((optimal_pairs_iff_isNash _ _ _).mpr equilibrium).2

/-- The fixed-opponent branch is linear in the own weights, on its whole
ambient vector space. The type values do not depend on those weights. -/
theorem branch_linear (first second : T → ℝ) (a b : ℝ) (opponent : FinDist B) :
    branch payoff (fun t => a * first t + b * second t) opponent =
      a * branch payoff first opponent + b * branch payoff second opponent := by
  unfold branch
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]

end GameTheory.ReBeL.TypeGame
