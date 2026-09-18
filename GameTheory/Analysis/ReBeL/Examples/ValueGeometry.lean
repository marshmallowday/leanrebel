/-
# Real game-level controls for M05

The first example derives its value from a canonical finite zero-sum matrix
game and refutes the global concavity/support claimed for radial normalization.
It does not refute the existence of the corrected extension. The second is
Appendix F's hidden-coin prediction game, with nonunique optimal opponents at
the nondifferentiable midpoint. Off-path conditional type values remain defined.
-/

import GameTheory.Analysis.ReBeL.ValueGeometry
import Mathlib.Analysis.Calculus.Deriv.Abs

noncomputable section

namespace GameTheory.ReBeL.Examples.ValueGeometry

open GameTheory.Math.Probability GameTheory.MatrixGame
open GameTheory.ReBeL.TypeGame

/-- A player with a hidden binary type and no choices receives one exactly
for type zero; the opponent receives its negative. -/
def indicatorPayoff (type : Fin 2) (_ : Unit) (_ : Unit) : ℝ :=
  if type = 0 then 1 else 0

/-- Conditional best-response values are fixed even for a zero-mass type. -/
theorem indicator_infoValue (opponent : FinDist Unit) (type : Fin 2) :
    infoValue indicatorPayoff opponent type = if type = 0 then 1 else 0 := by
  simp [infoValue, indicatorPayoff]

/-- Every opponent branch is the own mass of type zero. -/
theorem indicator_branch (weight : Fin 2 → ℝ) (opponent : FinDist Unit) :
    branch indicatorPayoff weight opponent = weight 0 := by
  simp [branch, indicator_infoValue, Fin.sum_univ_two]

/-- The actual minimax value of the canonical game, not a separately assigned
value function, equals the first type's mass. -/
theorem indicator_value (weight : Fin 2 → ℝ) (nonneg : ∀ type, 0 ≤ weight type) :
    value indicatorPayoff weight = weight 0 := by
  rw [← branch_valueColumn indicatorPayoff weight nonneg, indicator_branch]

/-- Appendix F's radial-normalization construction applied to that game. -/
def normalizedIndicatorValue (weight : Fin 2 → ℝ) : ℝ :=
  value indicatorPayoff (fun type => weight type / (weight 0 + weight 1))

/-- Exact reduction of the normalized game value on nonnegative weights. -/
theorem normalizedIndicatorValue_pair (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    normalizedIndicatorValue ![a, b] = a / (a + b) := by
  unfold normalizedIndicatorValue
  rw [indicator_value]
  · rfl
  · intro type
    fin_cases type <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] <;> positivity

/-- The normalized extension violates Jensen's inequality at strictly
positive weights, so the problem is not caused by boundary conditioning. -/
theorem normalizedIndicatorValue_not_concave :
    ¬ ConcaveOn ℝ {weight : Fin 2 → ℝ | ∀ type, 0 < weight type}
      normalizedIndicatorValue := by
  intro concave
  have hfirst : (fun type : Fin 2 => ![(1 : ℝ), 1] type) ∈
      {weight : Fin 2 → ℝ | ∀ type, 0 < weight type} := by
    intro type
    fin_cases type <;> norm_num
  have hsecond : (fun type : Fin 2 => ![(1 : ℝ), 3] type) ∈
      {weight : Fin 2 → ℝ | ∀ type, 0 < weight type} := by
    intro type
    fin_cases type <;> norm_num
  have inequality := concave.2 hfirst hsecond (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have midpoint : (1 / 2 : ℝ) • (![(1 : ℝ), 1] : Fin 2 → ℝ) +
      (1 / 2 : ℝ) • (![(1 : ℝ), 3] : Fin 2 → ℝ) = ![1, 2] := by
    funext type
    fin_cases type <;> norm_num
  rw [midpoint, normalizedIndicatorValue_pair _ _ (by norm_num) (by norm_num),
    normalizedIndicatorValue_pair _ _ (by norm_num) (by norm_num),
    normalizedIndicatorValue_pair _ _ (by norm_num) (by norm_num)] at inequality
  norm_num at inequality

/-- Eq. (2)'s centered type vector is not a global supporting vector for
Appendix F's particular normalized extension, even at an interior base. -/
theorem normalizedIndicatorValue_not_global_support :
    ¬ ∀ point : Fin 2 → ℝ, (∀ type, 0 < point type) →
      normalizedIndicatorValue point ≤ normalizedIndicatorValue ![1 / 2, 1 / 2] +
        ∑ type, centeredVector indicatorPayoff ![1 / 2, 1 / 2] (FinDist.pure ()) type *
          (point type - (![1 / 2, 1 / 2] : Fin 2 → ℝ) type) := by
  intro support
  have hpoint : ∀ type : Fin 2, 0 < (![(1 / 2 : ℝ), 3 / 2] : Fin 2 → ℝ) type := by
    intro type
    fin_cases type <;> norm_num
  have inequality := support ![1 / 2, 3 / 2] hpoint
  have hbase : ∀ type : Fin 2, 0 ≤ (![(1 / 2 : ℝ), 1 / 2] : Fin 2 → ℝ) type := by
    intro type
    fin_cases type <;> norm_num
  rw [normalizedIndicatorValue_pair _ _ (by norm_num) (by norm_num),
    normalizedIndicatorValue_pair _ _ (by norm_num) (by norm_num)] at inequality
  norm_num [centeredVector, indicator_infoValue, indicator_value _ hbase,
    Fin.sum_univ_two] at inequality

/-- The repaired extension has the required support for every nonnegative
weight vector in the very same game that refutes radial normalization. -/
theorem indicator_corrected_support (point : Fin 2 → ℝ) (hpoint : ∀ type, 0 ≤ point type) :
    centeredExtension indicatorPayoff ![1 / 2, 1 / 2] point ≤
      centeredExtension indicatorPayoff ![1 / 2, 1 / 2] ![1 / 2, 1 / 2] +
        ∑ type, centeredVector indicatorPayoff ![1 / 2, 1 / 2] (FinDist.pure ()) type *
          (point type - (![1 / 2, 1 / 2] : Fin 2 → ℝ) type) := by
  have hbase : (![(1 / 2 : ℝ), 1 / 2] : Fin 2 → ℝ) ∈ stdSimplex ℝ (Fin 2) := by
    constructor
    · intro type
      fin_cases type <;> norm_num
    · norm_num [Fin.sum_univ_two]
  apply centeredExtension_support indicatorPayoff hbase point hpoint (FinDist.pure ())
  rw [indicator_branch, indicator_value _ hbase.1]

/-- Type zero has zero own mass, but its conditional best-response value is
still one rather than an arbitrary equilibrium off-path action value. -/
theorem indicator_boundary_control :
    value indicatorPayoff ![0, 1] = 0 ∧ infoValue indicatorPayoff (FinDist.pure ()) 0 = 1 := by
  constructor
  · rw [indicator_value]
    · rfl
    · intro type
      fin_cases type <;> norm_num
  · simp [indicator_infoValue]

/-- Hidden-coin prediction: the informed player has no action; the predictor
receives one for a correct guess and minus one for an incorrect guess. -/
def coinPayoff (type : Fin 2) (_ : Unit) (guess : Fin 2) : ℝ :=
  if type = guess then -1 else 1

/-- No choice by the informed player can change a conditional coin payoff. -/
theorem coin_infoValue (opponent : FinDist (Fin 2)) (type : Fin 2) :
    infoValue coinPayoff opponent type = opponent.expect (fun guess =>
      if type = guess then -1 else 1) := rfl

/-- Every row distribution has the same payoff. This equality holds even
outside the nonnegative cone and makes the global nonsmooth test exact. -/
theorem coin_payoff_eq_branch (weight : Fin 2 → ℝ)
    (row : FinDist (Fin 2 → Unit)) (opponent : FinDist (Fin 2)) :
    expectedPayoff (matrix coinPayoff weight) row opponent = branch coinPayoff weight opponent := by
  rw [expectedPayoff_eq_expect_rows]
  calc
    _ = row.expect (fun _ => branch coinPayoff weight opponent) := by
      apply FinDist.expect_congr
      intro plan _
      rw [pure_payoff_eq]
      rfl
    _ = _ := FinDist.expect_const _ _

/-- The affine branches are mixtures of the two pure guessing payoffs. -/
theorem coin_branch (weight : Fin 2 → ℝ) (opponent : FinDist (Fin 2)) :
    branch coinPayoff weight opponent = opponent.expect (fun guess =>
      if guess = 0 then weight 1 - weight 0 else weight 0 - weight 1) := by
  unfold branch
  simp only [Fin.sum_univ_two, coin_infoValue]
  rw [← FinDist.expect_smul, ← FinDist.expect_smul, ← FinDist.expect_add]
  apply FinDist.expect_congr
  intro guess _
  fin_cases guess <;> simp <;> ring

/-- The minimax value really is the lower envelope of the two affine
opponent branches, including at their crossing point. -/
theorem coin_value (weight : Fin 2 → ℝ) :
    value coinPayoff weight = min (weight 1 - weight 0) (weight 0 - weight 1) := by
  apply le_antisymm
  · apply le_min
    · have bound := valueRow_guarantees (matrix coinPayoff weight) (FinDist.pure 0)
      rw [coin_payoff_eq_branch, coin_branch, FinDist.expect_pure, if_pos rfl] at bound
      exact bound
    · have bound := valueRow_guarantees (matrix coinPayoff weight) (FinDist.pure 1)
      rw [coin_payoff_eq_branch, coin_branch, FinDist.expect_pure, if_neg (by decide)] at bound
      exact bound
  · let opponent := valueColumn (matrix coinPayoff weight)
    have bound := valueColumn_caps (matrix coinPayoff weight)
      (FinDist.pure (fun _ : Fin 2 => ()))
    rw [coin_payoff_eq_branch, coin_branch] at bound
    refine le_trans ?_ bound
    calc
      min (weight 1 - weight 0) (weight 0 - weight 1) =
          opponent.expect (fun _ => min (weight 1 - weight 0) (weight 0 - weight 1)) :=
        (FinDist.expect_const _ _).symm
      _ ≤ _ := FinDist.expect_mono fun guess _ => by
        split_ifs
        · exact min_le_left _ _
        · exact min_le_right _ _

/-- The real affine coordinate through the probability simplex. -/
def coinSimplexValue (p : ℝ) : ℝ := value coinPayoff ![p, 1 - p]

/-- Figure 3's value curve, derived from its canonical game. The equality
holds on all real coordinates, making the differentiability claim unambiguous. -/
theorem coinSimplexValue_eq (p : ℝ) : coinSimplexValue p = -|2 * p - 1| := by
  rw [coinSimplexValue, coin_value]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  by_cases sign : 0 ≤ 2 * p - 1
  · rw [abs_of_nonneg sign, min_eq_left (by linarith)]
    ring
  · rw [abs_of_neg (lt_of_not_ge sign), min_eq_right (by linarith)]
    ring

/-- The equal-belief midpoint is genuinely nondifferentiable, rather than
merely a location where a selected equilibrium changes. -/
theorem coinSimplexValue_not_differentiable :
    ¬ DifferentiableAt ℝ coinSimplexValue (1 / 2 : ℝ) := by
  intro smooth
  have formula : coinSimplexValue = fun p : ℝ => -|2 * p - 1| := funext coinSimplexValue_eq
  rw [formula] at smooth
  have smooth' : DifferentiableAt ℝ (fun p : ℝ => -|2 * p - 1|) (((0 : ℝ) + 1) / 2) := by
    simpa using smooth
  have composed := smooth'.neg.comp (0 : ℝ)
    (by fun_prop : DifferentiableAt ℝ (fun x : ℝ => (x + 1) / 2) 0)
  have identity : (fun x : ℝ => -(-|2 * ((x + 1) / 2) - 1|)) = abs := by
    funext x
    rw [neg_neg]
    congr 1
    ring
  apply not_differentiableAt_abs_zero
  simpa only [Function.comp_def, identity] using composed

/-- Two distinct pure opponents both attain the midpoint value. Thus the
support theorem cannot require a unique minimizing opponent. -/
theorem coin_nonunique_opponents :
    FinDist.pure (0 : Fin 2) ≠ FinDist.pure (1 : Fin 2) ∧
      branch coinPayoff ![1 / 2, 1 / 2] (FinDist.pure 0) =
        value coinPayoff ![1 / 2, 1 / 2] ∧
      branch coinPayoff ![1 / 2, 1 / 2] (FinDist.pure 1) =
        value coinPayoff ![1 / 2, 1 / 2] := by
  constructor
  · intro equality
    have probability := congrArg (fun law : FinDist (Fin 2) => law.prob 0) equality
    norm_num at probability
  · constructor <;> norm_num [coin_branch, coin_value]

/-- Both equilibrium opponents give valid support at the nondifferentiable
midpoint, including comparisons against boundary beliefs. -/
theorem coin_midpoint_support (point : Fin 2 → ℝ) (hpoint : point ∈ stdSimplex ℝ (Fin 2))
    (guess : Fin 2) :
    value coinPayoff point ≤ value coinPayoff ![1 / 2, 1 / 2] +
      ∑ type, centeredVector coinPayoff ![1 / 2, 1 / 2] (FinDist.pure guess) type *
        (point type - (![1 / 2, 1 / 2] : Fin 2 → ℝ) type) := by
  have hbase : (![(1 / 2 : ℝ), 1 / 2] : Fin 2 → ℝ) ∈ stdSimplex ℝ (Fin 2) := by
    constructor
    · intro type
      fin_cases type <;> norm_num
    · norm_num [Fin.sum_univ_two]
  apply simplex_support coinPayoff hbase hpoint (FinDist.pure guess)
  fin_cases guess <;> norm_num [coin_branch, coin_value]

end GameTheory.ReBeL.Examples.ValueGeometry
