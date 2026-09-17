/-
# The zero-leaf search failure in Figure 1b

Figure 1b depicts the naive perfect-information-style one-ply truncation,
NOT an already-correct PBS tree. Replacing all continuation values by their
zero equilibrium values makes every mixture tie. The original game still
separates pure rock from the displayed (2/5,2/5,1/5) mixture.
-/

import GameTheory.ReBeL.Examples.ModifiedRPS

noncomputable section

namespace GameTheory.ReBeL.Examples.ModifiedRPS

open GameTheory.Math.Probability

/-- The naive one-ply search objective displayed in Figure 1b. -/
def zeroLeafObjective (policy : FinDist Move) : ℝ := policy.expect (fun _ => 0)

/-- Every legal mixture ties when the three leaf values are all replaced by zero. -/
theorem zeroLeaf_all_tie (policy : FinDist Move) : zeroLeafObjective policy = 0 := by
  simp [zeroLeafObjective]

/-- The uninformative truncation cannot distinguish the two candidate policies. -/
theorem zeroLeaf_misses_exploitation :
    zeroLeafObjective (FinDist.pure .rock) = zeroLeafObjective displayedLaw ∧
      (FinDist.pure Move.rock).expect (fun row => payoff row .paper) <
        displayedLaw.expect (fun row => payoff row .paper) := by
  constructor
  · rw [zeroLeaf_all_tie, zeroLeaf_all_tie]
  · rw [FinDist.expect_pure, displayed_column_value]
    norm_num [payoff]

/-- A continuation against a fixed response is a function of the whole root belief. -/
def responseValue (belief : FinDist Move) (response : Move) : ℝ :=
  belief.expect (fun hiddenMove => payoff hiddenMove response)

/-- The two beliefs at the same public situation require different continuation values. -/
theorem belief_value_not_constant :
    responseValue (FinDist.pure .rock) .paper = -1 ∧
      responseValue displayedLaw .paper = 0 := by
  constructor
  · simp [responseValue, FinDist.expect_pure, payoff]
  · exact displayed_column_value .paper

/-- The displayed belief protects against every mixture of the opponent's responses. -/
theorem displayed_against_every_response (opponent : FinDist Move) :
    opponent.expect (responseValue displayedLaw) = 0 := by
  have pointwise : responseValue displayedLaw = fun _ => (0 : ℝ) := by
    funext response
    exact displayed_column_value response
  rw [pointwise]
  simp

end GameTheory.ReBeL.Examples.ModifiedRPS
