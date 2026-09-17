/-
# Card compatibility and a nonuniform Bayes update

The fixed chance factor enforces sampling without replacement. Local reach
factors never authorize a duplicate card. A two-card example computes the
posterior (2/3, 1/3), and the exclusion theorem applies to arbitrary finite decks.
-/

import GameTheory.ReBeL.BeliefStatistic
import Mathlib.Tactic.NormNum

noncomputable section

namespace GameTheory.ReBeL.Examples.CompactCards

open GameTheory.Math.Probability
open scoped BigOperators

/-- A fixed unnormalized chance factor for an ordered pair of distinct cards. -/
def distinctCards (n : Nat) : ReachWeights (Fin n × Fin n) where
  weight cards := if cards.1 = cards.2 then 0 else 1
  nonneg cards := by split <;> norm_num

/-- The local private observation contains only the owner's card. -/
def observe (n : Nat) (i : Fin 2) (cards : Fin n × Fin n) : Fin n :=
  if i = 0 then cards.1 else cards.2

/-- Any normalized compatibility-aware encoding rules out duplicate cards. -/
theorem no_duplicate (n : Nat) (factors : Fin 2 → ReachWeights (Fin n))
    (positive : 0 < (ReachEncoding.joint (distinctCards n) (observe n) factors).mass)
    (card : Fin n) :
    ((ReachEncoding.joint (distinctCards n) (observe n) factors).normalize positive).prob
      (card, card) = 0 := by
  apply ReachEncoding.incompatible_prob_zero
  simp [distinctCards]

/-- In the two-card calculation, one observed action is twice as likely with card zero. -/
def actionFactors (i : Fin 2) : ReachWeights (Fin 2) where
  weight card := if i = 0 then if card = 0 then 1 else 1 / 2 else 1
  nonneg card := by split <;> split_ifs <;> norm_num

/-- These are valid likelihood factors in [0,1], not arbitrary large potentials. -/
theorem actionFactors_le_one (i card : Fin 2) : (actionFactors i).weight card ≤ 1 := by
  unfold actionFactors
  split_ifs <;> norm_num

/-- The fixed chance and local likelihood factors are decoded jointly. -/
def updatedWeights : ReachWeights (Fin 2 × Fin 2) :=
  ReachEncoding.joint (distinctCards 2) (observe 2) actionFactors

theorem updated_mass : updatedWeights.mass = 3 / 2 := by
  norm_num [updatedWeights, ReachWeights.mass, ReachEncoding.joint, distinctCards,
    observe, actionFactors, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.prod_univ_two]

/-- A certified positive normalizer, so no division-by-zero convention is used. -/
theorem updated_positive : 0 < updatedWeights.mass := by rw [updated_mass]; norm_num

def posterior : FinDist (Fin 2 × Fin 2) := updatedWeights.normalize updated_positive

/-- Exact nonuniform posterior and both forbidden diagonal events. -/
theorem posterior_probabilities :
    posterior.prob (0, 1) = 2 / 3 ∧ posterior.prob (1, 0) = 1 / 3 ∧
      posterior.prob (0, 0) = 0 ∧ posterior.prob (1, 1) = 0 := by
  norm_num [posterior, ReachWeights.prob_normalize, updated_mass, updatedWeights,
    ReachEncoding.joint, distinctCards, observe, actionFactors, Fin.prod_univ_two]

/-- The paper's three-action prescription has 156 probabilities per acting player. -/
theorem one_card_prescription_slots : Fintype.card (Fin 52 × Fin 3) = 156 := by norm_num

/-- The two local belief/reach vectors have 104 entries; the chance constraint is extra data. -/
theorem two_card_vector_slots : Fintype.card (Fin 52 ⊕ Fin 52) = 104 :=
  ReachEncoding.card_variable_slots

/-- Zero total reach yields no normalized probability law. -/
theorem zero_reach_has_no_posterior :
    (ReachWeights.normalize? (⟨fun _ : Fin 2 => 0, fun _ => le_rfl⟩ : ReachWeights (Fin 2))) =
      none := by
  rw [ReachWeights.normalize?_eq_none]
  simp [ReachWeights.mass]

end GameTheory.ReBeL.Examples.CompactCards
