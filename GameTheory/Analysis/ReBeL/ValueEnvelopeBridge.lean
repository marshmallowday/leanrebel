/-
# Extending finite type-game values to the whole vector space

The matrix value outside the nonnegative cone is not the desired extension:
negative type weights reverse a typewise maximization. Instead, extend the
lower envelope of the same opponent-indexed best-response branches. Finite
payoffs bound those branches on every signed vector, so the resulting concave
extension is real-valued everywhere, including neighborhoods of boundary
beliefs. It is different from Appendix F's degree-zero radial normalization.
-/

import GameTheory.Analysis.ReBeL.ValueEnvelope
import GameTheory.Analysis.ReBeL.ValueGeometry

noncomputable section

namespace GameTheory.ReBeL.TypeGame

open GameTheory.Math.Probability

universe u
variable {T B : Type u} [Fintype T] [DecidableEq T] [Fintype B] [Nonempty B]
variable {Action : T → Type u}
variable [∀ t, Fintype (Action t)] [∀ t, Nonempty (Action t)]
variable (payoff : (t : T) → Action t → B → ℝ)

omit [DecidableEq T] [Nonempty B] [∀ t, Nonempty (Action t)] in
/-- Finite conditional payoff tables supply a uniform bound; boundedness is
not an extra assumption on equilibrium selections or on mixed opponents. -/
theorem exists_payoff_abs_bound : ∃ bound : ℝ, ∀ t action opponent,
    |payoff t action opponent| ≤ bound := by
  obtain ⟨bound, bounded⟩ := (Set.finite_range fun entry : (Σ t, Action t) × B =>
    |payoff entry.1.1 entry.1.2 entry.2|).bddAbove
  exact ⟨bound, fun t action opponent => bounded ⟨⟨⟨t, action⟩, opponent⟩, rfl⟩⟩

omit [Fintype T] [DecidableEq T] [Fintype B] [Nonempty B] in
/-- An attaining type best response remains within the original payoff bound,
including types whose current probability is zero. -/
theorem infoValue_abs_le (bound : ℝ)
    (bounded : ∀ t action opponent, |payoff t action opponent| ≤ bound)
    (opponent : FinDist B) (t : T) : |infoValue payoff opponent t| ≤ bound := by
  apply abs_le.mpr
  constructor
  · calc
      -bound = opponent.expect (fun _ => -bound) := (FinDist.expect_const _ _).symm
      _ ≤ infoValue payoff opponent t := FinDist.expect_mono fun current _ =>
        (abs_le.mp (bounded t (typeResponse payoff opponent t) current)).1
  · exact FinDist.expect_le_of_forall opponent _ bound fun current _ =>
      (abs_le.mp (bounded t (typeResponse payoff opponent t) current)).2

omit [DecidableEq T] [Nonempty B] in
/-- The same finite bound works simultaneously for all mixed opponents. -/
theorem exists_infoValue_abs_bound : ∃ bound : ℝ,
    ∀ (opponent : FinDist B) t, |infoValue payoff opponent t| ≤ bound := by
  obtain ⟨bound, bounded⟩ := exists_payoff_abs_bound payoff
  exact ⟨bound, infoValue_abs_le payoff bound bounded⟩

omit [DecidableEq T] [Nonempty B] in
/-- Uniformly bounded conditional values make the lower envelope finite at
all signed weight vectors, not only normalized or positive weights. -/
theorem branches_bounded_below (point : T → ℝ) :
    BddBelow (Set.range fun opponent : FinDist B =>
      ValueGeometry.pairing (infoValue payoff opponent) point) := by
  obtain ⟨bound, bounded⟩ := exists_infoValue_abs_bound payoff
  exact ValueGeometry.bounded_below_of_abs_bound (infoValue payoff) bound bounded point

/-- On nonnegative weights the lower envelope is exactly the canonical
finite-game value, by minimax attainment proved in `TypeValue`. -/
theorem envelope_eq_value (weight : T → ℝ) (nonnegative : ∀ t, 0 ≤ weight t) :
    ValueGeometry.envelope (infoValue payoff) weight = value payoff weight :=
  (value_isLeast payoff weight nonnegative).csInf_eq

/-- A real-valued extension on the full ambient vector space. The affine
correction fixes the normal component at the chosen base belief. -/
def allSpaceExtension (base point : T → ℝ) : ℝ :=
  ValueGeometry.extension (infoValue payoff) (value payoff base) point

/-- The extension agrees with the game value on the entire probability
simplex, not merely near a chosen fully supported belief. -/
theorem allSpaceExtension_eq_on_simplex (base : T → ℝ) :
    Set.EqOn (allSpaceExtension payoff base) (value payoff) (stdSimplex ℝ T) := by
  intro point hpoint
  rw [allSpaceExtension, ValueGeometry.extension_eq_of_mass_one _ _ _ hpoint.2,
    envelope_eq_value payoff point hpoint.1]

/-- Concavity on all signed vectors also supplies genuine neighborhoods at
boundary beliefs. No extension by the negative-weight matrix value is used. -/
theorem allSpaceExtension_concave (base : T → ℝ) :
    ConcaveOn ℝ Set.univ (allSpaceExtension payoff base) := by
  let : Nonempty (FinDist B) := ⟨FinDist.pure (Classical.choice ‹Nonempty B›)⟩
  exact ValueGeometry.extension_concave (infoValue payoff) (value payoff base)
    (branches_bounded_below payoff)

/-- Every minimizing opponent, not only the selected one, supplies global
support for the same base-anchored extension. -/
theorem allSpaceExtension_support {base : T → ℝ} (hbase : base ∈ stdSimplex ℝ T)
    (opponent : FinDist B) (optimal : branch payoff base opponent = value payoff base)
    (point : T → ℝ) :
    allSpaceExtension payoff base point ≤ allSpaceExtension payoff base base +
      ∑ t, centeredVector payoff base opponent t * (point t - base t) := by
  have atBase := envelope_eq_value payoff base hbase.1
  have active : ValueGeometry.envelope (infoValue payoff) base =
      ValueGeometry.pairing (infoValue payoff opponent) base := atBase.trans optimal.symm
  have supporting := ValueGeometry.centered_support (infoValue payoff)
    (branches_bounded_below payoff) base hbase.2 opponent active point
  rw [atBase] at supporting
  simpa only [allSpaceExtension, ValueGeometry.pairing, Pi.sub_apply, centeredVector,
    mul_comm] using supporting

/-- Theorem 1's existential-extension interpretation, strengthened to all
real own-weight vectors. It includes boundary and nonunique equilibria while
making no false claim about the normalized extension in the supplement. -/
theorem theorem1_allSpaceExtension {base : T → ℝ} (hbase : base ∈ stdSimplex ℝ T)
    (opponent : FinDist B) (optimal : branch payoff base opponent = value payoff base) :
    ∃ extension : (T → ℝ) → ℝ,
      Set.EqOn extension (value payoff) (stdSimplex ℝ T) ∧
      ConcaveOn ℝ Set.univ extension ∧
      (∀ point : T → ℝ, extension point ≤ extension base +
        ∑ t, centeredVector payoff base opponent t * (point t - base t)) ∧
      (∀ t, infoValue payoff opponent t =
        value payoff base + centeredVector payoff base opponent t) := by
  exact ⟨allSpaceExtension payoff base, allSpaceExtension_eq_on_simplex payoff base,
    allSpaceExtension_concave payoff base,
    allSpaceExtension_support payoff hbase opponent optimal,
    infoValue_eq_value_add_centered payoff base opponent⟩

end GameTheory.ReBeL.TypeGame
