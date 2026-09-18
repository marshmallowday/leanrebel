/-
# Finite PBS-rooted plan games and minimax witnesses

The initial law is the actual joint public belief, not a product of player
marginals. Plans are the existing finite information-local tables. The mixed
extension uses independent player randomization and the original continuation
runner. Behavioral realization is a separate theorem, not silently assumed.
-/

import GameTheory.ReBeL.FiniteSites
import GameTheory.ReBeL.BeliefExecution
import GameTheory.Analysis.Minimax
import GameTheory.Analysis.ReBeL.EquilibriumValue

noncomputable section

namespace GameTheory.ReBeL.PublicBelief

open GameTheory.Protocol GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History]

/-- Assemble a full legal behavioral profile from finite pure plans. -/
def planProfile (fallback : Profile M.strategicSignature)
    (plans : (i : Fin 2) → FinitePlan M i) : Profile M.behavioralSignature :=
  fun i => (FinitePlan.toPolicy M (fallback i) (plans i)).toBehavioral

/-- Finite pure strategies are evaluated by canonical PBS continuation. -/
abbrev planGame (fallback : Profile M.strategicSignature)
    (belief : State M) (fuel : ℕ) : GameForm (Fin 2) where
  sig := { Strategy := FinitePlan M, Outcome := E.History }
  play plans := continuationLaw M (planProfile M fallback plans) fuel belief.2

/-- The pure evaluator retains the full joint root law and original history
outcomes, including chance correlation and terminal roots. -/
theorem planGame_play (fallback : Profile M.strategicSignature)
    (belief : State M) (fuel : ℕ)
    (plans : Profile (planGame M fallback belief fuel).sig) :
    (planGame M fallback belief fuel).play plans =
      belief.2.law.bind (M.runBehavioralFrom (planProfile M fallback plans) fuel) := rfl

/-- Independent mixed plans are drawn once, before the root and continuation.
This is an outcome-law statement, before any utility is chosen. -/
theorem planGame_mixed_play (fallback : Profile M.strategicSignature)
    (belief : State M) (fuel : ℕ)
    (mixed : Profile (planGame M fallback belief fuel).sig.mixed) :
    (planGame M fallback belief fuel).mixed.play mixed =
      (FinDist.pi mixed).bind (fun plans =>
        belief.2.law.bind (M.runBehavioralFrom (planProfile M fallback plans) fuel)) := rfl

/-- The finite PBS plan game has a mixed equilibrium for every history
utility. Finiteness and nonempty legal fallbacks are supplied explicitly. -/
theorem exists_planGame_nash [∀ i, Fintype (E.Action i)]
    (fallback : Profile M.strategicSignature) (belief : State M) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) :
    ∃ mixed : Profile (planGame M fallback belief fuel).sig.mixed,
      IsNash (planGame M fallback belief fuel).mixed (euPreference utility) mixed := by
  let : ∀ i, Fintype (FinitePlan M i) := fun i => finitePlanFintype M i
  let : ∀ i, Nonempty (FinitePlan M i) := fun i => ⟨fun info => fallback i info.1⟩
  exact exists_isNash_mixed (F := planGame M fallback belief fuel) utility

/-- The existing minimax theorem applies to this concrete PBS-rooted game,
not to an unrelated supplied payoff matrix. The quantifiers cover every
mixed finite plan deviation for either player. -/
theorem exists_planGame_value [∀ i, Fintype (E.Action i)]
    (fallback : Profile M.strategicSignature) (belief : State M) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility) :
    ∃ (value : ℝ) (mixed : Profile (planGame M fallback belief fuel).sig.mixed),
      (∀ row, expectedUtility utility 0
        ((planGame M fallback belief fuel).mixed.play (Profile.update mixed 0 row)) ≤ value) ∧
      (∀ column, value ≤ expectedUtility utility 0
        ((planGame M fallback belief fuel).mixed.play (Profile.update mixed 1 column))) ∧
      ∀ other, IsSaddlePoint (F := planGame M fallback belief fuel) utility other →
        expectedUtility utility 0 ((planGame M fallback belief fuel).mixed.play other) = value := by
  let : ∀ i, Fintype (FinitePlan M i) := fun i => finitePlanFintype M i
  let : ∀ i, Nonempty (FinitePlan M i) := fun i => ⟨fun info => fallback i info.1⟩
  exact exists_value (F := planGame M fallback belief fuel) utility hzero

/-- Equilibrium nonuniqueness does not make the PBS plan-game value ambiguous. -/
theorem planGame_nash_value_eq (fallback : Profile M.strategicSignature)
    (belief : State M) (fuel : ℕ) (utility : E.History → Fin 2 → ℝ)
    (hzero : IsZeroSum utility)
    (first second : Profile (planGame M fallback belief fuel).sig.mixed)
    (hfirst : IsNash (planGame M fallback belief fuel).mixed (euPreference utility) first)
    (hsecond : IsNash (planGame M fallback belief fuel).mixed (euPreference utility) second) :
    expectedUtility utility 0 ((planGame M fallback belief fuel).mixed.play first) =
      expectedUtility utility 0 ((planGame M fallback belief fuel).mixed.play second) :=
  nash_value_eq (planGame M fallback belief fuel).mixed utility hzero first second hfirst hsecond

end GameTheory.ReBeL.PublicBelief
