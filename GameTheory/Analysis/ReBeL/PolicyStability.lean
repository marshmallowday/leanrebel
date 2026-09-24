/-
# Behavioral stability from primitive action probabilities

An own-policy change affects bounded complete-history payoffs by at most
horizon times its largest information-local mass distance. Chance and every
other player's policy remain in the canonical execution kernel. The estimate
holds at every legal history, without any posterior or support premise.
-/

import GameTheory.Protocol.Information
import GameTheory.Math.Probability.FinDistMassDistance
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FinCases

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)

/-- Independent joint moves charge only the changing player's action law.
All other players, simultaneous moves and chance retain their original semantics. -/
theorem behavioralJoint_expect_policy_change
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (first second : M.BehavioralPolicy who) (history : E.History)
    (live : ¬ E.terminal history.state)
    (value : {joint : ∀ i, Option (E.Action i) // E.Legal history.state joint} → ℝ)
    (bound : ℝ) (bounded : ∀ joint, |value joint| ≤ bound) :
    |(M.behavioralJoint (Profile.update unknown who first) history.trace live).expect value -
      (M.behavioralJoint (Profile.update unknown who second) history.trace live).expect value| ≤
        bound * FinDist.massDistance (first (M.infoOf who history.trace))
          (second (M.infoOf who history.trace)) := by
  let firstLaws := fun i => Profile.update unknown who first i (M.infoOf i history.trace)
  let secondLaws := fun i => Profile.update unknown who second i (M.infoOf i history.trace)
  let pack := fun draws : (i : Fin 2) → M.Choice i (M.infoOf i history.trace) =>
    (⟨fun i => (draws i).1, ExecutionProtocol.legal_of_legalOption live fun i =>
      (M.menu_adequate i history.trace (draws i).1).mp (draws i).2⟩ :
        {joint : ∀ i, Option (E.Action i) // E.Legal history.state joint})
  have same : ∀ other, other ≠ who → firstLaws other = secondLaws other := by
    intro other different
    simp only [firstLaws, secondLaws, Profile.update_of_ne unknown _ different]
  change |(FinDist.map pack (FinDist.pi firstLaws)).expect value -
    (FinDist.map pack (FinDist.pi secondLaws)).expect value| ≤ _
  rw [FinDist.expect_map, FinDist.expect_map]
  have result := FinDist.abs_expect_pi_sub_le_massDistance firstLaws secondLaws who same
    (fun draws => value (pack draws)) bound (fun draws => bounded (pack draws))
  simpa only [firstLaws, secondLaws, Profile.update_same] using result

/-- One real canonical transition is stable under an own-policy change. -/
theorem runBehavioralFrom_one_policy_change
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (first second : M.BehavioralPolicy who) (history : E.History)
    (value : E.History → ℝ) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ h, |value h| ≤ bound) :
    |(M.runBehavioralFrom (Profile.update unknown who first) 1 history).expect value -
      (M.runBehavioralFrom (Profile.update unknown who second) 1 history).expect value| ≤
        bound * FinDist.massDistance (first (M.infoOf who history.trace))
          (second (M.infoOf who history.trace)) := by
  by_cases terminal : E.terminal history.state
  · rw [M.runBehavioralFrom_of_terminal _ 1 terminal,
      M.runBehavioralFrom_of_terminal _ 1 terminal, sub_self, abs_zero]
    exact mul_nonneg nonneg (FinDist.massDistance_nonneg _ _)
  · let advance := fun draw : {joint : ∀ i, Option (E.Action i) //
        E.Legal history.state joint} =>
      (E.step history.state draw).bindOnSupport fun _ realized =>
        FinDist.pure (history.extend draw.2 realized)
    have result := behavioralJoint_expect_policy_change M unknown who first second history
      terminal (fun draw => (advance draw).expect value) bound
      (fun draw => FinDist.abs_expect_le_of_abs_bound _ value (fun h _ => bounded h))
    rw [M.runBehavioralFrom_succ_of_not_terminal _ 0 terminal,
      M.runBehavioralFrom_succ_of_not_terminal _ 0 terminal,
      FinDist.expect_bind, FinDist.expect_bind]
    exact result

private theorem run_difference_of_step_bound (first second : Profile M.behavioralSignature)
    (value : E.History → ℝ) (bound rate : ℝ) (bounded : ∀ h, |value h| ≤ bound)
    (oneStep : ∀ test : E.History → ℝ, (∀ h, |test h| ≤ bound) → ∀ history,
      |(M.runBehavioralFrom first 1 history).expect test -
        (M.runBehavioralFrom second 1 history).expect test| ≤ bound * rate)
    (fuel : Nat) (history : E.History) :
    |(M.runBehavioralFrom first fuel history).expect value -
      (M.runBehavioralFrom second fuel history).expect value| ≤ bound * fuel * rate := by
  induction fuel generalizing history with
  | zero =>
      simp only [InformationModel.runBehavioralFrom, ExecutionProtocol.runRandomizedFor_zero,
        FinDist.expect_pure, sub_self, abs_zero, Nat.cast_zero, mul_zero, le_refl]
  | succ fuel ih =>
      let prefix := M.runBehavioralFrom first 1 history
      let oldTail := fun h => (M.runBehavioralFrom first fuel h).expect value
      let newTail := fun h => (M.runBehavioralFrom second fuel h).expect value
      have tailBound : |prefix.expect oldTail - prefix.expect newTail| ≤ bound * fuel * rate := by
        rw [← FinDist.expect_sub]
        exact FinDist.abs_expect_le_of_abs_bound _ _ (fun h _ => ih h)
      have headBound := oneStep newTail
        (fun h => FinDist.abs_expect_le_of_abs_bound _ value (fun next _ => bounded next)) history
      calc
        _ = |prefix.expect oldTail -
            (M.runBehavioralFrom second 1 history).expect newTail| := by
          rw [show fuel + 1 = 1 + fuel by omega,
            M.runBehavioralFrom_add, M.runBehavioralFrom_add,
            FinDist.expect_bind, FinDist.expect_bind]
        _ ≤ |prefix.expect oldTail - prefix.expect newTail| +
            |prefix.expect newTail -
              (M.runBehavioralFrom second 1 history).expect newTail| := abs_sub_le _ _ _
        _ ≤ bound * fuel * rate + bound * rate := add_le_add tailBound headBound
        _ = _ := by rw [Nat.cast_add, Nat.cast_one]; ring

variable [Fintype E.History]

/-- Largest action-law distance at information states represented by legal
histories. Duplicate representatives do not inflate the maximum. -/
def behavioralPolicyDistance (who : Fin 2) (first second : M.BehavioralPolicy who) : ℝ :=
  max 0 (Finset.univ.sup' ⟨E.initHistory, Finset.mem_univ _⟩ fun history =>
    FinDist.massDistance (first (M.infoOf who history.trace))
      (second (M.infoOf who history.trace)))

/-- The policy allowance is nonnegative. -/
theorem behavioralPolicyDistance_nonneg (who : Fin 2)
    (first second : M.BehavioralPolicy who) : 0 ≤ behavioralPolicyDistance M who first second :=
  le_max_left _ _

/-- Every actual legal history's local action distance occurs in the finite maximum. -/
theorem massDistance_le_behavioralPolicyDistance (who : Fin 2)
    (first second : M.BehavioralPolicy who) (history : E.History) :
    FinDist.massDistance (first (M.infoOf who history.trace))
        (second (M.infoOf who history.trace)) ≤ behavioralPolicyDistance M who first second :=
  (Finset.le_sup' (f := fun h : E.History =>
      FinDist.massDistance (first (M.infoOf who h.trace)) (second (M.infoOf who h.trace)))
    (Finset.mem_univ history)).trans (le_max_right _ _)

/-- An unchanged own policy has no replacement cost, regardless of the other player. -/
theorem behavioralPolicyDistance_self (who : Fin 2) (policy : M.BehavioralPolicy who) :
    behavioralPolicyDistance M who policy policy = 0 := by
  unfold behavioralPolicyDistance
  simp only [FinDist.massDistance_self, Finset.sup'_const, max_self]

/-- A primitive uniform numerical action-distance bound controls the policy maximum. -/
theorem behavioralPolicyDistance_le (who : Fin 2) (first second : M.BehavioralPolicy who)
    (rate : ℝ) (nonneg : 0 ≤ rate)
    (localBound : ∀ history : E.History,
      FinDist.massDistance (first (M.infoOf who history.trace))
        (second (M.infoOf who history.trace)) ≤ rate) :
    behavioralPolicyDistance M who first second ≤ rate := by
  apply max_le nonneg
  apply Finset.sup'_le
  intro history _
  exact localBound history

/-- All policy distances use the same explicit normalization as finite laws. -/
theorem behavioralPolicyDistance_le_two (who : Fin 2) (first second : M.BehavioralPolicy who) :
    behavioralPolicyDistance M who first second ≤ 2 :=
  behavioralPolicyDistance_le M who first second 2 (by norm_num)
    (fun _ => FinDist.massDistance_le_two _ _)

/-- Full-horizon stability against any fixed unknown opponent, at every legal
history. No equality of model and actual posteriors or common support is used. -/
theorem runBehavioralFrom_policy_stability
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (first second : M.BehavioralPolicy who) (fuel : Nat) (history : E.History)
    (value : E.History → ℝ) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ h, |value h| ≤ bound) :
    |(M.runBehavioralFrom (Profile.update unknown who first) fuel history).expect value -
      (M.runBehavioralFrom (Profile.update unknown who second) fuel history).expect value| ≤
        bound * fuel * behavioralPolicyDistance M who first second := by
  apply run_difference_of_step_bound M _ _ value bound _ bounded
  intro test testBound h
  exact (runBehavioralFrom_one_policy_change M unknown who first second h test bound
    nonneg testBound).trans (mul_le_mul_of_nonneg_left
      (massDistance_le_behavioralPolicyDistance M who first second h) nonneg)

/-- Sum of the two primitive own-policy distances for a full model replacement. -/
def behavioralProfileDistance (first second : Profile M.behavioralSignature) : ℝ :=
  ∑ who, behavioralPolicyDistance M who (first who) (second who)

/-- A full-profile replacement allowance is nonnegative. -/
theorem behavioralProfileDistance_nonneg (first second : Profile M.behavioralSignature) :
    0 ≤ behavioralProfileDistance M first second :=
  Finset.sum_nonneg fun who _ => behavioralPolicyDistance_nonneg M who _ _

/-- Model continuation payoffs are controlled by both players' primitive
policy distances. This is not inferred from scalar equilibrium accuracy. -/
theorem runBehavioralFrom_profile_stability (first second : Profile M.behavioralSignature)
    (fuel : Nat) (history : E.History) (value : E.History → ℝ) (bound : ℝ)
    (nonneg : 0 ≤ bound) (bounded : ∀ h, |value h| ≤ bound) :
    |(M.runBehavioralFrom first fuel history).expect value -
      (M.runBehavioralFrom second fuel history).expect value| ≤
        bound * fuel * behavioralProfileDistance M first second := by
  let middle := Profile.update first 0 (second 0)
  have left := runBehavioralFrom_policy_stability M first 0 (first 0) (second 0)
    fuel history value bound nonneg bounded
  simp only [Profile.update_eq_self] at left
  have right := runBehavioralFrom_policy_stability M middle 1 (middle 1) (second 1)
    fuel history value bound nonneg bounded
  simp only [Profile.update_eq_self] at right
  have finish : Profile.update middle 1 (second 1) = second := by
    funext who
    fin_cases who <;> simp [middle]
  have other : middle 1 = first 1 := by simp [middle]
  rw [finish, other] at right
  calc
    _ ≤ |(M.runBehavioralFrom first fuel history).expect value -
          (M.runBehavioralFrom middle fuel history).expect value| +
        |(M.runBehavioralFrom middle fuel history).expect value -
          (M.runBehavioralFrom second fuel history).expect value| := abs_sub_le _ _ _
    _ ≤ bound * fuel * behavioralPolicyDistance M 0 (first 0) (second 0) +
        bound * fuel * behavioralPolicyDistance M 1 (first 1) (second 1) :=
      add_le_add left right
    _ = _ := by simp only [behavioralProfileDistance, Fin.sum_univ_two]; ring

end GameTheory.ReBeL
