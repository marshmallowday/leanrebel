/-
# Resampling and coordinate averaging are not carried-iteration execution

This hostile control uses a genuine hidden-type history with different own
first and second actions. A fixed private iteration cannot produce it. Fresh
per-information-state mixing can, despite identical local marginal seed laws.
-/

import GameTheory.Analysis.ReBeL.CFRDCarriedPlay
import GameTheory.Analysis.ReBeL.Examples.RationalReach

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- One bit fixes both of the focal player's strategic actions. -/
def carriedBitPlan (bit : Bool) : Plan where
  first _ := bit
  second _ _ := bit

/-- Both policies remain information-local; the seed is selected outside play. -/
def carriedBitProfile (bit : Bool) : Profile (model fullPrior).behavioralSignature :=
  fun who => (fullPlanPolicy fullPrior who (carriedBitPlan bit)).toBehavioral

/-- A fair private iteration bit, independent of the game's private type draw. -/
def carriedBitLaw : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) (FinDist.pure false) (FinDist.pure true)

/-- Player one always chooses true and does not observe the private seed. -/
def carriedBitOpponent : Profile (model fullPrior).behavioralSignature := carriedBitProfile true

/-- The intentionally wrong coordinate average resamples at each information state. -/
def freshBitPolicy : (model fullPrior).BehavioralPolicy 0 := fun info =>
  carriedBitLaw.bind fun bit => carriedBitProfile bit 0 info

/-- A legal complete history whose focal actions disagree between stages. -/
def carriedBitWitness : (protocol fullPrior).History :=
  decode (.finished false false false true true true)

private theorem witness_chance : outcomeChanceWeight 3 carriedBitWitness = 1 / 4 := by
  unfold outcomeChanceWeight
  rw [if_pos (by exact ⟨by decide, Or.inl rfl⟩)]
  unfold carriedBitWitness
  rw [← chanceReach_correct (.finished false false false true true true)]
  norm_num [GameTheory.ReBeL.Rational.HiddenTypes.table,
    GameTheory.ReBeL.Rational.HiddenTypes.chanceFactors]

private theorem witness_reach (strategy : Profile (model fullPrior).behavioralSignature)
    (who : Player) :
    (model fullPrior).playerReachProbability strategy who carriedBitWitness.trace =
      (strategy who ((model fullPrior).infoOf who (decode (.drawn false false)).trace)).prob
          (rowChoiceEquiv who (.drawn false false)
            (GameTheory.ReBeL.Rational.HiddenTypes.own who false true)) *
        (strategy who ((model fullPrior).infoOf who
          (decode (.second false false false true)).trace)).prob
          (rowChoiceEquiv who (.second false false false true) true) := by
  rw [carriedBitWitness, playerReach_finished, playerReach_second]
  congr 2
  rcases (by decide : ∀ player : Fin 2, player = 0 ∨ player = 1) who with rfl | rfl <;> rfl

private theorem bit_draw_prob (bit : Bool) (who : Player) (a : Bool) :
    (carriedBitProfile bit who ((model fullPrior).infoOf who
      (decode (.drawn false false)).trace)).prob
      (rowChoiceEquiv who (.drawn false false) a) = if a = bit then 1 else 0 := by
  dsimp only [carriedBitProfile, Policy.toBehavioral]
  rw [FinDist.prob_pure_eq_ite]
  have eq : rowChoiceEquiv who (.drawn false false) a =
      fullPlanPolicy fullPrior who (carriedBitPlan bit)
        ((model fullPrior).infoOf who (decode (.drawn false false)).trace) ↔ a = bit := by
    constructor
    · intro h
      exact Option.some.inj (congrArg Subtype.val h)
    · intro h
      subst a
      rfl
  by_cases h : a = bit
  · rw [if_pos (eq.mpr h), if_pos h]
  · rw [if_neg (fun equal => h (eq.mp equal)), if_neg h]

private theorem bit_second_prob (bit : Bool) (who : Player) (a : Bool) :
    (carriedBitProfile bit who ((model fullPrior).infoOf who
      (decode (.second false false false true)).trace)).prob
      (rowChoiceEquiv who (.second false false false true) a) = if a = bit then 1 else 0 := by
  dsimp only [carriedBitProfile, Policy.toBehavioral]
  rw [FinDist.prob_pure_eq_ite]
  have eq : rowChoiceEquiv who (.second false false false true) a =
      fullPlanPolicy fullPrior who (carriedBitPlan bit)
        ((model fullPrior).infoOf who (decode (.second false false false true)).trace) ↔
      a = bit := by
    constructor
    · intro h
      exact Option.some.inj (congrArg Subtype.val h)
    · intro h
      subst a
      rfl
  by_cases h : a = bit
  · rw [if_pos (eq.mpr h), if_pos h]
  · rw [if_neg (fun equal => h (eq.mp equal)), if_neg h]

/-- Under either complete selected policy the mismatch history is impossible. -/
theorem carriedBit_fixed_zero (bit : Bool) :
    ((model fullPrior).runBehavioral
      (Profile.update carriedBitOpponent 0 (carriedBitProfile bit 0)) 3).prob
        carriedBitWitness = 0 := by
  rw [run_probability_factorization (model fullPrior), witness_chance, Fin.prod_univ_two,
    witness_reach, witness_reach]
  simp only [Profile.update_same, Profile.update_of_ne _ _ (by decide : (1 : Fin 2) ≠ 0),
    carriedBitOpponent]
  rw [bit_draw_prob, bit_draw_prob, bit_second_prob, bit_second_prob]
  cases bit <;> norm_num [GameTheory.ReBeL.Rational.HiddenTypes.own]

/-- Arithmetic local mixing puts positive mass on the exact same legal history. -/
theorem carriedBit_fresh_positive :
    ((model fullPrior).runBehavioral (Profile.update carriedBitOpponent 0 freshBitPolicy) 3).prob
      carriedBitWitness = 1 / 16 := by
  rw [run_probability_factorization (model fullPrior), witness_chance, Fin.prod_univ_two,
    witness_reach, witness_reach]
  simp only [Profile.update_same, Profile.update_of_ne _ _ (by decide : (1 : Fin 2) ≠ 0),
    carriedBitOpponent, freshBitPolicy, FinDist.prob_bind]
  rw [bit_draw_prob, bit_second_prob]
  simp only [carriedBitLaw, FinDist.expect_mix, FinDist.expect_pure]
  rw [bit_draw_prob, bit_draw_prob, bit_second_prob, bit_second_prob]
  norm_num [GameTheory.ReBeL.Rational.HiddenTypes.own]

/-- The actual carried-state execution is not the coordinate-average policy. -/
theorem carriedBit_resampling_changes_law :
    privateCarriedContinue (model fullPrior) carriedBitLaw carriedBitProfile
        carriedBitOpponent 0 2 1 ≠
      (model fullPrior).runBehavioral (Profile.update carriedBitOpponent 0 freshBitPolicy) 3 := by
  intro same
  have h := congrArg (fun law => law.prob carriedBitWitness) same
  rw [privateCarriedContinue_eq, privateIterationLaw, FinDist.prob_bind] at h
  have zero : (carriedBitLaw.expect fun bit =>
      ((model fullPrior).runBehavioral
        (Profile.update carriedBitOpponent 0 (carriedBitProfile bit 0)) 3).prob
          carriedBitWitness) = 0 := by
    calc
      _ = carriedBitLaw.expect (fun _ => (0 : ℝ)) :=
        FinDist.expect_congr (fun bit _ => carriedBit_fixed_zero bit)
      _ = 0 := FinDist.expect_const _ _
  rw [zero, carriedBit_fresh_positive] at h
  norm_num at h

end GameTheory.ReBeL.Examples.HiddenTypes
