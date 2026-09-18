/-
# Attaining opponents are exactly Nash-equilibrium policies

This closes the converse in Lemma 2 for the actual PBS runner. A minimizing
opponent is paired with an existing equilibrium row policy. The proof checks
every unilateral behavioral deviation and does not incorrectly pair the
opponent with an arbitrary best response.
-/

import GameTheory.Analysis.ReBeL.PBSValue

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel GameTheory.Math.Probability

/-- Fixing the same opponent and the same replacement produces the same
profile, independently of the unused original own coordinate. -/
theorem sameOpponent_update (signature : GameSignature (Fin 2))
    (first second : Profile signature) (same : first 1 = second 1)
    (replacement : signature.Strategy 0) :
    Profile.update first 0 replacement = Profile.update second 0 replacement := by
  funext who
  rcases (by decide : ∀ who : Fin 2, who = 0 ∨ who = 1) who with rfl | rfl
  · rw [Profile.update_same, Profile.update_same]
  · simpa only [Profile.update_of_ne _ _ (by decide : (1 : Fin 2) ≠ 0)] using same

/-- An opponent bounding every row by the equilibrium value is itself a Nash
policy. The existing equilibrium row, rather than an arbitrary best response,
provides the compatible partner. -/
theorem nash_replaceOpponent_of_upper_bound (form : GameForm (Fin 2))
    (utility : form.sig.Outcome → Fin 2 → ℝ) (hzero : IsZeroSum utility)
    (reference opponents : Profile form.sig)
    (equilibrium : IsNash form (euPreference utility) reference)
    (upper : ∀ replacement : form.sig.Strategy 0,
      expectedUtility utility 0 (form.play (Profile.update opponents 0 replacement)) ≤
        expectedUtility utility 0 (form.play reference)) :
    IsNash form (euPreference utility) (Profile.update reference 1 (opponents 1)) := by
  let joined := Profile.update reference 1 (opponents 1)
  have cross : joined = Profile.update opponents 0 (reference 0) := by
    funext who
    rcases (by decide : ∀ who : Fin 2, who = 0 ∨ who = 1) who with rfl | rfl
    · simp only [joined, Profile.update_of_ne _ _ (by decide : (0 : Fin 2) ≠ 1),
        Profile.update_same]
    · simp only [joined, Profile.update_of_ne _ _ (by decide : (1 : Fin 2) ≠ 0),
        Profile.update_same]
  have guaranteed (replacement : form.sig.Strategy 1) :
      expectedUtility utility 0 (form.play reference) ≤
        expectedUtility utility 0 (form.play (Profile.update reference 1 replacement)) := by
    have bound : expectedUtility utility 1
        (form.play (Profile.update reference 1 replacement)) ≤
          expectedUtility utility 1 (form.play reference) :=
      (isNash_iff reference).mp equilibrium 1 replacement
    rw [hzero.expectedUtility_one, hzero.expectedUtility_one] at bound
    linarith
  have joinedValue : expectedUtility utility 0 (form.play joined) =
      expectedUtility utility 0 (form.play reference) := by
    apply le_antisymm
    · rw [cross]
      exact upper (reference 0)
    · exact guaranteed (opponents 1)
  have sameRow (replacement : form.sig.Strategy 0) :
      Profile.update joined 0 replacement = Profile.update opponents 0 replacement :=
    sameOpponent_update form.sig joined opponents (Profile.update_same _ _ _) replacement
  have sameColumn (replacement : form.sig.Strategy 1) :
      Profile.update joined 1 replacement = Profile.update reference 1 replacement := by
    funext who
    rcases (by decide : ∀ who : Fin 2, who = 0 ∨ who = 1) who with rfl | rfl
    · simp only [joined, Profile.update_of_ne _ _ (by decide : (0 : Fin 2) ≠ 1)]
    · rw [Profile.update_same, Profile.update_same]
  show IsNash form (euPreference utility) joined
  rw [isNash_iff]
  intro who replacement
  rcases (by decide : ∀ who : Fin 2, who = 0 ∨ who = 1) who with rfl | rfl
  · rw [euPreference_apply, sameRow]
    exact (upper replacement).trans_eq joinedValue.symm
  · rw [euPreference_apply, hzero.expectedUtility_one, hzero.expectedUtility_one,
      sameColumn, joinedValue]
    exact neg_le_neg (guaranteed replacement)

namespace TypeBeliefSlice

universe us ua up uq uk ut
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable {M : InformationModel.{0, us, ua, up, uq, uk} E}
variable [Fintype E.History] [∀ i, Fintype (E.Action i)]
variable {observations : List M.PublicSignal} {T : Type ut}
variable (slice : TypeBeliefSlice M observations 0 T)

/-- The branch depends only on the opponent, not the unused own coordinate
of the full profile used to represent it. -/
theorem branch_eq_of_sameOpponent (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : ℕ) (payoff : E.History → ℝ)
    (own : FinDist T) (first second : Profile M.behavioralSignature)
    (same : first 1 = second 1) :
    slice.branch fallback fuel payoff own first =
      slice.branch fallback fuel payoff own second := by
  have equality : (fun replacement : M.BehavioralPolicy 0 =>
      (PublicBelief.continuationLaw M (Profile.update first 0 replacement)
        fuel (slice.mixture own)).expect payoff) =
      (fun replacement : M.BehavioralPolicy 0 =>
        (PublicBelief.continuationLaw M (Profile.update second 0 replacement)
          fuel (slice.mixture own)).expect payoff) := by
    funext replacement
    rw [sameOpponent_update M.behavioralSignature first second same replacement]
  have greatest := slice.branch_isGreatest hrecall fallback fuel payoff own first
  rw [equality] at greatest
  exact greatest.unique (slice.branch_isGreatest hrecall fallback fuel payoff own second)

variable [Fintype T]

/-- Lemma 2, including its converse: the minimizing behavioral opponents are
precisely those that occur in a canonical PBS Nash equilibrium. -/
theorem branch_eq_value_iff_nashOpponent (hrecall : M.PerfectRecall)
    (clock : ObservationClock M) (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility) (own : FinDist T)
    (opponents : Profile M.behavioralSignature) :
    slice.branch fallback fuel (fun history => utility history 0) own opponents =
        slice.value fallback fuel (fun history => utility history 0) own.prob ↔
      ∃ profile : Profile M.behavioralSignature,
        IsNash (behavioralBeliefForm M (slice.mixture own) fuel) (euPreference utility) profile ∧
          profile 1 = opponents 1 := by
  constructor
  · intro optimal
    obtain ⟨reference, equilibrium⟩ := exists_publicBelief_nash M hrecall clock fallback
      (slice.mixture own) fuel utility
    have valueAt := slice.value_eq_equilibriumPayoff hrecall fallback fuel utility hzero
      own reference equilibrium
    refine ⟨Profile.update reference 1 (opponents 1), ?_, Profile.update_same _ _ _⟩
    apply nash_replaceOpponent_of_upper_bound
      (behavioralBeliefForm M (slice.mixture own) fuel) utility hzero
        reference opponents equilibrium
    intro replacement
    exact (slice.payoff_le_branch hrecall fallback fuel
      (fun history => utility history 0) own opponents replacement).trans_eq
        (optimal.trans valueAt)
  · rintro ⟨profile, equilibrium, same⟩
    rw [slice.branch_eq_of_sameOpponent hrecall fallback fuel
      (fun history => utility history 0) own opponents profile same.symm]
    exact (slice.branch_eq_equilibriumPayoff hrecall fallback fuel utility
      own profile equilibrium).trans (slice.value_eq_equilibriumPayoff hrecall fallback fuel
        utility hzero own profile equilibrium).symm

end TypeBeliefSlice
end GameTheory.ReBeL
