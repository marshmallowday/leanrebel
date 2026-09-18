/-
# Characterizing every minimizing PBS opponent

The minimum in Lemma 2 is not merely attained by one selected equilibrium.
Its complete argmin is exactly the set of opponent components that occur in
canonical behavioral Nash equilibria. The proof reuses the legal conditional
best-response construction and zero-sum security, without uniqueness assumptions.
-/

import GameTheory.Analysis.ReBeL.PBSValue

noncomputable section

namespace GameTheory.ReBeL.TypeBeliefSlice

open GameTheory.Protocol GameTheory.Math.Probability

universe us ua up uq uk ut
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable {M : InformationModel.{0, us, ua, up, uq, uk} E}
variable [Fintype E.History] [∀ i, Fintype (E.Action i)]
variable {observations : List M.PublicSignal} {who : Fin 2} {T : Type ut}
variable (slice : TypeBeliefSlice M observations who T)

/-- A fixed-opponent branch depends only on the opponent coordinate, not on
the unused own component of its profile argument. -/
theorem branch_eq_of_other_eq (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : ℕ) (payoff : E.History → ℝ)
    (own : FinDist T) (left right : Profile M.behavioralSignature)
    (same : left (otherPlayer who) = right (otherPlayer who)) :
    slice.branch fallback fuel payoff own left = slice.branch fallback fuel payoff own right := by
  have functions :
      (fun replacement : M.BehavioralPolicy who =>
        (PublicBelief.continuationLaw M (Profile.update left who replacement)
          fuel (slice.mixture own)).expect payoff) =
      (fun replacement : M.BehavioralPolicy who =>
        (PublicBelief.continuationLaw M (Profile.update right who replacement)
          fuel (slice.mixture own)).expect payoff) := by
    funext replacement
    rw [update_self_congr_of_other_eq left right who same replacement]
  have hleft := slice.branch_isGreatest hrecall fallback fuel payoff own left
  have hright := slice.branch_isGreatest hrecall fallback fuel payoff own right
  rw [functions] at hleft
  exact le_antisymm (hright.2 hleft.1) (hleft.2 hright.1)

/-- Pair any minimizing opponent with the own part of an existing equilibrium.
Both players' arbitrary behavioral deviations remain unprofitable. -/
theorem minimizing_opponent_isNash (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility)
    (own : FinDist T) (opponents : Profile M.behavioralSignature)
    (optimal : slice.branch fallback fuel (fun history => utility history who) own opponents =
      slice.value hrecall clock fallback fuel utility own) :
    IsNash (behavioralBeliefForm M (slice.mixture own) fuel) (euPreference utility)
      (Profile.update opponents who
        (publicBeliefEquilibrium M hrecall clock fallback (slice.mixture own) fuel utility who)) := by
  let form := behavioralBeliefForm M (slice.mixture own) fuel
  let base := publicBeliefEquilibrium M hrecall clock fallback (slice.mixture own) fuel utility
  let candidate := Profile.update opponents who (base who)
  have equilibrium : IsNash form (euPreference utility) base :=
    publicBeliefEquilibrium_isNash M hrecall clock fallback (slice.mixture own) fuel utility
  have security := nash_security form utility hzero base equilibrium who
    (opponents (otherPlayer who))
  rw [update_other_eq_update_self] at security
  have capped := slice.payoff_le_branch hrecall fallback fuel
    (fun history => utility history who) own opponents (base who)
  rw [optimal] at capped
  have hpayoff : expectedUtility utility who (form.play candidate) =
      slice.value hrecall clock fallback fuel utility own := le_antisymm capped security
  rw [isNash_iff]
  intro player replacement
  rcases player_eq_self_or_other who player with rfl | rfl
  · rw [euPreference_apply]
    calc
      _ = expectedUtility utility who
          (form.play (Profile.update opponents who replacement)) := by
        rw [Profile.update_idem]
      _ ≤ slice.branch fallback fuel (fun history => utility history who) own opponents :=
        slice.payoff_le_branch hrecall fallback fuel _ own opponents replacement
      _ = expectedUtility utility who (form.play candidate) := optimal.trans hpayoff.symm
  · rw [euPreference_apply, expectedUtility_other utility hzero,
      expectedUtility_other utility hzero]
    apply neg_le_neg
    have same : Profile.update candidate (otherPlayer who) replacement =
        Profile.update base (otherPlayer who) replacement := by
      funext player
      rcases player_eq_self_or_other who player with rfl | rfl
      · rw [Profile.update_of_ne _ _ (otherPlayer_ne who).symm,
          Profile.update_of_ne _ _ (otherPlayer_ne who).symm]
        exact Profile.update_same opponents who (base who)
      · rw [Profile.update_same, Profile.update_same]
    rw [same, hpayoff]
    exact nash_security form utility hzero base equilibrium who replacement

/-- The complete argmin in Lemma 2 is precisely the opponent projection of
the equilibrium set. This includes nonunique minimizing opponents. -/
theorem branch_eq_value_iff_equilibriumOpponent
    (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility)
    (own : FinDist T) (opponents : Profile M.behavioralSignature) :
    slice.branch fallback fuel (fun history => utility history who) own opponents =
        slice.value hrecall clock fallback fuel utility own ↔
      ∃ profile : Profile M.behavioralSignature,
        IsNash (behavioralBeliefForm M (slice.mixture own) fuel) (euPreference utility) profile ∧
          profile (otherPlayer who) = opponents (otherPlayer who) := by
  constructor
  · intro optimal
    exact ⟨Profile.update opponents who
      (publicBeliefEquilibrium M hrecall clock fallback (slice.mixture own) fuel utility who),
      slice.minimizing_opponent_isNash hrecall clock fallback fuel utility hzero own opponents optimal,
      Profile.update_of_ne _ _ (otherPlayer_ne who)⟩
  · rintro ⟨profile, equilibrium, same⟩
    rw [slice.branch_eq_of_other_eq hrecall fallback fuel _ own opponents profile same.symm]
    exact slice.branch_eq_value_of_nash hrecall clock fallback fuel utility hzero own profile equilibrium

end GameTheory.ReBeL.TypeBeliefSlice
