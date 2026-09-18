/-
# Canonical PBS value and attained minimax

Existence is obtained from the finite legal-plan construction. Uniqueness is
M04's canonical zero-sum Nash theorem. Conditional maxima and simultaneous
attainment are the actual PBS runner results from PBSInfoValue. These three
independent proofs yield Lemma 2 without assuming a minimax certificate.
-/

import GameTheory.Analysis.ReBeL.BeliefExistence
import GameTheory.Analysis.ReBeL.PBSInfoValue
import GameTheory.Analysis.ReBeL.EquilibriumValue

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Math.Probability

/-- The other player in a genuinely two-player game. -/
def otherPlayer (who : Fin 2) : Fin 2 := if who = 0 then 1 else 0

/-- A player is different from their opponent. -/
theorem otherPlayer_ne (who : Fin 2) : otherPlayer who ≠ who := by
  fin_cases who <;> decide

/-- There is no third coordinate in a two-player strategy profile. -/
theorem player_eq_self_or_other (who player : Fin 2) :
    player = who ∨ player = otherPlayer who := by
  fin_cases who <;> fin_cases player <;> decide

/-- Cross-playing two profiles is the same unilateral update viewed from
either side. This uses the canonical dependent strategy profile. -/
theorem update_other_eq_update_self {signature : GameSignature (Fin 2)}
    (left right : Profile signature) (who : Fin 2) :
    Profile.update left (otherPlayer who) (right (otherPlayer who)) =
      Profile.update right who (left who) := by
  funext player
  rcases player_eq_self_or_other who player with rfl | rfl
  · rw [Profile.update_of_ne _ _ (otherPlayer_ne who).symm, Profile.update_same]
  · rw [Profile.update_same, Profile.update_of_ne _ _ (otherPlayer_ne who)]

/-- If opponents are equal, every own replacement produces the same profile. -/
theorem update_self_congr_of_other_eq {signature : GameSignature (Fin 2)}
    (left right : Profile signature) (who : Fin 2)
    (same : left (otherPlayer who) = right (otherPlayer who))
    (replacement : signature.Strategy who) :
    Profile.update left who replacement = Profile.update right who replacement := by
  funext player
  rcases player_eq_self_or_other who player with rfl | rfl
  · rw [Profile.update_same, Profile.update_same]
  · rw [Profile.update_of_ne _ _ (otherPlayer_ne who),
      Profile.update_of_ne _ _ (otherPlayer_ne who), same]

/-- The expected utilities of the two players are opposite in either order. -/
theorem expectedUtility_other {Outcome : Type*} (utility : Outcome → Fin 2 → ℝ)
    (hzero : IsZeroSum utility) (who : Fin 2) (law : FinDist Outcome) :
    expectedUtility utility (otherPlayer who) law = -expectedUtility utility who law := by
  fin_cases who <;> simp [otherPlayer, hzero.expectedUtility_one]

/-- Nash guarantees the player's equilibrium value against every opponent
replacement; the expected-utility order is reversed using zero-sumness. -/
theorem nash_security (form : GameForm (Fin 2))
    (utility : form.sig.Outcome → Fin 2 → ℝ) (hzero : IsZeroSum utility)
    (profile : Profile form.sig) (equilibrium : IsNash form (euPreference utility) profile)
    (who : Fin 2) (replacement : form.sig.Strategy (otherPlayer who)) :
    expectedUtility utility who (form.play profile) ≤
      expectedUtility utility who
        (form.play (Profile.update profile (otherPlayer who) replacement)) := by
  have bound := (isNash_iff profile).mp equilibrium (otherPlayer who) replacement
  rw [euPreference_apply, expectedUtility_other utility hzero,
    expectedUtility_other utility hzero] at bound
  exact neg_le_neg_iff.mp bound

/-- M04 value uniqueness applies to either player's value, not only player zero. -/
theorem nash_value_eq_player (form : GameForm (Fin 2))
    (utility : form.sig.Outcome → Fin 2 → ℝ) (hzero : IsZeroSum utility)
    (first second : Profile form.sig)
    (hfirst : IsNash form (euPreference utility) first)
    (hsecond : IsNash form (euPreference utility) second) (who : Fin 2) :
    expectedUtility utility who (form.play first) =
      expectedUtility utility who (form.play second) := by
  have equality := nash_value_eq form utility hzero first second hfirst hsecond
  fin_cases who
  · exact equality
  · rw [hzero.expectedUtility_one, hzero.expectedUtility_one, equality]

universe us ua up uq uk ut
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ i, Fintype (E.Action i)]

/-- Select an equilibrium whose existence was proved from finite legal plans,
perfect recall and the observable continuation clock. -/
def publicBeliefEquilibrium (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) {observations : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals observations) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) : Profile M.behavioralSignature :=
  Classical.choose (exists_publicBelief_nash M hrecall clock fallback belief fuel utility)

/-- The selected profile satisfies the canonical behavioral Nash predicate. -/
theorem publicBeliefEquilibrium_isNash (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) {observations : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals observations) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) :
    IsNash (behavioralBeliefForm M belief fuel) (euPreference utility)
      (publicBeliefEquilibrium M hrecall clock fallback belief fuel utility) :=
  Classical.choose_spec (exists_publicBelief_nash M hrecall clock fallback belief fuel utility)

/-- The actual PBS value is the expected utility of an existing canonical
behavioral equilibrium. Zero-sumness proves independence of the selection. -/
def publicBeliefValue (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) {observations : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals observations) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (who : Fin 2) : ℝ :=
  expectedUtility utility who ((behavioralBeliefForm M belief fuel).play
    (publicBeliefEquilibrium M hrecall clock fallback belief fuel utility))

/-- Any equilibrium, including a nonunique one, yields this same PBS value. -/
theorem publicBeliefValue_eq_of_nash (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) {observations : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals observations) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility) (who : Fin 2)
    (profile : Profile M.behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm M belief fuel) (euPreference utility) profile) :
    publicBeliefValue M hrecall clock fallback belief fuel utility who =
      expectedUtility utility who ((behavioralBeliefForm M belief fuel).play profile) :=
  nash_value_eq_player _ utility hzero _ profile
    (publicBeliefEquilibrium_isNash M hrecall clock fallback belief fuel utility) equilibrium who

namespace TypeBeliefSlice

variable {M} {observations : List M.PublicSignal} {who : Fin 2} {T : Type ut}
variable (slice : TypeBeliefSlice M observations who T)

/-- The PBS value on an admissible own-belief slice of complete conditional
joint history laws. These kernels, not just opponent marginals, stay fixed. -/
def value (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (own : FinDist T) : ℝ :=
  publicBeliefValue M hrecall clock fallback (slice.mixture own) fuel utility who

/-- At every equilibrium the own conditional best-response values average to
the PBS equilibrium value. Simultaneous legal attainment is essential here. -/
theorem branch_eq_value_of_nash (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility)
    (own : FinDist T) (profile : Profile M.behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreference utility) profile) :
    slice.branch fallback fuel (fun history => utility history who) own profile =
      slice.value hrecall clock fallback fuel utility own := by
  rw [value, publicBeliefValue_eq_of_nash M hrecall clock fallback
    (slice.mixture own) fuel utility hzero who profile equilibrium]
  apply le_antisymm
  · rw [← slice.branch_attained]
    exact (isNash_iff profile).mp equilibrium who _
  · have bound := slice.payoff_le_branch hrecall fallback fuel
      (fun history => utility history who) own profile (profile who)
    rw [Profile.update_eq_self] at bound
    exact bound

/-- Every fixed opponent gives an upper bound on the actual PBS value. -/
theorem value_le_branch (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility)
    (own : FinDist T) (opponents : Profile M.behavioralSignature) :
    slice.value hrecall clock fallback fuel utility own ≤
      slice.branch fallback fuel (fun history => utility history who) own opponents := by
  let profile := publicBeliefEquilibrium M hrecall clock fallback (slice.mixture own) fuel utility
  have equilibrium := publicBeliefEquilibrium_isNash M hrecall clock fallback
    (slice.mixture own) fuel utility
  have security := nash_security (behavioralBeliefForm M (slice.mixture own) fuel)
    utility hzero profile equilibrium who (opponents (otherPlayer who))
  rw [update_other_eq_update_self] at security
  exact security.trans (slice.payoff_le_branch hrecall fallback fuel
    (fun history => utility history who) own opponents (profile who))

/-- Lemma 2: the canonical PBS value is an attained minimum over all
behavioral opponents of the conditional best-response affine branches. -/
theorem value_isLeast (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility) (own : FinDist T) :
    IsLeast (Set.range (slice.branch fallback fuel (fun history => utility history who) own))
      (slice.value hrecall clock fallback fuel utility own) := by
  constructor
  · exact ⟨publicBeliefEquilibrium M hrecall clock fallback (slice.mixture own) fuel utility,
      slice.branch_eq_value_of_nash hrecall clock fallback fuel utility hzero own _
        (publicBeliefEquilibrium_isNash M hrecall clock fallback (slice.mixture own) fuel utility)⟩
  · rintro result ⟨opponents, rfl⟩
    exact slice.value_le_branch hrecall clock fallback fuel utility hzero own opponents

end TypeBeliefSlice
end GameTheory.ReBeL
