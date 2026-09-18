/-
# Canonical PBS value and attained minimax

The opponent branches are the actual conditional best responses in the
canonical continuation runner. The Nash inequalities prove attainment and
minimality; these properties are not assumptions on an abstract value oracle.
The focal player is labeled zero and the other player one. Conditional joint
history kernels remain fixed while own weights vary.
-/

import GameTheory.Analysis.ReBeL.PBSInfoValue
import GameTheory.Analysis.ReBeL.BeliefExistence
import GameTheory.Analysis.ReBeL.EquilibriumValue
import GameTheory.Analysis.ReBeL.ValueEnvelope

noncomputable section

namespace GameTheory.ReBeL.TypeBeliefSlice

open GameTheory.Protocol InformationModel GameTheory.Math.Probability

universe us ua up uq uk ut
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable {M : InformationModel.{0, us, ua, up, uq, uk} E}
variable [Fintype E.History] [∀ i, Fintype (E.Action i)]
variable {observations : List M.PublicSignal} {T : Type ut}
variable (slice : TypeBeliefSlice M observations 0 T)

/-- At a Nash profile the fixed-opponent best-response branch is exactly the
canonical equilibrium payoff, including boundary own beliefs. -/
theorem branch_eq_equilibriumPayoff (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (own : FinDist T)
    (profile : Profile M.behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreference utility) profile) :
    slice.branch fallback fuel (fun history => utility history 0) own profile =
      expectedUtility utility 0
        ((behavioralBeliefForm M (slice.mixture own) fuel).play profile) := by
  rw [isNash_iff] at equilibrium
  apply le_antisymm
  · rw [← slice.branch_attained fallback fuel (fun history => utility history 0) own profile]
    exact equilibrium 0
      (slice.simultaneousResponse fallback fuel (fun history => utility history 0)
        profile).toBehavioral
  · have bound := slice.payoff_le_branch hrecall fallback fuel
      (fun history => utility history 0) own profile (profile 0)
    simpa only [Profile.update_eq_self, expectedUtility] using bound

/-- The equilibrium player's strategy guarantees its value against every
opponent. The opponent's Nash inequality is used through zero-sum utility. -/
theorem equilibriumPayoff_le_branch (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility) (own : FinDist T)
    (profile : Profile M.behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreference utility) profile) (opponents : Profile M.behavioralSignature) :
    expectedUtility utility 0
        ((behavioralBeliefForm M (slice.mixture own) fuel).play profile) ≤
      slice.branch fallback fuel (fun history => utility history 0) own opponents := by
  rw [isNash_iff] at equilibrium
  have cross : Profile.update profile 1 (opponents 1) =
      Profile.update opponents 0 (profile 0) := by
    funext who
    rcases (by decide : ∀ who : Fin 2, who = 0 ∨ who = 1) who with rfl | rfl
    · rw [Profile.update_of_ne _ _ (by decide), Profile.update_same]
    · rw [Profile.update_same, Profile.update_of_ne _ _ (by decide)]
  have column : expectedUtility utility 1
      ((behavioralBeliefForm M (slice.mixture own) fuel).play
        (Profile.update profile 1 (opponents 1))) ≤
      expectedUtility utility 1
        ((behavioralBeliefForm M (slice.mixture own) fuel).play profile) :=
    equilibrium 1 (opponents 1)
  rw [hzero.expectedUtility_one, hzero.expectedUtility_one, cross] at column
  have upper : expectedUtility utility 0
      ((behavioralBeliefForm M (slice.mixture own) fuel).play
        (Profile.update opponents 0 (profile 0))) ≤
      slice.branch fallback fuel (fun history => utility history 0) own opponents :=
    slice.payoff_le_branch hrecall fallback fuel
      (fun history => utility history 0) own opponents (profile 0)
  exact (by linarith : expectedUtility utility 0
    ((behavioralBeliefForm M (slice.mixture own) fuel).play profile) ≤
      expectedUtility utility 0 ((behavioralBeliefForm M (slice.mixture own) fuel).play
        (Profile.update opponents 0 (profile 0)))).trans upper

/-- Actual PBS minimax: the equilibrium opponent attains the least of all
behavioral-opponent best-response branches. No restriction to pure opponents. -/
theorem branch_isLeast_of_nash (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility) (own : FinDist T)
    (profile : Profile M.behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreference utility) profile) :
    IsLeast (Set.range (slice.branch fallback fuel (fun history => utility history 0) own))
      (expectedUtility utility 0
        ((behavioralBeliefForm M (slice.mixture own) fuel).play profile)) := by
  constructor
  · exact ⟨profile, slice.branch_eq_equilibriumPayoff hrecall fallback fuel
      utility own profile equilibrium⟩
  · rintro result ⟨opponents, rfl⟩
    exact slice.equilibriumPayoff_le_branch hrecall fallback fuel utility hzero
      own profile equilibrium opponents

/-- Finite histories uniformly bound every conditional optimum, for all
behavioral opponents and all types, including types of current weight zero. -/
theorem exists_infoValue_abs_bound (fallback : Profile M.strategicSignature)
    (fuel : ℕ) (payoff : E.History → ℝ) :
    ∃ bound : ℝ, ∀ (opponents : Profile M.behavioralSignature) type,
      |slice.infoValue fallback fuel payoff opponents type| ≤ bound := by
  obtain ⟨bound, bounded⟩ := (Set.finite_range fun history : E.History =>
    |payoff history|).bddAbove
  have expectation_bound (law : FinDist E.History) : |law.expect payoff| ≤ bound := by
    apply abs_le.mpr
    constructor
    · calc
        -bound = law.expect (fun _ => -bound) := (FinDist.expect_const _ _).symm
        _ ≤ law.expect payoff := FinDist.expect_mono fun history _ =>
          (abs_le.mp (bounded ⟨history, rfl⟩)).1
    · exact FinDist.expect_le_of_forall law payoff bound fun history _ =>
        (abs_le.mp (bounded ⟨history, rfl⟩)).2
  refine ⟨bound, ?_⟩
  intro opponents type
  unfold infoValue conditionalPayoff
  exact expectation_bound _

variable [Fintype T]

/-- The lower envelope of the canonical PBS best-response branches. Its
restriction to probability weights is the Nash payoff, as proved below. -/
def value (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) (weight : T → ℝ) : ℝ :=
  ValueGeometry.envelope (slice.infoValue fallback fuel payoff) weight

/-- The signed-weight lower envelope is finite, even off the simplex. -/
theorem branches_bounded_below (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) (weight : T → ℝ) :
    BddBelow (Set.range fun opponents : Profile M.behavioralSignature =>
      ValueGeometry.pairing (slice.infoValue fallback fuel payoff opponents) weight) := by
  obtain ⟨bound, bounded⟩ := slice.exists_infoValue_abs_bound fallback fuel payoff
  exact ValueGeometry.bounded_below_of_abs_bound
    (slice.infoValue fallback fuel payoff) bound bounded weight

/-- The envelope is the payoff of every canonical PBS equilibrium, not just
a selected one. Thus nonunique equilibria cannot change the PBS value. -/
theorem value_eq_equilibriumPayoff (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility) (own : FinDist T)
    (profile : Profile M.behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreference utility) profile) :
    slice.value fallback fuel (fun history => utility history 0) own.prob =
      expectedUtility utility 0
        ((behavioralBeliefForm M (slice.mixture own) fuel).play profile) := by
  show sInf (Set.range
    (slice.weightedBranch fallback fuel (fun history => utility history 0) own.prob)) = _
  have same : slice.weightedBranch fallback fuel (fun history => utility history 0) own.prob =
      slice.branch fallback fuel (fun history => utility history 0) own := by
    funext opponents
    exact (slice.branch_eq_weightedBranch fallback fuel
      (fun history => utility history 0) own opponents).symm
  rw [same]
  exact (slice.branch_isLeast_of_nash hrecall fallback fuel utility hzero
    own profile equilibrium).csInf_eq

/-- Equilibrium existence and value agreement are jointly discharged using
the finite PBS realization theorem. An equilibrium is not an input premise. -/
theorem exists_nash_with_value (hrecall : M.PerfectRecall) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (utility : E.History → Fin 2 → ℝ) (hzero : IsZeroSum utility) (own : FinDist T) :
    ∃ profile : Profile M.behavioralSignature,
      IsNash (behavioralBeliefForm M (slice.mixture own) fuel) (euPreference utility) profile ∧
      slice.value fallback fuel (fun history => utility history 0) own.prob =
        expectedUtility utility 0
          ((behavioralBeliefForm M (slice.mixture own) fuel).play profile) := by
  obtain ⟨profile, equilibrium⟩ := exists_publicBelief_nash M hrecall clock fallback
    (slice.mixture own) fuel utility
  exact ⟨profile, equilibrium, slice.value_eq_equilibriumPayoff hrecall fallback
    fuel utility hzero own profile equilibrium⟩

end GameTheory.ReBeL.TypeBeliefSlice
