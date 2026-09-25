/-
# Conditional values at a fixed PBS slice and fixed opposing policies

Approximate Nash controls probability-weighted conditional losses. Comparing
TWO profiles additionally requires equality of every opposing coordinate.
The sharp symmetric allowance is the maximum of the two root errors, divided
by the own-type mass only on support. Off-path kernels are not set to zero.
The actual information-set solver also bounds its gap to its CURRENT
opponent's Eq. (1) value, not to an independently recomputed opponent's value.
Own-law mean absolute gaps need no mass floor; a changed query law instead
carries an explicit density cap. It does not change the slice or opponents.
-/

import GameTheory.Analysis.ReBeL.PBSApproximateOptimality
import GameTheory.Analysis.ReBeL.PBSValueStability
import GameTheory.ReBeL.OracleReweighting

noncomputable section

namespace GameTheory.ReBeL.TypeBeliefSlice

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk ut
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable {M : InformationModel.{uι, us, ua, up, uq, uk} E}
variable [Fintype ι] [DecidableEq ι]
variable {observations : List M.PublicSignal} {who : ι} {T : Type ut}
variable (slice : TypeBeliefSlice M observations who T)

/-- Replacing the queried player's policy erases that coordinate of the input
profile, but not any opposing coordinate. No support assumption is needed. -/
theorem conditionalPayoff_eq_of_opponents_eq
    (first second : Profile M.behavioralSignature)
    (opponents : ∀ other, other ≠ who → first other = second other)
    (fuel : Nat) (payoff : E.History → ℝ) (replacement : M.BehavioralPolicy who)
    (type : T) :
    slice.conditionalPayoff first fuel payoff replacement type =
      slice.conditionalPayoff second fuel payoff replacement type := by
  have equal : Profile.update first who replacement = Profile.update second who replacement := by
    funext other
    by_cases same : other = who
    · subst other
      simp only [Profile.update_same]
    · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]
      exact opponents other same
  unfold conditionalPayoff
  rw [equal]

variable [Fintype E.History] [∀ i, Fintype (E.Action i)]

/-- A unilateral comparison with another self-play payoff is valid when its
opponents are the same. Multiplication preserves the absent-type case. -/
theorem weighted_payoff_sub_le_of_same_opponents (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (own : FinDist T)
    (first second : Profile M.behavioralSignature)
    (opponents : ∀ other, other ≠ who → first other = second other) (error : ℝ)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreferenceWithin error utility) first) (type : T) :
    own.prob type *
      (slice.conditionalPayoff second fuel (fun h => utility h who) (second who) type -
        slice.conditionalPayoff first fuel (fun h => utility h who) (first who) type) ≤
      error := by
  have better := slice.conditionalPayoff_le_infoValue hrecall fallback fuel
    (fun h => utility h who) first type (second who)
  rw [slice.conditionalPayoff_eq_of_opponents_eq first second opponents] at better
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_right better _)
    (FinDist.prob_nonneg own type)).trans
      (slice.weighted_infoGap_le_of_approxNash hrecall fallback fuel utility own first
        error equilibrium type)

/-- The two one-sided regret bounds give a MAXIMUM, not the sum, when the
opposing coordinates agree. This weighted statement includes absent types. -/
theorem weighted_payoff_abs_sub_le_of_same_opponents (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (own : FinDist T)
    (first second : Profile M.behavioralSignature)
    (opponents : ∀ other, other ≠ who → first other = second other)
    (firstError secondError : ℝ)
    (firstNash : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreferenceWithin firstError utility) first)
    (secondNash : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreferenceWithin secondError utility) second) (type : T) :
    own.prob type *
      |slice.conditionalPayoff first fuel (fun h => utility h who) (first who) type -
        slice.conditionalPayoff second fuel (fun h => utility h who) (second who) type| ≤
      max firstError secondError := by
  have lower := (slice.weighted_payoff_sub_le_of_same_opponents hrecall fallback fuel
    utility own first second opponents firstError firstNash type).trans
      (le_max_left firstError secondError)
  have upper := (slice.weighted_payoff_sub_le_of_same_opponents hrecall fallback fuel
    utility own second first (fun other different => (opponents other different).symm)
    secondError secondNash type).trans (le_max_right firstError secondError)
  calc
    _ = |own.prob type *
        (slice.conditionalPayoff first fuel (fun h => utility h who) (first who) type -
          slice.conditionalPayoff second fuel (fun h => utility h who) (second who) type)| := by
      rw [abs_mul, abs_of_nonneg (FinDist.prob_nonneg own type)]
    _ ≤ max firstError secondError := abs_le.mpr ⟨by nlinarith only [lower], upper⟩

/-- Division is justified only at a supported type. This is NOT a conditional
value-vector comparison for arbitrary independently changed opponents. -/
theorem payoff_abs_sub_le_of_same_opponents (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (own : FinDist T)
    (first second : Profile M.behavioralSignature)
    (opponents : ∀ other, other ≠ who → first other = second other)
    (firstError secondError : ℝ)
    (firstNash : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreferenceWithin firstError utility) first)
    (secondNash : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreferenceWithin secondError utility) second) (type : T)
    (supported : type ∈ own.support) :
    |slice.conditionalPayoff first fuel (fun h => utility h who) (first who) type -
      slice.conditionalPayoff second fuel (fun h => utility h who) (second who) type| ≤
      max firstError secondError / own.prob type := by
  apply (le_div_iff₀ (FinDist.prob_pos_iff.mpr supported)).mpr
  simpa only [mul_comm] using
    slice.weighted_payoff_abs_sub_le_of_same_opponents hrecall fallback fuel utility own
      first second opponents firstError secondError firstNash secondNash type

/-- An approximate equilibrium's current-opponent Eq. (1) error is nonnegative,
so its absolute error has the same inverse-probability bound as its gap. -/
theorem infoGap_abs_le_of_approxNash (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (own : FinDist T)
    (profile : Profile M.behavioralSignature) (error : ℝ)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreferenceWithin error utility) profile) (type : T)
    (supported : type ∈ own.support) :
    |slice.infoValue fallback fuel (fun h => utility h who) profile type -
      slice.conditionalPayoff profile fuel (fun h => utility h who) (profile who) type| ≤
      error / own.prob type := by
  rw [abs_of_nonneg (sub_nonneg.mpr (slice.conditionalPayoff_le_infoValue hrecall
    fallback fuel (fun h => utility h who) profile type (profile who)))]
  apply (le_div_iff₀ (FinDist.prob_pos_iff.mpr supported)).mpr
  simpa only [mul_comm] using slice.weighted_infoGap_le_of_approxNash hrecall fallback fuel
    utility own profile error equilibrium type

/-- The absolute current-opponent Eq. (1) gap is controlled in the OWN-law
mean without dividing by any type probability. Absent types remain unobserved. -/
theorem mean_infoGap_abs_le_of_approxNash (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (own : FinDist T)
    (profile : Profile M.behavioralSignature) (error : ℝ)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreferenceWithin error utility) profile) :
    own.expect (fun type =>
      |slice.infoValue fallback fuel (fun h => utility h who) profile type -
        slice.conditionalPayoff profile fuel (fun h => utility h who) (profile who) type|) ≤
      error := by
  calc
    _ = own.expect (fun type =>
        slice.infoValue fallback fuel (fun h => utility h who) profile type -
          slice.conditionalPayoff profile fuel (fun h => utility h who) (profile who) type) := by
      apply FinDist.expect_congr
      intro type _
      exact abs_of_nonneg (sub_nonneg.mpr (slice.conditionalPayoff_le_infoValue hrecall
        fallback fuel (fun h => utility h who) profile type (profile who)))
    _ ≤ error := slice.mean_infoGap_le_of_approxNash fallback fuel utility own profile
      error equilibrium

/-- Changing the QUERY LAW, not the slice or opponents, costs its explicit
density cap times the root error. This is an averaged conditional bound, not a
uniform oracle guarantee. Exact domination rules out new absent-type queries. -/
theorem reweighted_mean_infoGap_abs_le_of_approxNash (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (own : FinDist T)
    (profile : Profile M.behavioralSignature) (error : ℝ)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreferenceWithin error utility) profile)
    (query : FinDist T) (ratio : T → ℝ) (factor : ℝ) (nonneg : 0 ≤ factor)
    (density : ∀ type, query.prob type = own.prob type * ratio type)
    (bounded : ∀ type ∈ own.support, ratio type ≤ factor) :
    query.expect (fun type =>
      |slice.infoValue fallback fuel (fun h => utility h who) profile type -
        slice.conditionalPayoff profile fuel (fun h => utility h who) (profile who) type|) ≤
      factor * error := by
  rw [informationReweight_expect own query (fun type => type) ratio density]
  calc
    _ ≤ own.expect (fun type => factor *
        |slice.infoValue fallback fuel (fun h => utility h who) profile type -
          slice.conditionalPayoff profile fuel (fun h => utility h who) (profile who) type|) :=
      FinDist.expect_mono fun type sampled =>
        mul_le_mul_of_nonneg_right (bounded type sampled) (abs_nonneg _)
    _ = factor * own.expect (fun type =>
        |slice.infoValue fallback fuel (fun h => utility h who) profile type -
          slice.conditionalPayoff profile fuel (fun h => utility h who) (profile who) type|) :=
      FinDist.expect_smul _ _ _
    _ ≤ factor * error := mul_le_mul_of_nonneg_left
      (slice.mean_infoGap_abs_le_of_approxNash hrecall fallback fuel utility own profile
        error equilibrium) nonneg

end GameTheory.ReBeL.TypeBeliefSlice

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk ut
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {observations : List M.PublicSignal} {who : Fin 2} {T : Type ut}

/-- The actual budgeted information-set CFR solve approximates its CURRENT
opponent's conditional optimum. No Nash or conditional-rate premise is supplied. -/
theorem pbsInformationBudgetProfile_infoGap_abs_le
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ h player, |utility h player| ≤ bound)
    (error : ℝ) (positive : 0 < error) (type : T) (supported : type ∈ own.support) :
    let output := pbsInformationBudgetProfile M (slice.mixture own) fallback fuel
      utility bound error
    |slice.infoValue (fun player => liftPolicy M player (fallback player)) fuel
        (fun h => utility h who) output type -
      slice.conditionalPayoff output fuel (fun h => utility h who) (output who) type| ≤
      error / own.prob type :=
  slice.infoGap_abs_le_of_approxNash (fullSignals_perfectRecall M.toInfoSignals)
    (fun player => liftPolicy M player (fallback player)) fuel utility own _ error
    (pbsInformationBudgetProfile_isNash M (slice.mixture own) fallback fuel utility
      zeroSum bound nonneg bounded error positive) type supported

/-- Finite information-set CFR OUTPUTS have a conditional comparison when
opponents coincide. Distinct fallbacks and positive iteration counts are allowed;
the equality of opposing policies is an explicit, undischarged side condition. -/
theorem pbsInformationCFR_conditional_abs_sub_le_of_same_opponents
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (firstFallback secondFallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : Fin 2 → ℝ) (nonneg : ∀ player, 0 ≤ bound player)
    (bounded : ∀ player h, |payoff player h| ≤ bound player)
    (fuel firstTime secondTime : Nat) [NeZero firstTime] [NeZero secondTime]
    (opponents : ∀ other, other ≠ who →
      pbsInformationCFR M (slice.mixture own) firstFallback payoff fuel firstTime other =
        pbsInformationCFR M (slice.mixture own) secondFallback payoff fuel secondTime other)
    (type : T) (supported : type ∈ own.support) :
    let first := pbsInformationCFR M (slice.mixture own) firstFallback payoff fuel firstTime
    let second := pbsInformationCFR M (slice.mixture own) secondFallback payoff fuel secondTime
    |slice.conditionalPayoff first fuel (payoff who) (first who) type -
      slice.conditionalPayoff second fuel (payoff who) (second who) type| ≤
      max (pbsRootCFRBound M (slice.mixture own).law bound fuel firstTime)
        (pbsRootCFRBound M (slice.mixture own).law bound fuel secondTime) / own.prob type :=
  slice.payoff_abs_sub_le_of_same_opponents (fullSignals_perfectRecall M.toInfoSignals)
    (fun player => liftPolicy M player (firstFallback player)) fuel
    (fun h player => payoff player h) own _ _ opponents _ _
    (pbsInformationCFR_isNash M (slice.mixture own) firstFallback payoff zeroSum bound
      nonneg bounded fuel firstTime)
    (pbsInformationCFR_isNash M (slice.mixture own) secondFallback payoff zeroSum bound
      nonneg bounded fuel secondTime) type supported

/-- The genuine finite information-set solver controls its current-opponent
conditional gap under a dominated query law. The Nash error is derived from
its actual iteration count; the query-density cap is an explicit side condition. -/
theorem pbsInformationCFR_reweighted_infoGap_abs_le
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : Fin 2 → ℝ) (nonneg : ∀ player, 0 ≤ bound player)
    (bounded : ∀ player h, |payoff player h| ≤ bound player)
    (fuel time : Nat) [NeZero time]
    (query : FinDist T) (ratio : T → ℝ) (factor : ℝ) (factorNonneg : 0 ≤ factor)
    (density : ∀ type, query.prob type = own.prob type * ratio type)
    (ratioBound : ∀ type ∈ own.support, ratio type ≤ factor) :
    let output := pbsInformationCFR M (slice.mixture own) fallback payoff fuel time
    query.expect (fun type =>
      |slice.infoValue (fun player => liftPolicy M player (fallback player)) fuel
          (payoff who) output type -
        slice.conditionalPayoff output fuel (payoff who) (output who) type|) ≤
      factor * pbsRootCFRBound M (slice.mixture own).law bound fuel time :=
  slice.reweighted_mean_infoGap_abs_le_of_approxNash
    (fullSignals_perfectRecall M.toInfoSignals)
    (fun player => liftPolicy M player (fallback player)) fuel
    (fun h player => payoff player h) own _ _
    (pbsInformationCFR_isNash M (slice.mixture own) fallback payoff zeroSum bound
      nonneg bounded fuel time) query ratio factor factorNonneg density ratioBound

/-- A requested positive root budget gives a query-weighted conditional error
without using the least type mass. It still concerns THIS output's opponents,
not those of another solve, and does not assert a density cap for native queries. -/
theorem pbsInformationBudgetProfile_reweighted_infoGap_abs_le
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ h player, |utility h player| ≤ bound)
    (error : ℝ) (positive : 0 < error)
    (query : FinDist T) (ratio : T → ℝ) (factor : ℝ) (factorNonneg : 0 ≤ factor)
    (density : ∀ type, query.prob type = own.prob type * ratio type)
    (ratioBound : ∀ type ∈ own.support, ratio type ≤ factor) :
    let output := pbsInformationBudgetProfile M (slice.mixture own) fallback fuel
      utility bound error
    query.expect (fun type =>
      |slice.infoValue (fun player => liftPolicy M player (fallback player)) fuel
          (fun h => utility h who) output type -
        slice.conditionalPayoff output fuel (fun h => utility h who) (output who) type|) ≤
      factor * error :=
  slice.reweighted_mean_infoGap_abs_le_of_approxNash
    (fullSignals_perfectRecall M.toInfoSignals)
    (fun player => liftPolicy M player (fallback player)) fuel utility own _ error
    (pbsInformationBudgetProfile_isNash M (slice.mixture own) fallback fuel utility
      zeroSum bound nonneg bounded error positive)
    query ratio factor factorNonneg density ratioBound

end GameTheory.ReBeL
