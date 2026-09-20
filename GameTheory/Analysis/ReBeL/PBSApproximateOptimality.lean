/-
# Approximate PBS Nash and probability-weighted conditional losses

One legal remembered-type best response attains every conditional maximum.
Approximate Nash controls the mean of these nonnegative gaps, hence each
probability-weighted gap. Dividing requires a supported type; uniform typewise
loss needs an explicit positive mass floor or a type-dependent solve budget.
An unvisited type is not certified by a zero-weight inequality.
-/

import GameTheory.Analysis.ReBeL.PBSLeafOptimality

noncomputable section

namespace GameTheory.ReBeL.TypeBeliefSlice

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk ut
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable {M : InformationModel.{uι, us, ua, up, uq, uk} E}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype E.History] [∀ i, Fintype (E.Action i)]
variable {observations : List M.PublicSignal} {who : ι} {T : Type ut}
variable (slice : TypeBeliefSlice M observations who T)

/-- The mean conditional best-response gap is bounded by canonical approximate
Nash. The deviation is the existing single legal remembered-type splice. -/
theorem mean_infoGap_le_of_approxNash
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (own : FinDist T)
    (profile : Profile M.behavioralSignature) (error : ℝ)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreferenceWithin error utility) profile) :
    own.expect (fun type =>
      slice.infoValue fallback fuel (fun h => utility h who) profile type -
        slice.conditionalPayoff profile fuel (fun h => utility h who) (profile who) type) ≤
      error := by
  have bound := (isNash_iff (F := behavioralBeliefForm M (slice.mixture own) fuel)
    (weaklyPrefers := euPreferenceWithin error utility) profile).mp equilibrium who
      (slice.simultaneousResponse fallback fuel (fun h => utility h who) profile).toBehavioral
  have actual : (PublicBelief.continuationLaw M profile fuel (slice.mixture own)).expect
        (fun h => utility h who) =
      own.expect (slice.conditionalPayoff profile fuel (fun h => utility h who) (profile who)) := by
    simpa only [conditionalPayoff, Profile.update_eq_self] using
      slice.mixture_payoff own profile fuel (fun h => utility h who)
  have attained := slice.branch_attained fallback fuel (fun h => utility h who) own profile
  rw [euPreferenceWithin_apply] at bound
  simp only [expectedUtility, behavioralBeliefForm] at bound
  rw [attained, actual] at bound
  rw [FinDist.expect_sub]
  dsimp only [branch] at bound
  linarith

/-- Even at zero type mass the multiplied statement is valid. The absent
case deliberately gives no conditional optimality guarantee. -/
theorem weighted_infoGap_le_of_approxNash (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (own : FinDist T)
    (profile : Profile M.behavioralSignature) (error : ℝ)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreferenceWithin error utility) profile) (type : T) :
    own.prob type *
      (slice.infoValue fallback fuel (fun h => utility h who) profile type -
        slice.conditionalPayoff profile fuel (fun h => utility h who) (profile who) type) ≤
      error := by
  classical
  let gap := fun t => slice.infoValue fallback fuel (fun h => utility h who) profile t -
    slice.conditionalPayoff profile fuel (fun h => utility h who) (profile who) t
  have nonneg (t : T) : 0 ≤ gap t := sub_nonneg.mpr
    (slice.conditionalPayoff_le_infoValue hrecall fallback fuel
      (fun h => utility h who) profile t (profile who))
  have atom : own.prob type * gap type ≤ own.expect gap := by
    rw [← FinDist.expect_ite_eq own type (gap type)]
    apply FinDist.expect_mono
    intro t _
    by_cases equal : type = t
    · subst t
      rw [if_pos rfl]
    · rw [if_neg equal]
      exact nonneg t
  exact atom.trans (slice.mean_infoGap_le_of_approxNash fallback fuel utility own profile
    error equilibrium)

/-- Any complete behavioral deviation has conditional gain at most error
DIVIDED BY the type probability. Positive support is necessary for division. -/
theorem conditional_gain_le_of_approxNash (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (own : FinDist T)
    (profile : Profile M.behavioralSignature) (error : ℝ)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreferenceWithin error utility) profile) (type : T) (supported : type ∈ own.support)
    (target : M.BehavioralPolicy who) :
    slice.conditionalPayoff profile fuel (fun h => utility h who) target type -
      slice.conditionalPayoff profile fuel (fun h => utility h who) (profile who) type ≤
        error / own.prob type := by
  have weighted := slice.weighted_infoGap_le_of_approxNash hrecall fallback fuel utility own
    profile error equilibrium type
  have better := slice.conditionalPayoff_le_infoValue hrecall fallback fuel
    (fun h => utility h who) profile type target
  apply (le_div_iff₀ (FinDist.prob_pos_iff.mpr supported)).mpr
  nlinarith [FinDist.prob_nonneg own type]

/-- A solver may allocate a root error budget proportional to each queried
type mass. This yields the requested conditional loss without dividing by a
possibly tiny probability in the conclusion. It still excludes absent types. -/
theorem conditional_gain_le_of_mass_budget (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → ι → ℝ) (own : FinDist T)
    (profile : Profile M.behavioralSignature) (error loss : ℝ)
    (equilibrium : IsNash (behavioralBeliefForm M (slice.mixture own) fuel)
      (euPreferenceWithin error utility) profile) (type : T) (supported : type ∈ own.support)
    (budget : error ≤ own.prob type * loss) (target : M.BehavioralPolicy who) :
    slice.conditionalPayoff profile fuel (fun h => utility h who) target type -
      slice.conditionalPayoff profile fuel (fun h => utility h who) (profile who) type ≤ loss := by
  have bound := slice.conditional_gain_le_of_approxNash hrecall fallback fuel utility own
    profile error equilibrium type supported target
  exact bound.trans ((div_le_iff₀ (FinDist.prob_pos_iff.mpr supported)).mpr (by
    simpa only [mul_comm] using budget))

end GameTheory.ReBeL.TypeBeliefSlice
