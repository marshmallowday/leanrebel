/-
# A reference joint law covering every unilateral deviation

Uniform legal own play is a proof device, not a new opponent or an oracle per
deviation. Perfect recall makes the unilateral density information-local.
The terminal-aware canonical runner retains early absorption and every
zero-factual-reach branch. No positive lower bound on current play is assumed.
-/

import GameTheory.Analysis.ReBeL.UnilateralAverage
import GameTheory.ReBeL.OracleReweighting

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

variable [∀ who info, Fintype (M.Choice who info)]

/-- A full-support legal policy, including singleton inactive menus. -/
def uniformLegalPolicy (who : ι) (fallback : M.Policy who) : M.BehavioralPolicy who :=
  fun info => by
    let : Nonempty (M.Choice who info) := ⟨fallback info⟩
    exact FinDist.uniformOfFintype

/-- This profile is used only to name game-dependent own-reach constants. -/
def uniformLegalProfile (fallback : (who : ι) → M.Policy who) :
    Profile M.behavioralSignature := fun who => uniformLegalPolicy M who (fallback who)

/-- Every legal choice has positive mass without relying on a current iterate. -/
theorem uniformLegalPolicy_positive (who : ι) (fallback : M.Policy who)
    (info : M.InfoState who) (choice : M.Choice who info) :
    0 < (uniformLegalPolicy M who fallback info).prob choice := by
  let : Nonempty (M.Choice who info) := ⟨fallback info⟩
  exact FinDist.prob_pos_iff.mpr (FinDist.mem_support_uniformOfFintype choice)

/-- Every legal trace has positive uniform own reach, even when opponents
assign it zero probability. This does not assert positive full-game reach. -/
theorem uniformOwnReach_positive (fallback : (who : ι) → M.Policy who) (who : ι)
    {state : E.State} (trace : E.Trace state) :
    0 < M.playerReachProbability (uniformLegalProfile M fallback) who trace := by
  induction trace with
  | start => exact zero_lt_one
  | extend prior joint legal realized ih =>
      exact mul_pos ih (uniformLegalPolicy_positive M who (fallback who) _ _)

/-- The structural denominator is positive at every legally realized information
state, even when the current policy never reaches any history in that fiber. -/
theorem uniformInformationReach_positive (fallback : (who : ι) → M.Policy who)
    (who : ι) (info : M.InfoState who)
    (realized : ∃ history : E.History, M.infoOf who history.trace = info) :
    0 < informationOwnReach M (uniformLegalProfile M fallback) who info := by
  classical
  rw [informationOwnReach, dif_pos realized]
  exact uniformOwnReach_positive M fallback who _

variable [Fintype ι] [DecidableEq ι]

/-- A single dominating joint law fixes the actual opponents and chance,
replacing only the focal player's policy by uniform legal play. -/
def unilateralReferenceLaw (base : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι) (cut : Nat) : FinDist E.History :=
  M.runBehavioral (Profile.update base who (uniformLegalPolicy M who (fallback who))) cut

/-- The exact density of a unilateral alternative is information-local.
The denominator is game-dependent and positive, not the current own reach. -/
def unilateralDensity (base : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι) (policy : M.BehavioralPolicy who)
    (info : M.InfoState who) : ℝ :=
  informationOwnReach M (Profile.update base who policy) who info /
    informationOwnReach M (uniformLegalProfile M fallback) who info

/-- Canonical finite-horizon execution realizes the information-local density.
This supplies the game-semantic premise of the oracle reweighting theorem,
rather than asking callers to assume preservation of deviating payoffs. -/
theorem unilateralReference_density (hrecall : M.PerfectRecall)
    (base : Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (who : ι) (policy : M.BehavioralPolicy who) (cut : Nat) (history : E.History) :
    (M.runBehavioral (Profile.update base who policy) cut).prob history =
      (unilateralReferenceLaw M base fallback who cut).prob history *
        unilateralDensity M base fallback who policy (M.infoOf who history.trace) := by
  unfold unilateralReferenceLaw unilateralDensity
  rw [unilateral_probability_factorization M, unilateral_probability_factorization M,
    informationOwnReach_eq_player M hrecall, informationOwnReach_eq_player M hrecall]
  have same : M.playerReachProbability
      (Profile.update base who (uniformLegalPolicy M who (fallback who))) who history.trace =
      M.playerReachProbability (uniformLegalProfile M fallback) who history.trace :=
    ownReach_eq_of_policy_eq M _ (uniformLegalProfile M fallback) who
      (Profile.update_same base who (uniformLegalPolicy M who (fallback who))) history.trace
  rw [same]
  have positive := uniformOwnReach_positive M fallback who history.trace
  field_simp [ne_of_gt positive]

/-- A single conditional vector for the reference covers the expectation
under EVERY unilateral policy, with the original delta error. All values are
conditional on information states, never pointwise hidden-history values. -/
theorem unilateralReference_oracle_error (hrecall : M.PerfectRecall)
    (base : Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (who : ι) (cut : Nat) (value : E.History → ℝ)
    (prediction : M.InfoState who → ℝ) (error : ℝ)
    (accurate : ∀ info ∈ ((unilateralReferenceLaw M base fallback who cut).map
        (fun history => M.infoOf who history.trace)).support,
      |prediction info - conditionalOracleValue (unilateralReferenceLaw M base fallback who cut)
        (fun history => M.infoOf who history.trace) value info| ≤ error)
    (policy : M.BehavioralPolicy who) :
    |((M.runBehavioral (Profile.update base who policy) cut).map
        (fun history => M.infoOf who history.trace)).expect prediction -
      (M.runBehavioral (Profile.update base who policy) cut).expect value| ≤ error := by
  exact conditionalOracle_reweight_error _ _ _
    (unilateralDensity M base fallback who policy)
    (unilateralReference_density M hrecall base fallback who policy cut)
    value prediction error accurate

end GameTheory.ReBeL
