/-
# Conditional PBS best-response values and simultaneous attainment

Equation (1) is an attained maximum over actual legal behavioral policies in
the canonical continuation runner. Finite predrawing bounds every behavioral
deviation, and remembered-type splicing attains all conditional maxima at
once. Off-path own weights are never used to condition these fixed kernels.
-/

import GameTheory.Analysis.ReBeL.TypeBeliefSlice
import GameTheory.Analysis.ReBeL.ContinuationDeviations

noncomputable section

namespace GameTheory.ReBeL.TypeBeliefSlice

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk ut
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable {M : InformationModel.{uι, us, ua, up, uq, uk} E}
variable [Fintype ι] [DecidableEq ι]
variable {observations : List M.PublicSignal} {who : ι} {T : Type ut}
variable (slice : TypeBeliefSlice M observations who T)

/-- The actual conditional expected continuation payoff against fixed
opponents after replacing only the player's own behavioral policy. -/
def conditionalPayoff (opponents : Profile M.behavioralSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) (replacement : M.BehavioralPolicy who) (type : T) : ℝ :=
  (PublicBelief.continuationLaw M (Profile.update opponents who replacement)
    fuel (slice.kernel type)).expect payoff

variable [Fintype E.History] [∀ i, Fintype (E.Action i)]

/-- A finite pure continuation plan attaining the conditional optimum. Its
payoff is evaluated by the existing protocol, not an independently supplied matrix. -/
def bestResponsePlan (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) (opponents : Profile M.behavioralSignature) (type : T) :
    FinitePlan M who := by
  classical
  let : Fintype (FinitePlan M who) := finitePlanFintype M who
  let : Nonempty (FinitePlan M who) := ⟨fun info => fallback who info.1⟩
  exact Classical.choose (Finite.exists_max fun plan : FinitePlan M who =>
    slice.conditionalPayoff opponents fuel payoff
      (FinitePlan.toPolicy M (fallback who) plan).toBehavioral type)

/-- Equation (1) on the explicitly fixed compatible conditional-history
slice. It is defined even when the corresponding own-type probability is zero. -/
def infoValue (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) (opponents : Profile M.behavioralSignature) (type : T) : ℝ :=
  slice.conditionalPayoff opponents fuel payoff
    (FinitePlan.toPolicy M (fallback who)
      (slice.bestResponsePlan fallback fuel payoff opponents type)).toBehavioral type

/-- Every finite pure continuation plan is bounded by the selected optimum. -/
theorem plan_le_infoValue (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) (opponents : Profile M.behavioralSignature) (type : T)
    (plan : FinitePlan M who) :
    slice.conditionalPayoff opponents fuel payoff
        (FinitePlan.toPolicy M (fallback who) plan).toBehavioral type ≤
      slice.infoValue fallback fuel payoff opponents type := by
  classical
  let : Fintype (FinitePlan M who) := finitePlanFintype M who
  let : Nonempty (FinitePlan M who) := ⟨fun info => fallback who info.1⟩
  exact Classical.choose_spec (Finite.exists_max fun plan : FinitePlan M who =>
    slice.conditionalPayoff opponents fuel payoff
      (FinitePlan.toPolicy M (fallback who) plan).toBehavioral type) plan

/-- The maximum controls all behavioral replacements, not merely the finite
pure plans used to construct it. Opponent coordinates remain unchanged. -/
theorem conditionalPayoff_le_infoValue (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : ℕ) (payoff : E.History → ℝ)
    (opponents : Profile M.behavioralSignature) (type : T)
    (replacement : M.BehavioralPolicy who) :
    slice.conditionalPayoff opponents fuel payoff replacement type ≤
      slice.infoValue fallback fuel payoff opponents type := by
  apply publicBelief_deviationValue_le_of_finitePlans_le M hrecall fuel opponents fallback who
    payoff _ (slice.kernel type)
  exact slice.plan_le_infoValue fallback fuel payoff opponents type

/-- Equation (1) is an attained maximum of the actual behavioral payoff set,
rather than an assumed best-response value or a supremum without attainment. -/
theorem infoValue_isGreatest (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : ℕ) (payoff : E.History → ℝ)
    (opponents : Profile M.behavioralSignature) (type : T) :
    IsGreatest (Set.range fun replacement : M.BehavioralPolicy who =>
      slice.conditionalPayoff opponents fuel payoff replacement type)
        (slice.infoValue fallback fuel payoff opponents type) := by
  constructor
  · exact ⟨(FinitePlan.toPolicy M (fallback who)
      (slice.bestResponsePlan fallback fuel payoff opponents type)).toBehavioral, rfl⟩
  · rintro result ⟨replacement, rfl⟩
    exact slice.conditionalPayoff_le_infoValue hrecall fallback fuel payoff opponents
      type replacement

/-- One legal information-local policy pastes all the attaining type plans. -/
def simultaneousResponse (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) (opponents : Profile M.behavioralSignature) : M.Policy who :=
  slice.memory.splice fun type => FinitePlan.toPolicy M (fallback who)
    (slice.bestResponsePlan fallback fuel payoff opponents type)

/-- All conditional optima are attained by that one legal policy, including
zero-own-weight types and nonunique conditional maximizers. -/
theorem simultaneousResponse_attains (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) (opponents : Profile M.behavioralSignature) (type : T) :
    slice.conditionalPayoff opponents fuel payoff
        (slice.simultaneousResponse fallback fuel payoff opponents).toBehavioral type =
      slice.infoValue fallback fuel payoff opponents type := by
  unfold conditionalPayoff simultaneousResponse
  rw [splice_conditionalLaw]
  rfl

/-- Lemma 1's fixed-opponent branch, with actual conditional best responses. -/
def branch (fallback : Profile M.strategicSignature) (fuel : ℕ) (payoff : E.History → ℝ)
    (own : FinDist T) (opponents : Profile M.behavioralSignature) : ℝ :=
  own.expect (slice.infoValue fallback fuel payoff opponents)

/-- Every behavioral own strategy lies below the fixed-opponent branch. -/
theorem payoff_le_branch (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : ℕ) (payoff : E.History → ℝ)
    (own : FinDist T) (opponents : Profile M.behavioralSignature)
    (replacement : M.BehavioralPolicy who) :
    (PublicBelief.continuationLaw M (Profile.update opponents who replacement)
        fuel (slice.mixture own)).expect payoff ≤
      slice.branch fallback fuel payoff own opponents := by
  rw [mixture_payoff]
  exact FinDist.expect_mono fun type _ =>
    slice.conditionalPayoff_le_infoValue hrecall fallback fuel payoff opponents type replacement

/-- The branch is attained simultaneously, not by illegally choosing different
strategies at indistinguishable histories. -/
theorem branch_attained (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) (own : FinDist T) (opponents : Profile M.behavioralSignature) :
    (PublicBelief.continuationLaw M (Profile.update opponents who
      (slice.simultaneousResponse fallback fuel payoff opponents).toBehavioral)
        fuel (slice.mixture own)).expect payoff =
      slice.branch fallback fuel payoff own opponents := by
  rw [mixture_payoff]
  exact FinDist.expect_congr fun type _ =>
    slice.simultaneousResponse_attains fallback fuel payoff opponents type

/-- Lemma 1 on the actual PBS: the branch is the greatest behavioral payoff. -/
theorem branch_isGreatest (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : ℕ) (payoff : E.History → ℝ)
    (own : FinDist T) (opponents : Profile M.behavioralSignature) :
    IsGreatest (Set.range fun replacement : M.BehavioralPolicy who =>
      (PublicBelief.continuationLaw M (Profile.update opponents who replacement)
        fuel (slice.mixture own)).expect payoff)
      (slice.branch fallback fuel payoff own opponents) := by
  constructor
  · exact ⟨(slice.simultaneousResponse fallback fuel payoff opponents).toBehavioral,
      slice.branch_attained fallback fuel payoff own opponents⟩
  · rintro result ⟨replacement, rfl⟩
    exact slice.payoff_le_branch hrecall fallback fuel payoff own opponents replacement

/-- Extend the fixed-opponent branch linearly to arbitrary own weights. -/
def weightedBranch [Fintype T] (fallback : Profile M.strategicSignature) (fuel : ℕ)
    (payoff : E.History → ℝ) (weight : T → ℝ) (opponents : Profile M.behavioralSignature) : ℝ :=
  ∑ type, weight type * slice.infoValue fallback fuel payoff opponents type

/-- On probability weights the affine expression equals the actual branch. -/
theorem branch_eq_weightedBranch [Fintype T]
    (fallback : Profile M.strategicSignature) (fuel : ℕ) (payoff : E.History → ℝ)
    (own : FinDist T) (opponents : Profile M.behavioralSignature) :
    slice.branch fallback fuel payoff own opponents =
      slice.weightedBranch fallback fuel payoff own.prob opponents := by
  rw [branch, FinDist.expect, tsum_fintype]
  rfl

/-- Lemma 1's own-belief linearity holds with fixed conditional joint laws
and fixed opponents. The conditional optima do not depend on these weights. -/
theorem weightedBranch_linear [Fintype T]
    (fallback : Profile M.strategicSignature) (fuel : ℕ) (payoff : E.History → ℝ)
    (first second : T → ℝ) (a b : ℝ) (opponents : Profile M.behavioralSignature) :
    slice.weightedBranch fallback fuel payoff (fun type => a * first type + b * second type)
        opponents = a * slice.weightedBranch fallback fuel payoff first opponents +
          b * slice.weightedBranch fallback fuel payoff second opponents := by
  unfold weightedBranch
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]

end GameTheory.ReBeL.TypeBeliefSlice
