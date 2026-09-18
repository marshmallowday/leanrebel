/-
# Uniform bounds for canonical counterfactual payoffs

Finite history fibers and bounded game payoffs bound every local action value,
under every behavioral profile. No bound on a produced regret table, learner
or solution is an input. Zero-reach histories remain in each sum.
-/

import GameTheory.Analysis.ReBeL.CFRTrace

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability GameTheory.Analysis.Approachability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Every own-action factor lies in the unit interval, on any legal trace. -/
theorem playerStep_unitInterval (strategy : Profile M.behavioralSignature)
    (who : ι) {state : E.State} (trace : E.Trace state)
    (joint : E.JointAction) (hlegal : E.Legal state joint) :
    0 ≤ M.playerStepProb strategy who trace joint hlegal ∧
      M.playerStepProb strategy who trace joint hlegal ≤ 1 := by
  unfold InformationModel.playerStepProb
  exact ⟨FinDist.prob_nonneg _ _, FinDist.prob_le_one _ _⟩

/-- A player's actual own reach is a product of lawful probability factors. -/
theorem playerReach_unitInterval (strategy : Profile M.behavioralSignature)
    (who : ι) {state : E.State} (trace : E.Trace state) :
    0 ≤ M.playerReachProbability strategy who trace ∧
      M.playerReachProbability strategy who trace ≤ 1 := by
  induction trace with
  | start => simp [InformationModel.playerReachProbability]
  | extend prior joint hlegal realized ih =>
      have hstep := playerStep_unitInterval M strategy who prior joint hlegal
      simp only [InformationModel.playerReachProbability]
      refine ⟨mul_nonneg ih.1 hstep.1, ?_⟩
      calc
        _ ≤ 1 * M.playerStepProb strategy who prior joint hlegal :=
          mul_le_mul_of_nonneg_right ih.2 hstep.1
        _ ≤ 1 := by simpa using hstep.2

variable [Fintype ι] [DecidableEq ι]

/-- Chance and every opponent factor are in the unit interval; deleting the
focal player's factor does not turn a single-history weight into a posterior. -/
theorem counterfactualStep_unitInterval (strategy : Profile M.behavioralSignature)
    (who : ι) {state : E.State} (trace : E.Trace state)
    (joint : E.JointAction) (hlegal : E.Legal state joint) (next : E.State) :
    0 ≤ M.counterfactualStepProb strategy who trace joint hlegal next ∧
      M.counterfactualStepProb strategy who trace joint hlegal next ≤ 1 := by
  have hproduct0 : 0 ≤ ∏ other ∈ Finset.univ.erase who,
      M.playerStepProb strategy other trace joint hlegal :=
    Finset.prod_nonneg fun other _ =>
      (playerStep_unitInterval M strategy other trace joint hlegal).1
  have hproduct1 : (∏ other ∈ Finset.univ.erase who,
      M.playerStepProb strategy other trace joint hlegal) ≤ 1 :=
    Finset.prod_le_one
      (fun other _ => (playerStep_unitInterval M strategy other trace joint hlegal).1)
      (fun other _ => (playerStep_unitInterval M strategy other trace joint hlegal).2)
  unfold InformationModel.counterfactualStepProb
  refine ⟨mul_nonneg (FinDist.prob_nonneg _ _) hproduct0, ?_⟩
  calc
    _ ≤ 1 * (∏ other ∈ Finset.univ.erase who,
        M.playerStepProb strategy other trace joint hlegal) :=
      mul_le_mul_of_nonneg_right (FinDist.prob_le_one _ _) hproduct0
    _ ≤ 1 := by simpa using hproduct1

/-- Every single-history counterfactual reach is nonnegative and at most one,
including histories impossible under the current focal policy. -/
theorem counterfactualReach_unitInterval (strategy : Profile M.behavioralSignature)
    (who : ι) {state : E.State} (trace : E.Trace state) :
    0 ≤ M.counterfactualReachProbability strategy who trace ∧
      M.counterfactualReachProbability strategy who trace ≤ 1 := by
  induction trace with
  | start => simp [InformationModel.counterfactualReachProbability]
  | @extend source next prior joint hlegal realized ih =>
      have hstep := counterfactualStep_unitInterval M strategy who prior joint hlegal next
      simp only [InformationModel.counterfactualReachProbability]
      refine ⟨mul_nonneg ih.1 hstep.1, ?_⟩
      calc
        _ ≤ 1 * M.counterfactualStepProb strategy who prior joint hlegal next :=
          mul_le_mul_of_nonneg_right ih.2 hstep.1
        _ ≤ 1 := by simpa using hstep.2

/-- The canonical unnormalized counterfactual value is bounded by the number
of histories in its information fiber times the game's payoff bound. -/
theorem counterfactualValue_abs_le (strategy : Profile M.behavioralSignature)
    (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)] (policy : M.BehavioralPolicy who)
    (payoff : E.History → ℝ) {bound : ℝ} (hbound0 : 0 ≤ bound)
    (hbound : ∀ history, |payoff history| ≤ bound) (fuel : ℕ) :
    |M.counterfactualContinuationValue strategy who site policy payoff fuel| ≤
      (Fintype.card (M.InformationHistory who site.1) : ℝ) * bound := by
  unfold InformationModel.counterfactualContinuationValue
  calc
    _ ≤ ∑ history : M.InformationHistory who site.1,
        |M.counterfactualReachProbability strategy who history.1.trace *
          M.behavioralContinuationValue strategy who policy payoff fuel history.1| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _history : M.InformationHistory who site.1, bound := by
      apply Finset.sum_le_sum
      intro history _
      have hreach := counterfactualReach_unitInterval M strategy who history.1.trace
      have hvalue : |M.behavioralContinuationValue strategy who policy payoff fuel
          history.1| ≤ bound :=
        FinDist.abs_expect_le_of_abs_bound _ _ (fun later _ => hbound later)
      rw [abs_mul, abs_of_nonneg hreach.1]
      calc
        _ ≤ M.counterfactualReachProbability strategy who history.1.trace * bound :=
          mul_le_mul_of_nonneg_left hvalue hreach.1
        _ ≤ 1 * bound := mul_le_mul_of_nonneg_right hreach.2 hbound0
        _ = bound := one_mul _
    _ = _ := by simp

/-- A coordinatewise bound controls the actual Euclidean norm used by the
existing regret/approachability modules, not a substituted scalar norm. -/
theorem euclidean_norm_le_coordinate_bound {A : Type*} [Fintype A]
    (x : EuclideanSpace ℝ A) {bound : ℝ} (hbound0 : 0 ≤ bound)
    (hbound : ∀ a, |x.ofLp a| ≤ bound) :
    ‖x‖ ≤ Real.sqrt (Fintype.card A) * bound := by
  have hsquared : ‖x‖ ^ 2 ≤ (Fintype.card A : ℝ) * bound ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _a : A, bound ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        have ha := abs_le.mp (hbound a)
        nlinarith [sq_nonneg (bound - x.ofLp a), sq_nonneg (bound + x.ofLp a)]
      _ = _ := by simp
  have hright0 : 0 ≤ Real.sqrt (Fintype.card A) * bound :=
    mul_nonneg (Real.sqrt_nonneg _) hbound0
  have hright : (Real.sqrt (Fintype.card A) * bound) ^ 2 =
      (Fintype.card A : ℝ) * bound ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  nlinarith [norm_nonneg x]

/-- A bounded finite-action utility produces uniformly bounded regret payoff
vectors against every legal mixed action and every environment. -/
theorem regretPayoff_norm_le_of_abs_bound {A Q : Type*} [Fintype A]
    (utility : A → Q → ℝ) {bound : ℝ} (hbound0 : 0 ≤ bound)
    (hbound : ∀ action environment, |utility action environment| ≤ bound)
    (law : FinDist A) (environment : Q) :
    ‖regretPayoff utility law environment‖ ≤
      Real.sqrt (Fintype.card A) * (2 * bound) := by
  apply euclidean_norm_le_coordinate_bound _ (by positivity)
  intro action
  rw [regretPayoff_ofLp]
  have hexpect := FinDist.abs_expect_le_of_abs_bound law
    (fun other => utility other environment) (fun other _ => hbound other environment)
  calc
    _ ≤ |utility action environment| + |law.expect (fun other => utility other environment)| :=
      abs_sub _ _
    _ ≤ 2 * bound := by linarith [hbound action environment]

/-- An explicit structural constant for the local Euclidean regret payoff. -/
def counterfactualPayoffBound (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)] (bound : ℝ) : ℝ :=
  Real.sqrt (Fintype.card (M.Choice who site.1)) *
    (2 * ((Fintype.card (M.InformationHistory who site.1) : ℝ) * bound))

/-- The structural payoff constant is nonnegative for a lawful payoff bound. -/
theorem counterfactualPayoffBound_nonneg (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)] {bound : ℝ} (hbound0 : 0 ≤ bound) :
    0 ≤ counterfactualPayoffBound M who site bound := by
  unfold counterfactualPayoffBound
  positivity

/-- The norm premise of regret matching is discharged from bounded game
payoffs and finite information fibers, uniformly over every profile and law. -/
theorem canonical_regretPayoff_norm_le (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who) [Fintype (M.InformationHistory who site.1)]
    (payoff : E.History → ℝ) {bound : ℝ} (hbound0 : 0 ≤ bound)
    (hbound : ∀ history, |payoff history| ≤ bound) (fuel : ℕ)
    (law : FinDist (M.Choice who site.1)) (strategy : Profile M.behavioralSignature) :
    ‖regretPayoff (fun choice current =>
        M.counterfactualActionUtility current who site payoff fuel choice) law strategy‖ ≤
      counterfactualPayoffBound M who site bound := by
  apply regretPayoff_norm_le_of_abs_bound _ (mul_nonneg (Nat.cast_nonneg _) hbound0)
  intro choice current
  exact counterfactualValue_abs_le M current who site ((current who).commit site.1 choice)
    payoff hbound0 hbound fuel

end GameTheory.ReBeL
