/-
# Training output of the structurally recursive PBS solver

The returned policy is the existing finite-budget own-reach average. The
additional vector is a uniform mean of backups on exactly that parent's noisy
learning trace, with its actual recursive child and computed number of rounds.
A zero-length schedule returns the input conditional payoff without a query.
-/

import GameTheory.Analysis.ReBeL.PBSComposedValueTarget
import GameTheory.Analysis.ReBeL.PBSRecursiveDepth

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
variable (bound : ℝ) {observations : List M.PublicSignal}
variable (belief : PublicBelief (fullInformation M).toInfoSignals observations)

/-- Exactly the parent's computed count; the empty schedule has one constant
value sample and performs no fictitious empty uniform draw. -/
def pbsRecursiveTargetRounds (cuts : List Nat) (tolerance : ℝ) : Nat :=
  match cuts with
  | [] => 1
  | cut :: tail =>
      pbsRootDepthBudgetRounds M belief.law fallback cut tail.sum bound
        (pbsDepthAllocationError
          (pbsRootDepthErrorFactor M belief.law fallback cut tail.sum) tolerance)
        (tolerance / 8) tolerance

/-- Every training mean uses a nonempty carrier. -/
instance pbsRecursiveTargetRounds_neZero (cuts : List Nat) (tolerance : ℝ) :
    NeZero (pbsRecursiveTargetRounds M fallback bound belief cuts tolerance) := by
  cases cuts with
  | nil => exact ⟨Nat.one_ne_zero⟩
  | cons cut tail =>
      dsimp only [pbsRecursiveTargetRounds]
      infer_instance

/-- Only the current node's allocated prediction error enters its backup
error; child solve error instead enters the finite-time policy guarantee. -/
def pbsRecursiveTargetError (cuts : List Nat) (tolerance : ℝ) : ℝ :=
  match cuts with
  | [] => 0
  | cut :: tail =>
      pbsDepthAllocationError
        (pbsRootDepthErrorFactor M belief.law fallback cut tail.sum) tolerance

/-- The actual recursive parent's backed-up per-type value at one round.
The solver is given only its modeled PBS, not a hidden actual history. -/
def pbsRecursiveTargetRound (noise : PBSRecursiveDepthNoise.{u})
    (cuts : List Nat) (tolerance : ℝ) (round : Nat) (who : Fin 2)
    (type : (fullInformation M).InfoState who) : ℝ := by
  cases cuts with
  | nil =>
      exact conditionalOracleValue belief.law
        (fun h => (fullInformation M).infoOf who h.trace) (payoff who) type
  | cons cut tail =>
      letI : Fintype (pbsRootProtocol belief.law).History := pbsRootHistoryFintype belief.law
      let error := pbsDepthAllocationError
        (pbsRootDepthErrorFactor M belief.law fallback cut tail.sum) tolerance
      exact pbsComposedValueTarget M belief fallback payoff cut tail.sum (tolerance / 8)
        (pbsRecursiveDepth noise tail (pbsRootProtocol belief.law)
          (pbsRootInformation (fullInformation M) belief.law)
          (pbsRootDepthFallback M belief.law fallback) (pbsRootPayoff belief.law payoff) bound)
        (noise E M belief.law error) round who type

/-- Proof-only same-round original continuation comparator. Its full rollout
is not evaluated by pbsRecursiveTargetRound or the training output. -/
def pbsRecursiveOriginalRound (noise : PBSRecursiveDepthNoise.{u})
    (cuts : List Nat) (tolerance : ℝ) (round : Nat) (who : Fin 2)
    (type : (fullInformation M).InfoState who) : ℝ := by
  cases cuts with
  | nil =>
      exact conditionalOracleValue belief.law
        (fun h => (fullInformation M).infoOf who h.trace) (payoff who) type
  | cons cut tail =>
      letI : Fintype (pbsRootProtocol belief.law).History := pbsRootHistoryFintype belief.law
      let error := pbsDepthAllocationError
        (pbsRootDepthErrorFactor M belief.law fallback cut tail.sum) tolerance
      exact pbsComposedOriginalTarget M belief fallback payoff cut tail.sum (tolerance / 8)
        (pbsRecursiveDepth noise tail (pbsRootProtocol belief.law)
          (pbsRootInformation (fullInformation M) belief.law)
          (pbsRootDepthFallback M belief.law fallback) (pbsRootPayoff belief.law payoff) bound)
        (noise E M belief.law error) round who type

/-- Numerical propagation applies at every recursively rooted node because
the noise contract quantifies over its actual protocol and allocated error. -/
theorem pbsRecursiveTargetRound_error (noise : PBSRecursiveDepthNoise.{u})
    (noiseBound : PBSRecursiveDepthNoiseBound noise) (cuts : List Nat)
    (tolerance : ℝ) (positive : 0 < tolerance) (round : Nat) (who : Fin 2)
    (type : (fullInformation M).InfoState who) :
    |pbsRecursiveTargetRound M fallback payoff bound belief noise cuts tolerance round who type -
      pbsRecursiveOriginalRound M fallback payoff bound belief noise cuts tolerance round
        who type| ≤ pbsRecursiveTargetError M fallback belief cuts tolerance := by
  cases cuts with
  | nil => simp only [pbsRecursiveTargetRound, pbsRecursiveOriginalRound,
      pbsRecursiveTargetError, sub_self, abs_zero, le_refl]
  | cons cut tail =>
      let _ : Fintype (pbsRootProtocol belief.law).History := pbsRootHistoryFintype belief.law
      apply pbsComposedValueTarget_error
      · exact (pbsDepthAllocationError_pos _ tolerance positive).le
      · exact noiseBound M belief.law _
          (pbsDepthAllocationError_pos _ tolerance positive).le

/-- The added vector uses the same finite count as the policy computation. -/
def pbsRecursiveValueTarget (noise : PBSRecursiveDepthNoise.{u})
    (cuts : List Nat) (tolerance : ℝ) (who : Fin 2)
    (type : (fullInformation M).InfoState who) : ℝ :=
  cfrDValueTargetMean
    (fun n => pbsRecursiveTargetRound M fallback payoff bound belief noise cuts tolerance n who)
    (pbsRecursiveTargetRounds M fallback bound belief cuts tolerance) type

/-- An empty schedule returns the current conditional payoff exactly. -/
theorem pbsRecursiveValueTarget_nil (noise : PBSRecursiveDepthNoise.{u})
    (tolerance : ℝ) (who : Fin 2) (type : (fullInformation M).InfoState who) :
    pbsRecursiveValueTarget M fallback payoff bound belief noise [] tolerance who type =
      conditionalOracleValue belief.law
        (fun h => (fullInformation M).infoOf who h.trace) (payoff who) type := by
  exact cfrDValueTargetMean_one _ type

/-- No inverse root mass or number-of-rounds factor is incurred. The mean
comparator retains the actual same-round decoded policies, not the final one. -/
theorem pbsRecursiveValueTarget_error (noise : PBSRecursiveDepthNoise.{u})
    (noiseBound : PBSRecursiveDepthNoiseBound noise) (cuts : List Nat)
    (tolerance : ℝ) (positive : 0 < tolerance) (who : Fin 2)
    (type : (fullInformation M).InfoState who) :
    |pbsRecursiveValueTarget M fallback payoff bound belief noise cuts tolerance who type -
      cfrDValueTargetMean
        (fun n => pbsRecursiveOriginalRound M fallback payoff bound belief
          noise cuts tolerance n who)
        (pbsRecursiveTargetRounds M fallback bound belief cuts tolerance) type| ≤
      pbsRecursiveTargetError M fallback belief cuts tolerance := by
  apply cfrDValueTargetMean_error
  intro n _
  exact pbsRecursiveTargetRound_error M fallback payoff bound belief
    noise noiseBound cuts tolerance positive n who type

/-- A search result contains both policy and infostate vector. The proof-only
full comparator is not a component and no correctness certificate is an input. -/
def pbsRecursiveTrainingOutput (noise : PBSRecursiveDepthNoise.{u})
    (cuts : List Nat) (tolerance : ℝ) :
    Profile (fullInformation M).behavioralSignature ×
      ((who : Fin 2) → (fullInformation M).InfoState who → ℝ) :=
  (pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance,
    pbsRecursiveValueTarget M fallback payoff bound belief noise cuts tolerance)

/-- The new result leaves the original recursive policy computation unchanged. -/
theorem pbsRecursiveTrainingOutput_policy (noise : PBSRecursiveDepthNoise.{u})
    (cuts : List Nat) (tolerance : ℝ) :
    (pbsRecursiveTrainingOutput M fallback payoff bound belief noise cuts tolerance).1 =
      pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance := rfl

/-- Both results concern the same recursively computed search. Policy accuracy
uses the proved smaller-solver induction and positive finite allocations;
target accuracy uses the actual same-round continuation mean. Neither claims
last-iterate convergence, Nash value-vector convergence or network convergence. -/
theorem pbsRecursiveTrainingOutput_correct (noise : PBSRecursiveDepthNoise.{u})
    (noiseBound : PBSRecursiveDepthNoiseBound noise) (cuts : List Nat)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (hb : 0 ≤ bound)
    (bounded : ∀ who h, |payoff who h| ≤ bound)
    (tolerance : ℝ) (positive : 0 < tolerance) :
    IsNash (behavioralBeliefForm (fullInformation M) belief cuts.sum)
        (euPreferenceWithin tolerance (fun h who => payoff who h))
        (pbsRecursiveTrainingOutput M fallback payoff bound belief noise cuts tolerance).1 ∧
      ∀ who type,
        |(pbsRecursiveTrainingOutput M fallback payoff bound belief noise cuts tolerance).2
            who type -
          cfrDValueTargetMean
            (fun n => pbsRecursiveOriginalRound M fallback payoff bound belief
              noise cuts tolerance n who)
            (pbsRecursiveTargetRounds M fallback bound belief cuts tolerance) type| ≤
          pbsRecursiveTargetError M fallback belief cuts tolerance := by
  constructor
  · exact pbsRecursiveDepth_isNash noise noiseBound cuts M fallback payoff zeroSum bound hb
      bounded belief tolerance positive
  · intro who type
    exact pbsRecursiveValueTarget_error M fallback payoff bound belief noise noiseBound
      cuts tolerance positive who type

end GameTheory.ReBeL
