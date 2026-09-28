/-
# Fresh recursive re-solving with a recomputed value term

The average is used only to evaluate a comparison value at each actual native
state. The next state still comes from the original private resolver, including
the joint law of its retained profile, history and saved MODEL posterior.
-/

import GameTheory.Analysis.ReBeL.PBSRecursivePosteriorValue

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {K : Type*}

/-- A schedule records every actual recursive solver configuration separately.
Changing a tolerance or noise allocation is not silently treated as a replay. -/
structure PBSRecursiveResolveConfig where
  noise : PBSRecursiveDepthNoise.{u}
  cuts : List Nat
  tolerance : ℝ
  fuel : Nat

/-- Convert a recorded configuration to the existing, unchanged native stage. -/
def pbsRecursiveConfigStage
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (config : PBSRecursiveResolveConfig.{u}) : CarriedResolveStage (fullInformation M) K :=
  pbsRecursiveDepthStage config.noise config.cuts M fallback payoff bound config.tolerance
    config.fuel initial

/-- A proof-side comparison law. It uses the fresh average at the actual saved
PBS, and preserves missing-belief and stopped behavior. It does not update any
native memory and is not substituted for the deployed resolver. -/
def pbsRecursiveRecomputedOutcome
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (config : PBSRecursiveResolveConfig.{u}) (remaining : Nat)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) : FinDist E.History :=
  if cfrDCutLive config.fuel state.history = true then
    match state.belief with
    | none => carriedSelectedTail (fullInformation M) initial unknown who
        (config.fuel + remaining) state
    | some belief => (fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (pbsRecursiveDepth config.noise config.cuts E M fallback payoff bound belief
            config.tolerance who)) (config.fuel + remaining) state.history
  else carriedSelectedTail (fullInformation M) initial unknown who remaining state

/-- The same private draw is retained through stage plus late fuel. On model
support its value equals the recomputed average; no incumbent equality is assumed. -/
theorem pbsRecursiveRecomputedOutcome_value
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (config : PBSRecursiveResolveConfig.{u}) (remaining : Nat)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))
    (outside : ¬ pbsCarriedCFRException M config.fuel state) (value : E.History → ℝ) :
    (carriedReplacementOutcome (fullInformation M) initial unknown who
      (pbsRecursiveConfigStage M fallback payoff bound initial config) remaining state).expect
      value =
    (pbsRecursiveRecomputedOutcome M fallback payoff bound initial unknown who
      config remaining state).expect value := by
  unfold carriedReplacementOutcome
  rw [FinDist.expect_bind]
  by_cases live : cfrDCutLive config.fuel state.history = true
  · cases stored : state.belief with
    | none =>
        have stageLive :
            cfrDCutLive
              (pbsRecursiveConfigStage M fallback payoff bound initial config).fuel
              state.history = true := live
        rw [carriedMemoryStep_selected_late_expect, if_pos stageLive]
        simp only [pbsRecursiveConfigStage, pbsRecursiveDepthStage,
          pbsRecursiveDepthResolver, stored, FinDist.expect_pure,
          pbsRecursiveRecomputedOutcome, if_pos live, carriedSelectedTail]
    | some belief =>
        have supported : state.history ∈ belief.law.support := by
          by_contra absent
          apply outside
          refine ⟨live, ?_⟩
          simpa only [stored] using absent
        simp only [pbsRecursiveRecomputedOutcome, if_pos live, stored]
        exact pbsRecursiveDepthStage_selected_late_value M config.noise config.cuts
          fallback payoff bound config.tolerance initial unknown who config.fuel remaining
          state belief stored live supported value
  · have stageStopped :
        ¬ cfrDCutLive
          (pbsRecursiveConfigStage M fallback payoff bound initial config).fuel
          state.history = true := live
    rw [carriedMemoryStep_selected_late_expect, if_neg stageStopped,
      pbsRecursiveRecomputedOutcome, if_neg live]

/-- Signed old-minus-recomputed value, retaining gains and the full late fuel. -/
def pbsRecursiveRecomputedLoss
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (config : PBSRecursiveResolveConfig.{u}) (remaining : Nat)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) (value : E.History → ℝ) : ℝ :=
  (carriedSelectedTail (fullInformation M) initial unknown who
    (config.fuel + remaining) state).expect value -
  (pbsRecursiveRecomputedOutcome M fallback payoff bound initial unknown who
    config remaining state).expect value

/-- At a live saved PBS the computed term is precisely the old-versus-new
policy comparison. The PBS is unchanged inside this comparison and the other
player remains the same unknown opponent. -/
theorem pbsRecursiveRecomputedLoss_eq_policyValueChange
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (config : PBSRecursiveResolveConfig.{u}) (remaining : Nat)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))
    (belief : PublicBelief (fullInformation M).toInfoSignals
      (publicTrace (fullInformation M).toInfoSignals state.history.trace))
    (stored : state.belief = some belief) (live : cfrDCutLive config.fuel state.history = true)
    (value : E.History → ℝ) :
    pbsRecursiveRecomputedLoss M fallback payoff bound initial unknown who config
      remaining state value =
    recursivePolicyValueChange M
      (carriedMemoryProfile (fullInformation M) initial state.iteration)
      (pbsRecursiveDepth config.noise config.cuts E M fallback payoff bound belief
        config.tolerance) unknown who (config.fuel + remaining) (FinDist.pure state.history)
      value := by
  simp only [pbsRecursiveRecomputedLoss, pbsRecursiveRecomputedOutcome, if_pos live, stored,
    recursivePolicyValueChange, FinDist.expect_pure, carriedSelectedTail]

/-- The exact native signed loss is bounded by the computed average-value
change plus actual unsupported mass. Neither term is assumed to be small. -/
theorem pbsRecursiveReplacement_expected_loss_le
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (config : PBSRecursiveResolveConfig.{u}) (remaining : Nat)
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)))
    (value : E.History → ℝ) (limit : ℝ) (bounded : ∀ h, |value h| ≤ limit) :
    states.expect (fun state => carriedReplacementSignedLoss (fullInformation M)
      initial unknown who (pbsRecursiveConfigStage M fallback payoff bound initial config)
      remaining state value) ≤
    states.expect (fun state => pbsRecursiveRecomputedLoss M fallback payoff bound initial
      unknown who config remaining state value) +
      2 * limit * states.probOf {state | pbsCarriedCFRException M config.fuel state} := by
  have estimate := FinDist.expect_sub_le_of_eq_off_event states
    {state | pbsCarriedCFRException M config.fuel state}
    (fun state => (pbsRecursiveRecomputedOutcome M fallback payoff bound initial unknown who
      config remaining state).expect value)
    (fun state => (carriedReplacementOutcome (fullInformation M) initial unknown who
      (pbsRecursiveConfigStage M fallback payoff bound initial config) remaining state).expect
        value) limit
    (fun _ _ => FinDist.abs_expect_le_of_abs_bound _ value (fun h _ => bounded h))
    (fun _ _ => FinDist.abs_expect_le_of_abs_bound _ value (fun h _ => bounded h))
    (fun state _ outside => (pbsRecursiveRecomputedOutcome_value M fallback payoff bound
      initial unknown who config remaining state outside value).symm)
  simp only [carriedReplacementSignedLoss, pbsRecursiveRecomputedLoss, FinDist.expect_sub,
    pbsRecursiveConfigStage, pbsRecursiveDepthStage] at estimate ⊢
  linarith only [estimate]

/-- Full-state forward accounting for a schedule of actual fresh solvers.
Later costs are evaluated after the NATIVE step, never after the comparison
average. The support penalty therefore uses the actual joint memory law. -/
def pbsRecursiveRecomputedBudget
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (finalFuel : Nat) (value : E.History → ℝ) (limit : ℝ) :
    List PBSRecursiveResolveConfig.{u} →
      FinDist (PrivateIterationState (fullInformation M)
        (CarriedResolveMemory (fullInformation M) K)) → ℝ
  | [], _ => 0
  | config :: configs, states =>
      let remaining := carriedResolveFuel (fullInformation M) finalFuel
        (configs.map (pbsRecursiveConfigStage M fallback payoff bound initial))
      states.expect (fun state => pbsRecursiveRecomputedLoss M fallback payoff bound initial
        unknown who config remaining state value) +
        2 * limit * states.probOf {state | pbsCarriedCFRException M config.fuel state} +
      pbsRecursiveRecomputedBudget fallback payoff bound initial unknown who finalFuel
        value limit configs (states.bind (carriedMemoryStep (fullInformation M)
          initial unknown who (pbsRecursiveConfigStage M fallback payoff bound initial config)))

/-- The complete actual recursive signed loss consumes the computed budget. -/
theorem carriedSignedSequenceLoss_le_recomputedBudget
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (finalFuel : Nat) (value : E.History → ℝ) (limit : ℝ)
    (bounded : ∀ h, |value h| ≤ limit) (configs : List PBSRecursiveResolveConfig.{u})
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))) :
    carriedSignedSequenceLoss (fullInformation M) initial unknown who finalFuel value
      (configs.map (pbsRecursiveConfigStage M fallback payoff bound initial)) states ≤
    pbsRecursiveRecomputedBudget M fallback payoff bound initial unknown who finalFuel value
      limit configs states := by
  induction configs generalizing states with
  | nil => exact le_refl _
  | cons config configs ih =>
      dsimp only [List.map, carriedSignedSequenceLoss, pbsRecursiveRecomputedBudget]
      exact add_le_add
        (pbsRecursiveReplacement_expected_loss_le M fallback payoff bound initial unknown who
          config _ states value limit bounded) (ih _)

/-- An already proved initial security bound propagates to the actual fresh
recursive chain with the explicit recomputation and support budget. This
does not assert the printed theorem's small rate for that budget. -/
theorem privateRecursiveResolve_inherits_recomputedBudget
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (seed : FinDist K) (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (cut finalFuel : Nat) (configs : List PBSRecursiveResolveConfig.{u})
    (value : E.History → ℝ) (limit : ℝ) (bounded : ∀ h, |value h| ≤ limit)
    (lower : ℝ)
    (prior : lower ≤ (privateCarriedContinue (fullInformation M) seed plays unknown who cut
      (carriedResolveFuel (fullInformation M) finalFuel
        (configs.map (pbsRecursiveConfigStage M fallback payoff bound plays)))).expect value) :
    lower - pbsRecursiveRecomputedBudget M fallback payoff bound plays unknown who finalFuel
      value limit configs
        ((privateCarriedPrefix (fullInformation M) seed plays unknown who cut).map
          (enterCarriedMemory (fullInformation M))) ≤
    (privateRecursiveResolve (fullInformation M) seed plays unknown who cut finalFuel
      (configs.map (pbsRecursiveConfigStage M fallback payoff bound plays))).expect value := by
  have exactBound := privateRecursiveResolve_inherits_signedLoss (fullInformation M)
    seed plays unknown who cut finalFuel
    (configs.map (pbsRecursiveConfigStage M fallback payoff bound plays)) value lower prior
  have budget := carriedSignedSequenceLoss_le_recomputedBudget M fallback payoff bound plays
    unknown who finalFuel value limit bounded configs
    ((privateCarriedPrefix (fullInformation M) seed plays unknown who cut).map
      (enterCarriedMemory (fullInformation M)))
  linarith only [exactBound, budget]

end GameTheory.ReBeL
