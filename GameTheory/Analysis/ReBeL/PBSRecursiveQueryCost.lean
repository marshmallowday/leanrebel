/-
# Actual fresh-query visits and payoff-diameter replacement costs

Missing PBSs and stopped stages retain the incumbent. Only actual fresh
queries can lose value. This gives a second, solver-independent cap even on
unsupported histories; it does not claim that queries become rare as T grows.
-/

import GameTheory.Analysis.ReBeL.PBSRecursiveGroupedSecurity
import GameTheory.Math.Probability.FinDistRangeError

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u v
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable {K : Type v}

/-- Actual invocation of a fresh resolver: positive live fuel and a saved PBS.
Unsupported hidden histories still count as queries; missing PBSs do not. -/
def pbsRecursiveQueryEvent (fuel : Nat) :
    Set (PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K)) :=
  {state | cfrDCutLive fuel state.history = true ∧ state.belief.isSome = true}

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- No actual query means zero signed native replacement cost, including the
entire late tail. The statement covers missing PBSs and true stopped states. -/
theorem pbsRecursiveReplacement_inactive
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (config : PBSRecursiveResolveConfig.{u}) (remaining : Nat)
    (state : PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K))
    (inactive : state ∉ pbsRecursiveQueryEvent M config.fuel) (value : E.History → ℝ) :
    carriedReplacementSignedLoss (fullInformation.{0, u, u, u, u, u} M) initial unknown who
      (pbsRecursiveConfigStage M fallback payoff bound initial config) remaining state value =
        0 := by
  unfold carriedReplacementSignedLoss carriedReplacementOutcome
  rw [FinDist.expect_bind, carriedMemoryStep_selected_late_expect]
  by_cases live : cfrDCutLive config.fuel state.history = true
  · have stageLive :
        cfrDCutLive (pbsRecursiveConfigStage M fallback payoff bound initial config).fuel
          state.history = true := live
    rw [if_pos stageLive]
    cases stored : state.belief with
    | none =>
        simp only [pbsRecursiveConfigStage, pbsRecursiveDepthStage,
          pbsRecursiveDepthResolver, FinDist.expect_pure, carriedSelectedTail, sub_self]
    | some _belief =>
        exact False.elim (inactive ⟨live, by rw [stored]; rfl⟩)
  · have stageStopped :
        ¬ cfrDCutLive (pbsRecursiveConfigStage M fallback payoff bound initial config).fuel
          state.history = true := live
    rw [if_neg stageStopped]
    have stopped := cfrDCutValue_stopped (fullInformation.{0, u, u, u, u, u} M)
      (Profile.update unknown who
        (carriedMemoryProfile (fullInformation.{0, u, u, u, u, u} M) initial state.iteration who))
      (fun history => ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom
        (Profile.update unknown who
          (carriedMemoryProfile (fullInformation.{0, u, u, u, u, u} M)
            initial state.iteration who)) remaining history).expect value)
      (pbsRecursiveConfigStage M fallback payoff bound initial config).fuel state.history
      stageStopped
    rw [← FinDist.expect_bind,
      ← (fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom_add] at stopped
    exact sub_eq_zero.mpr stopped

/-- Payoff diameter times actual query mass bounds a stage's signed loss.
No support domination, Nash premise, positive tolerance or noise bound is used. -/
theorem pbsRecursiveReplacement_le_queryMass
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (config : PBSRecursiveResolveConfig.{u}) (remaining : Nat)
    (states : FinDist (PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K)))
    (value : E.History → ℝ) (lower upper : ℝ)
    (lowerBound : ∀ h, lower ≤ value h) (upperBound : ∀ h, value h ≤ upper) :
    states.expect (fun state => carriedReplacementSignedLoss
      (fullInformation.{0, u, u, u, u, u} M) initial unknown who
      (pbsRecursiveConfigStage M fallback payoff bound initial config) remaining state value) ≤
    (upper - lower) * states.probOf (pbsRecursiveQueryEvent M config.fuel) := by
  have estimate := FinDist.expect_bind_sub_le_of_eq_off_event_range states
    (pbsRecursiveQueryEvent M config.fuel)
    (carriedSelectedTail (fullInformation.{0, u, u, u, u, u} M) initial unknown who
      ((pbsRecursiveConfigStage M fallback payoff bound initial config).fuel + remaining))
    (carriedReplacementOutcome (fullInformation.{0, u, u, u, u, u} M) initial unknown who
      (pbsRecursiveConfigStage M fallback payoff bound initial config) remaining)
    value lower upper lowerBound upperBound
    (fun state _ inactive => sub_eq_zero.mp
      (pbsRecursiveReplacement_inactive M fallback payoff bound initial unknown who
        config remaining state inactive value))
  simpa only [carriedReplacementSignedLoss, FinDist.expect_sub, FinDist.expect_bind]
    using estimate

/-- Expected number of fresh queries along the actual full-state native law.
This count can exceed one. All private draw/PBS correlations are retained. -/
def pbsRecursiveQueryVisits
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (configs : List PBSRecursiveResolveConfig.{u})
    (states : FinDist (PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K))) : ℝ :=
  FinDist.sequenceEventMass
    (fun config => carriedMemoryStep (fullInformation.{0, u, u, u, u, u} M) initial unknown who
      (pbsRecursiveConfigStage M fallback payoff bound initial config))
    (fun config => pbsRecursiveQueryEvent M config.fuel) configs states

/-- Native signed telescoping costs at most payoff diameter times the expected
query count, with the same retained draw used through every stage and late tail. -/
theorem carriedSignedSequenceLoss_le_queryVisits
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (finalFuel : Nat) (configs : List PBSRecursiveResolveConfig.{u})
    (states : FinDist (PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K)))
    (value : E.History → ℝ) (lower upper : ℝ)
    (lowerBound : ∀ h, lower ≤ value h) (upperBound : ∀ h, value h ≤ upper) :
    carriedSignedSequenceLoss (fullInformation.{0, u, u, u, u, u} M) initial unknown who
      finalFuel value (configs.map (pbsRecursiveConfigStage M fallback payoff bound initial))
      states ≤
    (upper - lower) * pbsRecursiveQueryVisits M fallback payoff bound initial unknown who
      configs states := by
  induction configs generalizing states with
  | nil =>
      simp only [List.map_nil, carriedSignedSequenceLoss, pbsRecursiveQueryVisits,
        FinDist.sequenceEventMass, mul_zero, le_refl]
  | cons config configs ih =>
      rw [pbsRecursiveQueryVisits, FinDist.sequenceEventMass, mul_add]
      dsimp only [List.map, carriedSignedSequenceLoss]
      exact add_le_add
        (pbsRecursiveReplacement_le_queryMass M fallback payoff bound initial unknown who
          config _ states value lower upper lowerBound upperBound) (ih _)

/-- An established initial guarantee inherits the diameter/query cap.
The native execution is unchanged and the unknown opponent remains arbitrary. -/
theorem privateRecursiveResolve_inherits_queryVisits
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (seed : FinDist K)
    (plays : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (cut finalFuel : Nat) (configs : List PBSRecursiveResolveConfig.{u})
    (value : E.History → ℝ) (lower upper : ℝ)
    (lowerBound : ∀ h, lower ≤ value h) (upperBound : ∀ h, value h ≤ upper)
    (security : ℝ)
    (prior : security ≤ (privateCarriedContinue (fullInformation.{0, u, u, u, u, u} M)
      seed plays unknown who cut
      (carriedResolveFuel (fullInformation.{0, u, u, u, u, u} M) finalFuel
        (configs.map (pbsRecursiveConfigStage M fallback payoff bound plays)))).expect value) :
    security - (upper - lower) * pbsRecursiveQueryVisits M fallback payoff bound plays
      unknown who configs
      ((privateCarriedPrefix (fullInformation.{0, u, u, u, u, u} M)
        seed plays unknown who cut).map
        (enterCarriedMemory (fullInformation.{0, u, u, u, u, u} M))) ≤
    (privateRecursiveResolve (fullInformation.{0, u, u, u, u, u} M) seed plays unknown who
      cut finalFuel (configs.map (pbsRecursiveConfigStage M fallback payoff bound plays))).expect
      value := by
  have inherited := privateRecursiveResolve_inherits_signedLoss
    (fullInformation.{0, u, u, u, u, u} M) seed plays unknown who cut finalFuel
    (configs.map (pbsRecursiveConfigStage M fallback payoff bound plays)) value security prior
  have budget := carriedSignedSequenceLoss_le_queryVisits M fallback payoff bound plays
    unknown who finalFuel configs
    ((privateCarriedPrefix (fullInformation.{0, u, u, u, u, u} M)
      seed plays unknown who cut).map
      (enterCarriedMemory (fullInformation.{0, u, u, u, u, u} M)))
    value lower upper lowerBound upperBound
  linarith only [inherited, budget]

end GameTheory.ReBeL
