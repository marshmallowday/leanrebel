/-
# Opponent-uniform potential accounting for native recursive security

All grouping is computed from actual native states. The full private memory
law advances with the original resolver. The opposing player's Nash condition
handles every unknown opponent. Conditional root discrepancy, incumbent surplus
and actual unsupported mass remain explicit and are not asserted small.
-/

import GameTheory.Analysis.ReBeL.PBSRecursivePotential
import GameTheory.Analysis.ReBeL.CFRDRecursiveSecurity

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u v
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {K : Type v}

/-- Actual group frequencies and conditional history marginals are charged
before each native step. Unsupported sampling retains its actual-mass penalty. -/
def pbsRecursivePotentialBudget
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (finalFuel : Nat) :
    List PBSRecursiveResolveConfig.{u} →
      FinDist (PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
        (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K)) → ℝ
  | [], _ => 0
  | config :: configs, states =>
      let remaining := carriedResolveFuel (fullInformation.{0, u, u, u, u, u} M) finalFuel
        (configs.map (pbsRecursiveConfigStage M fallback payoff bound initial))
      pbsRecursivePotentialCharge M fallback payoff bound initial unknown who config remaining
        states (pbsRecursiveNativeGroupKey M initial config) id +
        2 * bound * states.probOf {state | pbsCarriedCFRException M config.fuel state} +
      pbsRecursivePotentialBudget fallback payoff bound initial unknown who finalFuel configs
        (states.bind (carriedMemoryStep (fullInformation.{0, u, u, u, u, u} M)
          initial unknown who (pbsRecursiveConfigStage M fallback payoff bound initial config)))

/-- The canonical key proves compatibility at every stage, including after
native private memory updates. No caller-supplied grouping certificate is used. -/
theorem pbsRecursiveRecomputedBudget_le_potentialBudget
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (finalFuel : Nat) (configs : List PBSRecursiveResolveConfig.{u})
    (aligned : PBSRecursiveNashAligned finalFuel configs)
    (states : FinDist (PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K))) :
    pbsRecursiveRecomputedBudget M fallback payoff bound initial unknown who finalFuel
      (payoff who) bound configs states ≤
    pbsRecursivePotentialBudget M fallback payoff bound initial unknown who finalFuel configs
      states := by
  revert aligned
  induction configs generalizing states with
  | nil => intro _; exact le_refl _
  | cons config configs ih =>
      intro aligned
      obtain ⟨noiseBound, positive, horizon, tailAligned⟩ := aligned
      have alignedFuel : config.cuts.sum = config.fuel +
          carriedResolveFuel (fullInformation.{0, u, u, u, u, u} M) finalFuel
            (configs.map (pbsRecursiveConfigStage M fallback payoff bound initial)) := by
        simpa only [carriedResolveFuel_config_eq] using horizon
      dsimp only [pbsRecursiveRecomputedBudget, pbsRecursivePotentialBudget]
      apply add_le_add
      · apply add_le_add _ le_rfl
        exact pbsRecursiveRecomputedLoss_expect_le_potentialCharge M fallback payoff zeroSum
          bound nonneg bounded initial unknown who config _ noiseBound positive alignedFuel
          states (pbsRecursiveNativeGroupKey M initial config) id
          (pbsRecursiveNativeGroupKey_compatible M fallback payoff bound initial config states)
      · exact ih _ tailAligned

/-- The potential schedule controls the original native signed telescope,
including the actual unsupported mass and all retained late fuel. -/
theorem carriedSignedSequenceLoss_le_potentialBudget
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (finalFuel : Nat) (configs : List PBSRecursiveResolveConfig.{u})
    (aligned : PBSRecursiveNashAligned finalFuel configs)
    (states : FinDist (PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K))) :
    carriedSignedSequenceLoss (fullInformation.{0, u, u, u, u, u} M) initial unknown who finalFuel
      (payoff who) (configs.map (pbsRecursiveConfigStage M fallback payoff bound initial))
      states ≤
    pbsRecursivePotentialBudget M fallback payoff bound initial unknown who finalFuel configs
      states :=
  (carriedSignedSequenceLoss_le_recomputedBudget M fallback payoff bound initial unknown who
    finalFuel (payoff who) bound (bounded who) configs states).trans
      (pbsRecursiveRecomputedBudget_le_potentialBudget M fallback payoff zeroSum bound nonneg
        bounded initial unknown who finalFuel configs aligned states)

variable [∀ who info, Fintype ((fullInformation.{0, u, u, u, u, u} M).Choice who info)]
variable [∀ who, DecidableEq ((fullInformation.{0, u, u, u, u, u} M).InfoState who)]

/-- The actual finite noisy sampled parent supplies initial security. Every
later solve uses the canonical potential budget, with prediction error, finite
parent iterations and twice the child loss still separate. This does not
assert that the incumbent surplus or conditional root/support terms are small. -/
theorem cfrDRecursivePotential_security
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (cut finalFuel : Nat) (configs : List PBSRecursiveResolveConfig.{u})
    (bound error loss : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ player h, |payoff player h| ≤ bound) (noise : CFRDPredictionNoise M)
    (noiseBound : ∀ n trunk player info, |noise n trunk player info| ≤ error)
    (reference : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (equilibrium : IsNash ((fullInformation.{0, u, u, u, u, u} M).toBehavioralGameForm
      (cut + pbsRecursiveConfigFuel finalFuel configs))
      (euPreference (fun h player => payoff player h)) reference)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (who : Fin 2) (t : Nat) [NeZero t]
    (aligned : PBSRecursiveNashAligned finalFuel configs) :
    let remaining := pbsRecursiveConfigFuel finalFuel configs
    let plays := fun n : Fin t => cfrDDepthPlay (fullInformation.{0, u, u, u, u, u} M)
      (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut remaining
      (cfrDConstructedSampledInformationOracle M fallback payoff cut remaining
        bound loss noise) n.val
    ((fullInformation.{0, u, u, u, u, u} M).runBehavioral reference
      (cut + remaining)).expect (payoff who) -
      (cfrDDepthAverageErrorFloor (fullInformation.{0, u, u, u, u, u} M) (fullObservationClock M)
          (cfrDInformationFallback M fallback) cut remaining error loss +
        cfrDDepthAverageFiniteFactor (fullInformation.{0, u, u, u, u, u} M) (fullObservationClock M)
          (cfrDInformationFallback M fallback) cut remaining bound / Real.sqrt t +
        pbsRecursivePotentialBudget M fallback payoff bound plays unknown who finalFuel configs
          ((privateCarriedPrefix (fullInformation.{0, u, u, u, u, u} M)
            (cfrIterationLaw t) plays unknown who cut).map
            (enterCarriedMemory (fullInformation.{0, u, u, u, u, u} M)))) ≤
      (privateRecursiveResolve (fullInformation.{0, u, u, u, u, u} M)
        (cfrIterationLaw t) plays unknown who cut finalFuel
        (configs.map (pbsRecursiveConfigStage M fallback payoff bound plays))).expect
          (payoff who) := by
  intro remaining plays
  have security := cfrDRecursiveRecomputed_security M fallback payoff zeroSum cut finalFuel
    configs bound error loss hb he hl bounded noise noiseBound reference equilibrium unknown who t
  have budget := pbsRecursiveRecomputedBudget_le_potentialBudget M fallback payoff zeroSum
    bound hb bounded plays unknown who finalFuel configs aligned
    ((privateCarriedPrefix (fullInformation.{0, u, u, u, u, u} M)
            (cfrIterationLaw t) plays unknown who cut).map
      (enterCarriedMemory (fullInformation.{0, u, u, u, u, u} M)))
  dsimp only at security
  linarith only [security, budget]

end GameTheory.ReBeL
