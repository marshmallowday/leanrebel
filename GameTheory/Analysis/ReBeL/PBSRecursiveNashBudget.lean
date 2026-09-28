/-
# Nash transport budgets for the actual recursive memory schedule

Every fresh solver covers the entire stage-plus-late horizon. Model mismatch
is measured explicitly on the real state history; future states still follow
the native retained private draw and stored-posterior update.
-/

import GameTheory.Analysis.ReBeL.PBSRecursiveNashTransport

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u

/-- Total execution fuel of recorded configurations, including the late tail. -/
def pbsRecursiveConfigFuel (finalFuel : Nat) : List PBSRecursiveResolveConfig.{u} → Nat
  | [] => finalFuel
  | config :: configs => config.fuel + pbsRecursiveConfigFuel finalFuel configs

/-- Each actual solve has its numerical contract and positive tolerance, and
covers exactly the execution horizon used in its local replacement comparison. -/
def PBSRecursiveNashAligned (finalFuel : Nat) : List PBSRecursiveResolveConfig.{u} → Prop
  | [] => True
  | config :: configs =>
      PBSRecursiveDepthNoiseBound config.noise ∧ 0 < config.tolerance ∧
        config.cuts.sum = config.fuel + pbsRecursiveConfigFuel finalFuel configs ∧
        PBSRecursiveNashAligned finalFuel configs

variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {K : Type*}

/-- Configuration fuel agrees with the unchanged native stage runner. -/
theorem carriedResolveFuel_config_eq
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (finalFuel : Nat) (configs : List PBSRecursiveResolveConfig.{u}) :
    carriedResolveFuel (fullInformation M) finalFuel
      (configs.map (pbsRecursiveConfigStage M fallback payoff bound initial)) =
    pbsRecursiveConfigFuel finalFuel configs := by
  induction configs with
  | nil => rfl
  | cons config configs ih =>
      exact congrArg (config.fuel + ·) ih

/-- The live saved-belief branch uses a solver-derived tolerance plus measured
root/opponent transport. No-query branches retain their exact signed loss. -/
def pbsRecursiveNashEnvelope
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (config : PBSRecursiveResolveConfig.{u}) (remaining : Nat)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) : ℝ :=
  if cfrDCutLive config.fuel state.history = true then
    match state.belief with
    | some belief => config.tolerance + bound *
        nashReplacementTransport.{u} (E := E) (fullInformation.{0, u, u, u, u, u} M)
          (carriedMemoryProfile (fullInformation M) initial state.iteration)
          (pbsRecursiveDepth config.noise config.cuts E M fallback payoff bound belief
            config.tolerance) unknown who (config.fuel + remaining)
          (FinDist.pure state.history) belief.law
    | none => pbsRecursiveRecomputedLoss M fallback payoff bound initial unknown who
        config remaining state (payoff who)
  else pbsRecursiveRecomputedLoss M fallback payoff bound initial unknown who
    config remaining state (payoff who)

/-- The actual recomputed loss is bounded without any closeness premise on
the old and fresh own policies. The horizon equality includes all late fuel. -/
theorem pbsRecursiveRecomputedLoss_le_nashEnvelope
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (config : PBSRecursiveResolveConfig.{u}) (remaining : Nat)
    (noiseBound : PBSRecursiveDepthNoiseBound config.noise)
    (positive : 0 < config.tolerance) (horizon : config.cuts.sum = config.fuel + remaining)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) :
    pbsRecursiveRecomputedLoss M fallback payoff bound initial unknown who config remaining
      state (payoff who) ≤
    pbsRecursiveNashEnvelope M fallback payoff bound initial unknown who config remaining
      state := by
  classical
  by_cases live : cfrDCutLive config.fuel state.history = true
  · cases stored : state.belief with
    | none => simp only [pbsRecursiveNashEnvelope, if_pos live, stored, le_refl]
    | some belief =>
        simp only [pbsRecursiveNashEnvelope, if_pos live, stored]
        rw [pbsRecursiveRecomputedLoss_eq_policyValueChange (E := E) (K := K) M fallback
          payoff bound initial unknown who config remaining state belief stored live (payoff who)]
        simpa only [horizon] using
          (pbsRecursiveDepth_replacement_le.{u} (E := E) M config.noise noiseBound config.cuts
            fallback payoff zeroSum bound nonneg bounded belief config.tolerance positive
            (carriedMemoryProfile (fullInformation M) initial state.iteration) unknown who
            (FinDist.pure state.history))
  · simp only [pbsRecursiveNashEnvelope, if_neg live, le_refl]

/-- Accumulate the Nash envelope and the actual sampling-support penalty.
Forward laws are native full-state laws, not laws driven by comparison averages. -/
def pbsRecursiveNashBudget
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (finalFuel : Nat) :
    List PBSRecursiveResolveConfig.{u} →
      FinDist (PrivateIterationState (fullInformation M)
        (CarriedResolveMemory (fullInformation M) K)) → ℝ
  | [], _ => 0
  | config :: configs, states =>
      let remaining := carriedResolveFuel (fullInformation M) finalFuel
        (configs.map (pbsRecursiveConfigStage M fallback payoff bound initial))
      states.expect (pbsRecursiveNashEnvelope M fallback payoff bound initial unknown who
        config remaining) +
        2 * bound * states.probOf {state | pbsCarriedCFRException M config.fuel state} +
      pbsRecursiveNashBudget fallback payoff bound initial unknown who finalFuel configs
        (states.bind (carriedMemoryStep (fullInformation M) initial unknown who
          (pbsRecursiveConfigStage M fallback payoff bound initial config)))

/-- All aligned stages consume their actual solver guarantee in one forward
budget. No child Nash witness, model/actual posterior equality or reset is assumed. -/
theorem pbsRecursiveRecomputedBudget_le_nashBudget
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (finalFuel : Nat) (configs : List PBSRecursiveResolveConfig.{u})
    (aligned : PBSRecursiveNashAligned finalFuel configs)
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))) :
    pbsRecursiveRecomputedBudget M fallback payoff bound initial unknown who finalFuel
      (payoff who) bound configs states ≤
    pbsRecursiveNashBudget M fallback payoff bound initial unknown who finalFuel configs
      states := by
  revert aligned
  induction configs generalizing states with
  | nil => intro _; exact le_refl _
  | cons config configs ih =>
      intro aligned
      obtain ⟨noiseBound, positive, horizon, tailAligned⟩ := aligned
      have alignedFuel : config.cuts.sum = config.fuel +
          carriedResolveFuel (fullInformation M) finalFuel
            (configs.map (pbsRecursiveConfigStage M fallback payoff bound initial)) := by
        simpa only [carriedResolveFuel_config_eq] using horizon
      dsimp only [pbsRecursiveRecomputedBudget, pbsRecursiveNashBudget]
      apply add_le_add
      · apply add_le_add _ le_rfl
        apply FinDist.expect_mono
        intro state _
        exact pbsRecursiveRecomputedLoss_le_nashEnvelope M fallback payoff zeroSum bound
          nonneg bounded initial unknown who config _ noiseBound positive alignedFuel state
      · exact ih _ tailAligned

/-- The complete native signed loss is bounded by the Nash transport budget. -/
theorem carriedSignedSequenceLoss_le_nashBudget
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (finalFuel : Nat) (configs : List PBSRecursiveResolveConfig.{u})
    (aligned : PBSRecursiveNashAligned finalFuel configs)
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))) :
    carriedSignedSequenceLoss (fullInformation M) initial unknown who finalFuel (payoff who)
      (configs.map (pbsRecursiveConfigStage M fallback payoff bound initial)) states ≤
    pbsRecursiveNashBudget M fallback payoff bound initial unknown who finalFuel configs
      states :=
  (carriedSignedSequenceLoss_le_recomputedBudget M fallback payoff bound initial unknown who
    finalFuel (payoff who) bound (bounded who) configs states).trans
      (pbsRecursiveRecomputedBudget_le_nashBudget M fallback payoff zeroSum bound nonneg
        bounded initial unknown who finalFuel configs aligned states)

/-- Initial security propagates through the actual fresh recursive chain.
The extra root/opponent/support terms remain explicit and need not be small. -/
theorem privateRecursiveResolve_inherits_nashBudget
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    (seed : FinDist K) (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (cut finalFuel : Nat) (configs : List PBSRecursiveResolveConfig.{u})
    (aligned : PBSRecursiveNashAligned finalFuel configs) (lower : ℝ)
    (prior : lower ≤ (privateCarriedContinue (fullInformation M) seed plays unknown who cut
      (carriedResolveFuel (fullInformation M) finalFuel
        (configs.map (pbsRecursiveConfigStage M fallback payoff bound plays)))).expect
          (payoff who)) :
    lower - pbsRecursiveNashBudget M fallback payoff bound plays unknown who finalFuel configs
      ((privateCarriedPrefix (fullInformation M) seed plays unknown who cut).map
        (enterCarriedMemory (fullInformation M))) ≤
    (privateRecursiveResolve (fullInformation M) seed plays unknown who cut finalFuel
      (configs.map (pbsRecursiveConfigStage M fallback payoff bound plays))).expect
        (payoff who) := by
  have inherited := privateRecursiveResolve_inherits_recomputedBudget M fallback payoff bound
    seed plays unknown who cut finalFuel configs (payoff who) bound (bounded who) lower prior
  have budget := pbsRecursiveRecomputedBudget_le_nashBudget M fallback payoff zeroSum bound
    nonneg bounded plays unknown who finalFuel configs aligned
    ((privateCarriedPrefix (fullInformation M) seed plays unknown who cut).map
      (enterCarriedMemory (fullInformation M)))
  linarith only [inherited, budget]

end GameTheory.ReBeL
