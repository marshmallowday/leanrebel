/-
# Recursive security potentials against arbitrary opponents

The opponent's Nash deviation supplies a lower value bound for the fresh
strategy. Only the root law is transported. The old continuation surplus
over fresh self-play is explicit and can have either sign; it is not assumed
small or identified with the continuation selected by an earlier parent.
-/

import GameTheory.Analysis.ReBeL.PBSRecursiveGroupedValue

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u v w
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)

/-- The opposing player's Nash deviation secures the fresh self-play value
minus one tolerance against every unknown policy. No opponent agreement is
needed, and the self-play value is not asserted to equal the exact game value. -/
theorem behavioralNash_model_security
    {observations : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals observations)
    (fresh unknown : Profile M.behavioralSignature) (who : Fin 2) (fuel : Nat)
    (payoff : Fin 2 → E.History → ℝ) (error : ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (equilibrium : IsNash (behavioralBeliefForm M belief fuel)
      (euPreferenceWithin error (fun h player => payoff player h)) fresh) :
    (belief.law.bind (M.runBehavioralFrom fresh fuel)).expect (payoff who) - error ≤
      (belief.law.bind
        (M.runBehavioralFrom (Profile.update unknown who (fresh who)) fuel)).expect
          (payoff who) := by
  have deviation (player : Fin 2) :
      (belief.law.bind (M.runBehavioralFrom
        (Profile.update fresh player (unknown player)) fuel)).expect (payoff player) ≤
      (belief.law.bind (M.runBehavioralFrom fresh fuel)).expect (payoff player) + error := by
    have result := (isNash_iff (F := behavioralBeliefForm M belief fuel)
      (weaklyPrefers := euPreferenceWithin error (fun h p => payoff p h))
      fresh).mp equilibrium player (unknown player)
    rw [euPreferenceWithin_apply] at result
    simpa only [expectedUtility, behavioralBeliefForm, PublicBelief.continuationLaw] using result
  have hz (profile : Profile M.behavioralSignature) :
      (belief.law.bind (M.runBehavioralFrom profile fuel)).expect (payoff 1) =
        -(belief.law.bind (M.runBehavioralFrom profile fuel)).expect (payoff 0) :=
    zeroSum.expectedUtility_one _
  rcases (by decide : ∀ player : Fin 2, player = 0 ∨ player = 1) who with rfl | rfl
  · have opponent := deviation 1
    rw [hz, hz] at opponent
    rw [twoPlayer_cross_profile M unknown fresh]
    linarith only [opponent]
  · have opponent := deviation 0
    rw [hz, hz, ← twoPlayer_cross_profile M fresh unknown]
    linarith only [opponent]

variable [Fintype E.History]

/-- Transport only the root distribution while using the same actual opposing
policy on both sides. There is no execution charge comparing it with self-play. -/
theorem behavioralNash_root_security
    {observations : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals observations)
    (fresh unknown : Profile M.behavioralSignature) (who : Fin 2) (fuel : Nat)
    (actual : FinDist E.History) (payoff : Fin 2 → E.History → ℝ) (error bound : ℝ)
    (nonneg : 0 ≤ bound) (bounded : ∀ h, |payoff who h| ≤ bound)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (equilibrium : IsNash (behavioralBeliefForm M belief fuel)
      (euPreferenceWithin error (fun h player => payoff player h)) fresh) :
    (belief.law.bind (M.runBehavioralFrom fresh fuel)).expect (payoff who) - error -
        bound * FinDist.atomVariation actual belief.law ≤
      (actual.bind (M.runBehavioralFrom (Profile.update unknown who (fresh who)) fuel)).expect
        (payoff who) := by
  have security := behavioralNash_model_security M belief fresh unknown who fuel payoff
    error zeroSum equilibrium
  have transport := runBehavioralFrom_atomVariation_le M
    (Profile.update unknown who (fresh who)) (Profile.update unknown who (fresh who))
    fuel actual belief.law
  rw [executionKernelCharge_self, add_zero] at transport
  have discrepancy := (FinDist.abs_expect_sub_le_atomVariation
    (actual.bind (M.runBehavioralFrom (Profile.update unknown who (fresh who)) fuel))
    (belief.law.bind (M.runBehavioralFrom (Profile.update unknown who (fresh who)) fuel))
    (payoff who) bound bounded).trans (mul_le_mul_of_nonneg_left transport nonneg)
  have lower := (abs_le.mp discrepancy).1
  linarith only [security, lower]

/-- Signed incumbent surplus over the new computed self-play potential, plus
one root-law charge. This quantity need not be positive or small. -/
def nashSecurityPotential
    (old fresh unknown : Profile M.behavioralSignature) (who : Fin 2)
    (fuel : Nat) (actual model : FinDist E.History) (value : E.History → ℝ) (bound : ℝ) : ℝ :=
  (actual.bind (M.runBehavioralFrom (Profile.update unknown who (old who)) fuel)).expect value -
    (model.bind (M.runBehavioralFrom fresh fuel)).expect value +
    bound * FinDist.atomVariation actual model

variable [∀ who, Fintype (E.Action who)]

/-- The actual recursive solver supplies both players' Nash conditions.
The unknown opponent is arbitrary. The explicit incumbent surplus is not
dropped merely because the fresh policy is an accurate equilibrium. -/
theorem pbsRecursiveDepth_potential_replacement_le
    (noise : PBSRecursiveDepthNoise.{u}) (noiseBound : PBSRecursiveDepthNoiseBound noise)
    (cuts : List Nat) (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation.{0, u, u, u, u, u} M).toInfoSignals observations)
    (tolerance : ℝ) (positive : 0 < tolerance)
    (old unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (who : Fin 2) (actual : FinDist E.History) :
    let fresh := pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance
    recursivePolicyValueChange M old fresh unknown who cuts.sum actual (payoff who) ≤
      tolerance + nashSecurityPotential.{u} (E := E)
        (fullInformation.{0, u, u, u, u, u} M)
        old fresh unknown who cuts.sum actual belief.law (payoff who) bound := by
  intro fresh
  have equilibrium := @pbsRecursiveDepth_isNash.{u} noise noiseBound cuts E M
    inferInstance inferInstance fallback payoff zeroSum bound nonneg bounded
    observations belief tolerance positive
  have security := @behavioralNash_root_security.{u} E
    (fullInformation.{0, u, u, u, u, u} M) inferInstance observations belief
    fresh unknown who cuts.sum actual payoff tolerance bound nonneg (bounded who)
    zeroSum equilibrium
  unfold recursivePolicyValueChange nashSecurityPotential
  rw [FinDist.expect_sub]
  simp only [FinDist.expect_bind] at security ⊢
  linarith only [security]

/-- The finite private draw secures its own computed model value against
every seed-blind opponent. This uses the exact model root law, not a claim
that the native conditional history distribution equals the stored PBS. -/
theorem pbsRecursiveDepth_private_model_security
    (noise : PBSRecursiveDepthNoise.{u}) (noiseBound : PBSRecursiveDepthNoiseBound noise)
    (cuts : List Nat) (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation.{0, u, u, u, u, u} M).toInfoSignals observations)
    (tolerance : ℝ) (positive : 0 < tolerance)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (who : Fin 2) :
    let fresh := pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance
    (belief.law.bind
      ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom fresh cuts.sum)).expect
        (payoff who) - tolerance ≤
      (pbsRecursiveDepthDraw noise cuts M fallback payoff bound belief tolerance).expect
        (fun chosen => (belief.law.bind
          ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom
            (Profile.update unknown who (chosen who)) cuts.sum)).expect (payoff who)) := by
  intro fresh
  rw [pbsRecursiveDepthDraw_value noise cuts M fallback payoff bound belief tolerance
    unknown who cuts.sum (payoff who)]
  have equilibrium := @pbsRecursiveDepth_isNash.{u} noise noiseBound cuts E M
    inferInstance inferInstance fallback payoff zeroSum bound nonneg bounded
    observations belief tolerance positive
  exact @behavioralNash_model_security.{u} E
    (fullInformation.{0, u, u, u, u, u} M) observations belief
    fresh unknown who cuts.sum payoff tolerance zeroSum equilibrium

variable {K : Type v} {Label : Type w}

/-- The group's actual history law is transported once. Opposing-player Nash
supplies fresh security; the incumbent surplus over self-play remains signed. -/
theorem pbsRecursiveGroup_potential_loss_le
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (config : PBSRecursiveResolveConfig.{u}) (remaining : Nat) (query : PBSRecursiveGroupQuery M)
    (noiseBound : PBSRecursiveDepthNoiseBound config.noise) (positive : 0 < config.tolerance)
    (horizon : config.cuts.sum = config.fuel + remaining)
    (states : FinDist (PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K)))
    (agrees : ∀ state ∈ states.support,
      PBSRecursiveGroupAgrees M fallback payoff bound initial config query state) :
    states.expect (fun state => pbsRecursiveRecomputedLoss M fallback payoff bound initial
      unknown who config remaining state (payoff who)) ≤
    config.tolerance + nashSecurityPotential.{u} (E := E)
      (fullInformation.{0, u, u, u, u, u} M) query.old
      (pbsRecursiveDepth config.noise config.cuts E M fallback payoff bound query.belief
        config.tolerance) unknown who (config.fuel + remaining)
      (states.map (fun state => state.history)) query.belief.law (payoff who) bound := by
  rw [pbsRecursiveGroup_loss_eq M fallback payoff bound initial unknown who config remaining
    query states agrees]
  simpa only [horizon] using
    (pbsRecursiveDepth_potential_replacement_le.{u} (E := E) M config.noise noiseBound config.cuts
      fallback payoff zeroSum bound nonneg bounded query.belief config.tolerance positive
      query.old unknown who (states.map (fun state => state.history)))

/-- Expected cell bounds use the actual label frequencies. A missing query
keeps its signed conditional cost; it does not mean a zero-cost cell. -/
def pbsRecursivePotentialCharge
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (config : PBSRecursiveResolveConfig.{u}) (remaining : Nat)
    (states : FinDist (PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K)))
    (tag : PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K) → Label)
    (queries : Label → Option (PBSRecursiveGroupQuery M)) : ℝ :=
  (states.map tag).expect (fun label =>
    let cell := states.condOnFibre tag label
    match queries label with
    | none => cell.expect (fun state => pbsRecursiveRecomputedLoss M fallback payoff bound
        initial unknown who config remaining state (payoff who))
    | some query => config.tolerance + nashSecurityPotential.{u} (E := E)
        (fullInformation.{0, u, u, u, u, u} M) query.old
        (pbsRecursiveDepth config.noise config.cuts E M fallback payoff bound query.belief
          config.tolerance) unknown who (config.fuel + remaining)
        (cell.map (fun state => state.history)) query.belief.law (payoff who) bound)

/-- Disintegrate the actual joint memory distribution, then apply the
opponent-uniform potential bound. Neither independence nor equality with
the stored MODEL is assumed. -/
theorem pbsRecursiveRecomputedLoss_expect_le_potentialCharge
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (config : PBSRecursiveResolveConfig.{u}) (remaining : Nat)
    (noiseBound : PBSRecursiveDepthNoiseBound config.noise) (positive : 0 < config.tolerance)
    (horizon : config.cuts.sum = config.fuel + remaining)
    (states : FinDist (PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K)))
    (tag : PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K) → Label)
    (queries : Label → Option (PBSRecursiveGroupQuery M))
    (compatible : PBSRecursiveGroupingCompatible M fallback payoff bound initial config
      states tag queries) :
    states.expect (fun state => pbsRecursiveRecomputedLoss M fallback payoff bound initial
      unknown who config remaining state (payoff who)) ≤
    pbsRecursivePotentialCharge M fallback payoff bound initial unknown who config remaining
      states tag queries := by
  let value := fun state => pbsRecursiveRecomputedLoss M fallback payoff bound initial
    unknown who config remaining state (payoff who)
  calc
    _ = ((states.map tag).bind (states.condOnFibre tag)).expect value :=
      congrArg (fun law => law.expect value) (FinDist.eq_bind_condOnFibre states tag)
    _ = (states.map tag).expect (fun label => (states.condOnFibre tag label).expect value) :=
      FinDist.expect_bind _ _ _
    _ ≤ _ := by
      apply FinDist.expect_mono
      intro label present
      cases chosen : queries label with
      | none => exact le_refl _
      | some query =>
          exact pbsRecursiveGroup_potential_loss_le M fallback payoff zeroSum bound nonneg bounded
            initial unknown who config remaining query noiseBound positive horizon
            (states.condOnFibre tag label) (compatible label present query chosen)

/-- Leaving every group uncertified recovers the exact recomputed expectation
for any correlated joint law, including stopped and missing-PBS states. -/
theorem pbsRecursivePotentialCharge_none
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (config : PBSRecursiveResolveConfig.{u}) (remaining : Nat)
    (states : FinDist (PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K)))
    (tag : PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K) → Label) :
    pbsRecursivePotentialCharge M fallback payoff bound initial unknown who config remaining
      states tag (fun _ => none) =
    states.expect (fun state => pbsRecursiveRecomputedLoss M fallback payoff bound initial
      unknown who config remaining state (payoff who)) := by
  let value := fun state => pbsRecursiveRecomputedLoss M fallback payoff bound initial
    unknown who config remaining state (payoff who)
  calc
    _ = ((states.map tag).bind (states.condOnFibre tag)).expect value :=
      (FinDist.expect_bind _ _ _).symm
    _ = _ := congrArg (fun law => law.expect value)
      (FinDist.eq_bind_condOnFibre states tag).symm

end GameTheory.ReBeL
