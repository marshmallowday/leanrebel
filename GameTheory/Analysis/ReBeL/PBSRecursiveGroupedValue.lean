/-
# Conditional grouping for actual recursive replacement values

Group the native JOINT state law before comparing root distributions. A query
cell supplies computation identities, not a safety bound. Uncertified cells
retain their exact signed loss. This does not prove calibration for every
native schedule or identify distinct rooted/original solver computations.
-/

import GameTheory.Analysis.ReBeL.PBSRecursiveNashBudget

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u v w
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)

/-- A proof-side common query and incumbent for one group of native states.
This data is never supplied to the deployed resolver or unknown opponent. -/
structure PBSRecursiveGroupQuery where
  /-- Public observation index of this group's reference query. -/
  observations : List M.PublicSignal
  /-- Joint PBS used by the actual reference recursive computation. -/
  belief : PublicBelief (fullInformation.{0, u, u, u, u, u} M).toInfoSignals observations
  /-- Common carried incumbent, including all information-local choices. -/
  old : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {K : Type v} {Label : Type w}

/-- A cell is eligible only when each member is live and has exactly the
recorded incumbent and computed fresh policy. Equality of PBS laws alone is
not used to identify computations, and no payoff inequality is assumed. -/
def PBSRecursiveGroupAgrees
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (config : PBSRecursiveResolveConfig.{u}) (query : PBSRecursiveGroupQuery M)
    (state : PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K)) : Prop :=
  cfrDCutLive config.fuel state.history = true ∧
  carriedMemoryProfile (fullInformation.{0, u, u, u, u, u} M) initial state.iteration =
    query.old ∧
  state.belief.map (fun belief =>
    pbsRecursiveDepth config.noise config.cuts E M fallback payoff bound belief
      config.tolerance) =
    some (pbsRecursiveDepth config.noise config.cuts E M fallback payoff bound query.belief
      config.tolerance)

/-- Compatibility is checked only on positive-mass conditional native states.
Absent labels use the total conditional convention but are never charged. -/
def PBSRecursiveGroupingCompatible
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (config : PBSRecursiveResolveConfig.{u})
    (states : FinDist (PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K)))
    (tag : PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K) → Label)
    (queries : Label → Option (PBSRecursiveGroupQuery M)) : Prop :=
  ∀ label ∈ (states.map tag).support, ∀ query, queries label = some query →
    ∀ state ∈ (states.condOnFibre tag label).support,
      PBSRecursiveGroupAgrees M fallback payoff bound initial config query state

/-- A common computation allows the signed value to be averaged over the
conditional history marginal first. Hidden-state correlation is preserved. -/
theorem pbsRecursiveGroup_loss_eq
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (config : PBSRecursiveResolveConfig.{u}) (remaining : Nat) (query : PBSRecursiveGroupQuery M)
    (states : FinDist (PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K)))
    (agrees : ∀ state ∈ states.support,
      PBSRecursiveGroupAgrees M fallback payoff bound initial config query state) :
    states.expect (fun state => pbsRecursiveRecomputedLoss M fallback payoff bound initial
      unknown who config remaining state (payoff who)) =
    recursivePolicyValueChange M query.old
      (pbsRecursiveDepth config.noise config.cuts E M fallback payoff bound query.belief
        config.tolerance) unknown who (config.fuel + remaining)
      (states.map (fun state => state.history)) (payoff who) := by
  unfold recursivePolicyValueChange
  rw [FinDist.expect_map]
  apply FinDist.expect_congr
  intro state supported
  obtain ⟨live, old, computed⟩ := agrees state supported
  cases stored : state.belief with
  | none => simp only [stored, Option.map_none] at computed
  | some belief =>
      have fresh :
          pbsRecursiveDepth config.noise config.cuts E M fallback payoff bound belief
            config.tolerance =
          pbsRecursiveDepth config.noise config.cuts E M fallback payoff bound query.belief
            config.tolerance := by
        simpa only [stored, Option.map_some, Option.some.injEq] using computed
      rw [pbsRecursiveRecomputedLoss_eq_policyValueChange (E := E) (K := K) M fallback
        payoff bound initial unknown who config remaining state belief stored live (payoff who)]
      simp only [recursivePolicyValueChange, FinDist.expect_pure, old, fresh]

/-- The grouped root/opponent charge applies Nash to an actual recursive
computation. It avoids averaging singleton-to-PBS discrepancies. -/
theorem pbsRecursiveGroup_loss_le
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
    config.tolerance + bound * nashReplacementTransport.{u} (E := E)
      (fullInformation.{0, u, u, u, u, u} M) query.old
      (pbsRecursiveDepth config.noise config.cuts E M fallback payoff bound query.belief
        config.tolerance) unknown who (config.fuel + remaining)
      (states.map (fun state => state.history)) query.belief.law := by
  rw [pbsRecursiveGroup_loss_eq M fallback payoff bound initial unknown who config remaining
    query states agrees]
  simpa only [horizon] using
    (pbsRecursiveDepth_replacement_le.{u} (E := E) M config.noise noiseBound config.cuts
      fallback payoff zeroSum bound nonneg bounded query.belief config.tolerance positive
      query.old unknown who (states.map (fun state => state.history)))

/-- Calibration is a conditional HISTORY-law identity, not a singleton claim.
Against the computed opponent only the solver tolerance remains. -/
theorem pbsRecursiveGroup_calibrated_loss_le
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (config : PBSRecursiveResolveConfig.{u}) (remaining : Nat) (query : PBSRecursiveGroupQuery M)
    (noiseBound : PBSRecursiveDepthNoiseBound config.noise) (positive : 0 < config.tolerance)
    (horizon : config.cuts.sum = config.fuel + remaining)
    (states : FinDist (PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K)))
    (agrees : ∀ state ∈ states.support,
      PBSRecursiveGroupAgrees M fallback payoff bound initial config query state)
    (calibrated : states.map (fun state => state.history) = query.belief.law) (who : Fin 2) :
    states.expect (fun state => pbsRecursiveRecomputedLoss M fallback payoff bound initial
      (pbsRecursiveDepth config.noise config.cuts E M fallback payoff bound query.belief
        config.tolerance) who config remaining state (payoff who)) ≤ config.tolerance := by
  rw [pbsRecursiveGroup_loss_eq M fallback payoff bound initial _ who config remaining
    query states agrees, calibrated]
  simpa only [horizon] using
    (pbsRecursiveDepth_model_replacement_le.{u} (E := E) M config.noise noiseBound config.cuts
      fallback payoff zeroSum bound nonneg bounded query.belief config.tolerance positive
      query.old who)

/-- Expected cell bounds use the actual label frequencies. A missing query
keeps its signed conditional cost; it does not mean a zero-cost cell. -/
def pbsRecursiveGroupedCharge
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
    | some query => config.tolerance + bound * nashReplacementTransport.{u} (E := E)
        (fullInformation.{0, u, u, u, u, u} M) query.old
        (pbsRecursiveDepth config.noise config.cuts E M fallback payoff bound query.belief
          config.tolerance) unknown who (config.fuel + remaining)
        (cell.map (fun state => state.history)) query.belief.law)

/-- Disintegrate the actual joint memory distribution, then apply the derived
cell bound. Neither independence nor equality with the stored MODEL is assumed. -/
theorem pbsRecursiveRecomputedLoss_expect_le_groupedCharge
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
    pbsRecursiveGroupedCharge M fallback payoff bound initial unknown who config remaining
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
          exact pbsRecursiveGroup_loss_le M fallback payoff zeroSum bound nonneg bounded
            initial unknown who config remaining query noiseBound positive horizon
            (states.condOnFibre tag label) (compatible label present query chosen)

/-- Canonical proof-side key: preserve the saved PBS and entire incumbent.
The native resolver is unchanged. Stopped and missing-PBS states share the
uncertified cell, whose exact cost is retained rather than silently dropped. -/
def pbsRecursiveNativeGroupKey
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (config : PBSRecursiveResolveConfig.{u})
    (state : PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K)) :
    Option (PBSRecursiveGroupQuery M) :=
  if cfrDCutLive config.fuel state.history = true then
    state.belief.map (fun belief =>
      ⟨publicTrace (fullInformation.{0, u, u, u, u, u} M).toInfoSignals state.history.trace,
        belief, carriedMemoryProfile (fullInformation.{0, u, u, u, u, u} M)
          initial state.iteration⟩)
  else none

private theorem grouped_fibre_tag {A B : Type*} (law : FinDist A) (tag : A → B)
    (label : B) (present : label ∈ (law.map tag).support)
    (state : A) (reached : state ∈ (law.condOnFibre tag label).support) :
    tag state = label := by
  classical
  have possible : ∃ a ∈ tag ⁻¹' {label}, a ∈ law.support := by
    rw [FinDist.support_map] at present
    obtain ⟨a, supported, equal⟩ := present
    exact ⟨a, equal, supported⟩
  rw [FinDist.condOnFibre, dif_pos possible] at reached
  exact (FinDist.support_condOn law _ possible reached).1

/-- The canonical native key discharges all computation compatibility
conditions. No solver identity, grouping law or Nash certificate is supplied. -/
theorem pbsRecursiveNativeGroupKey_compatible
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (config : PBSRecursiveResolveConfig.{u})
    (states : FinDist (PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K))) :
    PBSRecursiveGroupingCompatible M fallback payoff bound initial config states
      (pbsRecursiveNativeGroupKey M initial config) id := by
  intro label present query chosen state reached
  have tagged := grouped_fibre_tag states (pbsRecursiveNativeGroupKey M initial config)
    label present state reached
  have labelEq : label = some query := chosen
  rw [labelEq] at tagged
  unfold pbsRecursiveNativeGroupKey at tagged
  by_cases live : cfrDCutLive config.fuel state.history = true
  · rw [if_pos live] at tagged
    cases stored : state.belief with
    | none => simp only [stored, Option.map_none] at tagged
    | some belief =>
        simp only [stored, Option.map_some, Option.some.injEq] at tagged
        subst query
        refine ⟨live, rfl, ?_⟩
        rw [stored]
        rfl
  · simp only [if_neg live] at tagged

/-- Leaving every group uncertified recovers the exact recomputed expectation
for any correlated joint law, including stopped and missing-PBS states. -/
theorem pbsRecursiveGroupedCharge_none
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (initial : K → Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) (who : Fin 2)
    (config : PBSRecursiveResolveConfig.{u}) (remaining : Nat)
    (states : FinDist (PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K)))
    (tag : PrivateIterationState (fullInformation.{0, u, u, u, u, u} M)
      (CarriedResolveMemory (fullInformation.{0, u, u, u, u, u} M) K) → Label) :
    pbsRecursiveGroupedCharge M fallback payoff bound initial unknown who config remaining
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
