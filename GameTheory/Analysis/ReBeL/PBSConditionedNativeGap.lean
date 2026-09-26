/-
# Native CFR queries selected by actual continuation events

The initial private seed and root type are drawn independently. Canonical legal
execution preserves their tag, but selecting an event can correlate them.
The resulting density cap is DERIVED from execution and its event probability.
No independent resampling, disclosure of the seed, or positive mass floor is
assumed. The gap still compares against the SAME computed average opponent.
-/

import GameTheory.Math.Probability.FinDistSelection
import GameTheory.Analysis.ReBeL.PBSJointNativeGap

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk ut
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {observations : List M.PublicSignal} {who : Fin 2} {T : Type ut}

/-- Execute the retained native own iterate from the type's full compatible
joint history law. Opponents are fixed legal policies, not functions of the seed. -/
def pbsInformationCFRExecutionKernel
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) (opponents : Profile (fullInformation M).behavioralSignature)
    (steps : Nat) (pair : Fin t × T) : FinDist E.History :=
  PublicBelief.continuationLaw (fullInformation M)
    (Profile.update opponents who
      (pbsInformationCFRIterate M (slice.mixture own) fallback payoff fuel pair.1.val who))
    steps (slice.kernel pair.2)

/-- Retain the private iteration and root type through the actual continuation.
Tagging is proof-side bookkeeping, not additional information given to policies. -/
def pbsInformationCFRTaggedExecution
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t] (opponents : Profile (fullInformation M).behavioralSignature)
    (steps : Nat) : FinDist ((Fin t × T) × E.History) :=
  ((cfrIterationLaw t).product own).bind (fun pair =>
    (pbsInformationCFRExecutionKernel M slice own fallback payoff fuel t opponents steps pair).map
      (fun history => (pair, history)))

/-- Execution alone does not change the retained tags' law. -/
theorem pbsInformationCFRTaggedExecution_tags
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t] (opponents : Profile (fullInformation M).behavioralSignature)
    (steps : Nat) :
    (pbsInformationCFRTaggedExecution M slice own fallback payoff fuel t opponents steps).map
      Prod.fst = (cfrIterationLaw t).product own := by
  simp only [pbsInformationCFRTaggedExecution, FinDist.map_bind, FinDist.map_comp,
    Function.comp_def, FinDist.map_const, FinDist.bind_pure]

/-- Forgetting the retained tags gives canonical execution of the actual CFR
average against arbitrary fixed opponents, with the ENTIRE root joint law.
This is an execution equality, not an independent recursive safety theorem. -/
theorem pbsInformationCFRTaggedExecution_history
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t] (opponents : Profile (fullInformation M).behavioralSignature)
    (steps : Nat) :
    (pbsInformationCFRTaggedExecution M slice own fallback payoff fuel t opponents steps).map
      Prod.snd = PublicBelief.continuationLaw (fullInformation M)
        (Profile.update opponents who
          (pbsInformationCFR M (slice.mixture own) fallback payoff fuel t who))
        steps (slice.mixture own) := by
  have mapHistory (law : FinDist E.History) : law.map (fun history => history) = law :=
    FinDist.map_id law
  simpa only [pbsInformationCFRTaggedExecution, pbsInformationCFRExecutionKernel,
    PublicBelief.continuationLaw, TypeBeliefSlice.mixture, FinDist.map_bind,
    FinDist.map_comp, Function.comp_def, mapHistory, FinDist.product,
    FinDist.bind_bind, FinDist.bind_map] using
    pbsInformationCFR_sampling_law M (slice.mixture own) fallback payoff fuel t opponents who steps

/-- Select a possible event in the complete tagged execution, then query the
retained seed and type. A zero-mass event has no constructor witness. -/
def pbsInformationCFRConditionedQuery
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t] (opponents : Profile (fullInformation M).behavioralSignature)
    (steps : Nat) (event : Set ((Fin t × T) × E.History))
    (possible : ∃ point ∈ event, point ∈
      (pbsInformationCFRTaggedExecution M slice own fallback payoff fuel t
        opponents steps).support) :
    FinDist (Fin t × T) :=
  ((pbsInformationCFRTaggedExecution M slice own fallback payoff fuel t opponents steps).condOn
    event possible).map Prod.fst

/-- The posterior probability ratio meets the joint density contract with the
DERIVED cap 1 / event mass. No atomwise source-law certificate is supplied. -/
theorem pbsInformationCFRConditionedQuery_density
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t] (opponents : Profile (fullInformation M).behavioralSignature)
    (steps : Nat) (event : Set ((Fin t × T) × E.History))
    (possible : ∃ point ∈ event, point ∈
      (pbsInformationCFRTaggedExecution M slice own fallback payoff fuel t
        opponents steps).support) :
    let actual := pbsInformationCFRConditionedQuery M slice own fallback payoff fuel t
      opponents steps event possible
    let prior := (cfrIterationLaw t).product own
    (∀ pair, actual.prob pair = prior.prob pair * (actual.prob pair / prior.prob pair)) ∧
      (∀ pair ∈ prior.support, actual.prob pair / prior.prob pair ≤
        1 / (pbsInformationCFRTaggedExecution M slice own fallback payoff fuel t
          opponents steps).probOf event) := by
  exact FinDist.tagged_condOn_density ((cfrIterationLaw t).product own)
    (pbsInformationCFRExecutionKernel M slice own fallback payoff fuel t opponents steps)
    event possible

/-- Native finite-T mean error after selecting an ACTUAL execution event.
Execution may use arbitrary fixed opponents, but the measured native gap
continues to use the solver's fixed average opponent and original type kernels. -/
theorem pbsInformationCFR_conditioned_native_mean_abs_le
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : Fin 2 → ℝ) (nonneg : ∀ player, 0 ≤ bound player)
    (bounded : ∀ player h, |payoff player h| ≤ bound player)
    (fuel t : Nat) [NeZero t] (opponents : Profile (fullInformation M).behavioralSignature)
    (steps : Nat) (event : Set ((Fin t × T) × E.History))
    (possible : ∃ point ∈ event, point ∈
      (pbsInformationCFRTaggedExecution M slice own fallback payoff fuel t
        opponents steps).support) :
    (pbsInformationCFRConditionedQuery M slice own fallback payoff fuel t
      opponents steps event possible).expect (fun pair =>
        |pbsInformationCFRConditionalDrawGap M slice own fallback payoff fuel t pair.2 pair.1|) ≤
      pbsRootCFRBound M (slice.mixture own).law bound fuel t /
        (pbsInformationCFRTaggedExecution M slice own fallback payoff fuel t
          opponents steps).probOf event := by
  have selected := FinDist.tagged_condOn_expect_le_div ((cfrIterationLaw t).product own)
    (pbsInformationCFRExecutionKernel M slice own fallback payoff fuel t opponents steps)
    event possible
    (fun pair =>
      |pbsInformationCFRConditionalDrawGap M slice own fallback payoff fuel t pair.2 pair.1|)
    (fun _ => abs_nonneg _)
  rw [FinDist.expect_product, FinDist.expect_comm] at selected
  exact selected.trans (div_le_div_of_nonneg_right
    (pbsInformationCFR_native_mean_abs_le M slice own fallback payoff zeroSum
      bound nonneg bounded fuel t) (FinDist.probOf_pos possible).le)

/-- Multiplying by the event's actual mass cancels the selection penalty.
This does NOT assert that the event is uniformly likely or that its conditional
error is bounded by the unconditional error. Finite-T error is not discarded. -/
theorem pbsInformationCFR_conditioned_native_weighted_le
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : Fin 2 → ℝ) (nonneg : ∀ player, 0 ≤ bound player)
    (bounded : ∀ player h, |payoff player h| ≤ bound player)
    (fuel t : Nat) [NeZero t] (opponents : Profile (fullInformation M).behavioralSignature)
    (steps : Nat) (event : Set ((Fin t × T) × E.History))
    (possible : ∃ point ∈ event, point ∈
      (pbsInformationCFRTaggedExecution M slice own fallback payoff fuel t
        opponents steps).support) :
    (pbsInformationCFRTaggedExecution M slice own fallback payoff fuel t
      opponents steps).probOf event *
      (pbsInformationCFRConditionedQuery M slice own fallback payoff fuel t
        opponents steps event possible).expect (fun pair =>
          |pbsInformationCFRConditionalDrawGap M slice own fallback payoff fuel t pair.2 pair.1|) ≤
      pbsRootCFRBound M (slice.mixture own).law bound fuel t := by
  have selected := pbsInformationCFR_conditioned_native_mean_abs_le M slice own fallback payoff
    zeroSum bound nonneg bounded fuel t opponents steps event possible
  simpa only [mul_comm] using (le_div_iff₀ (FinDist.probOf_pos possible)).mp selected

/-- A computed positive iteration budget controls the selected native gap.
The only amplification is the actual event reciprocal; no minimum event mass,
input equilibrium or learner convergence certificate is assumed. -/
theorem pbsInformationBudget_conditioned_native_mean_abs_le
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ h player, |utility h player| ≤ bound)
    (error : ℝ) (positive : 0 < error)
    (opponents : Profile (fullInformation M).behavioralSignature) (steps : Nat) :
    let t := pbsInformationBudgetRounds M (slice.mixture own).law (fun _ => bound) fuel error
    ∀ (event : Set ((Fin t × T) × E.History))
      (possible : ∃ point ∈ event, point ∈
        (pbsInformationCFRTaggedExecution M slice own fallback (fun player h => utility h player)
          fuel t opponents steps).support),
      (pbsInformationCFRConditionedQuery M slice own fallback (fun player h => utility h player)
        fuel t opponents steps event possible).expect (fun pair =>
          |pbsInformationCFRConditionalDrawGap M slice own fallback
            (fun player h => utility h player) fuel t pair.2 pair.1|) ≤
        error / (pbsInformationCFRTaggedExecution M slice own fallback
          (fun player h => utility h player) fuel t opponents steps).probOf event := by
  intro t event possible
  exact (pbsInformationCFR_conditioned_native_mean_abs_le M slice own fallback
    (fun player h => utility h player) zeroSum (fun _ => bound) (fun _ => nonneg)
    (fun player h => bounded h player) fuel t opponents steps event possible).trans
      (div_le_div_of_nonneg_right
        (pbsInformationBudgetRounds_error M (slice.mixture own).law (fun _ => bound)
          fuel error positive) (FinDist.probOf_pos possible).le)

end GameTheory.ReBeL
