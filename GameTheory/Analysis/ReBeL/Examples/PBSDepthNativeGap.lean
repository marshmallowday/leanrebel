/-
# Noisy depth-native conditional gap controls

The four-history joint PBS has two strategic stages. The actual parent samples
two iterates with nonzero noise, or a computed number of iterates for a small
allocated tolerance. These are constructed solvers, not supplied Nash witnesses.
-/

import GameTheory.Analysis.ReBeL.PBSDepthNativeGap
import GameTheory.Analysis.ReBeL.Examples.PBSCarriedDepth

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

/-- Include the full legal history carrier, not just the model's current support. -/
local instance depthNativeGapHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Two genuinely sampled noisy parent iterates consume the actual depth budget.
The numerical error 1/8, child loss 1/4 and finite-time residual are all retained. -/
theorem depthNativeGap_two_iterates :
    let slice := fullAOHBeliefSlice (reducedModel fullPrior) depthControlBelief 0
    let own := fullAOHOwnLaw (reducedModel fullPrior) depthControlBelief 0
    own.expect (fun type => (cfrIterationLaw 2).expect (fun n =>
      |pbsInformationDepthCFRConditionalDrawGap (reducedModel fullPrior) slice own
        pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
        (depthControlNoise (slice.mixture own).law) 2 type n|)) ≤
      pbsRootDepthBudget (reducedModel fullPrior) (slice.mixture own).law
        pbsRootControlFallback 1 1 2 (1 / 8) (1 / 4) 2 := by
  intro slice own
  apply pbsInformationDepthCFR_native_mean_abs_le (reducedModel fullPrior) slice own
    pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior) 1 1 2 (1 / 8) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) cfrPayoff_abs_le_two
  intro n trunk player info
  norm_num [depthControlNoise]

/-- An actual nonzero predictor bias and positive child tolerance give a small
native mean-absolute gap after the computed number of parent rounds. No mass
floor, supplied equilibrium or source-rate certificate is used. -/
theorem depthNativeGap_allocated_quarter :
    let slice := fullAOHBeliefSlice (reducedModel fullPrior) depthControlBelief 0
    let own := fullAOHOwnLaw (reducedModel fullPrior) depthControlBelief 0
    let coefficient := pbsRootDepthErrorFactor (reducedModel fullPrior) (slice.mixture own).law
      pbsRootControlFallback 1 1
    let error := pbsDepthAllocationError coefficient (1 / 4)
    let noise : PBSRootDepthNoise (reducedModel fullPrior) (slice.mixture own).law :=
      fun _ _ _ _ => error / 2
    let t := pbsRootDepthBudgetRounds (reducedModel fullPrior) (slice.mixture own).law
      pbsRootControlFallback 1 1 2 error ((1 / 4) / 8) (1 / 4)
    own.expect (fun type => (cfrIterationLaw t).expect (fun n =>
      |pbsInformationDepthCFRConditionalDrawGap (reducedModel fullPrior) slice own
        pbsRootControlFallback cfrPayoff 1 1 2 ((1 / 4) / 8) noise t type n|)) ≤ 1 / 4 := by
  intro slice own coefficient error noise t
  have positive : 0 < error := pbsDepthAllocationError_pos coefficient (1 / 4) (by norm_num)
  apply pbsInformationDepthBudget_native_mean_abs_le (reducedModel fullPrior) slice own
    pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior) 1 1 2 error
    ((1 / 4) / 8) (1 / 4) (by norm_num) positive.le (by norm_num) cfrPayoff_abs_le_two noise
  · intro n trunk player info
    dsimp only [noise]
    rw [abs_of_nonneg (by positivity)]
    linarith
  · exact pbsDepthAllocation_feasible coefficient (1 / 4) (by norm_num)

/-- One actual transition under arbitrary fixed opposing policies produces a
possible certain event. The theorem consumes the joint conditioned native query,
not an independently resampled seed/type product. -/
theorem depthNativeGap_certain_query
    (opponents : Profile (model fullPrior).behavioralSignature) :
    let slice := fullAOHBeliefSlice (reducedModel fullPrior) depthControlBelief 0
    let own := fullAOHOwnLaw (reducedModel fullPrior) depthControlBelief 0
    let noise := depthControlNoise (slice.mixture own).law
    let execution := pbsInformationDepthCFRTaggedExecution (reducedModel fullPrior) slice own
      pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4) noise 2 opponents 1
    ∃ possible : ∃ point ∈ (Set.univ : Set _), point ∈ execution.support,
      ((execution.condOn Set.univ possible).map Prod.fst).expect (fun pair =>
        |pbsInformationDepthCFRConditionalDrawGap (reducedModel fullPrior) slice own
          pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4) noise 2 pair.2 pair.1|) ≤
        pbsRootDepthBudget (reducedModel fullPrior) (slice.mixture own).law
          pbsRootControlFallback 1 1 2 (1 / 8) (1 / 4) 2 := by
  classical
  intro slice own noise execution
  obtain ⟨point, reached⟩ := execution.support_nonempty
  let possible : ∃ point ∈ (Set.univ : Set _), point ∈ execution.support :=
    ⟨point, Set.mem_univ _, reached⟩
  refine ⟨possible, ?_⟩
  have unitMass : execution.probOf Set.univ = 1 := by
    rw [← FinDist.expect_indicator_eq_probOf]
    simp only [Set.mem_univ, if_true, FinDist.expect_const]
  have estimate := pbsInformationDepthCFR_conditioned_native_mean_abs_le
    (reducedModel fullPrior) slice own pbsRootControlFallback cfrPayoff
    (cumulative_zeroSum fullPrior) 1 1 2 (1 / 8) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) cfrPayoff_abs_le_two noise
    (by intro n trunk player info; norm_num [noise, depthControlNoise])
    2 opponents 1 Set.univ possible
  dsimp only [execution] at unitMass
  simpa only [unitMass, div_one] using estimate

/-- A zero-mass event cannot manufacture a conditional native query, including
on the actual noisy depth-parent execution rather than an arbitrary toy law. -/
theorem depthNativeGap_impossible_query
    (opponents : Profile (model fullPrior).behavioralSignature) :
    let slice := fullAOHBeliefSlice (reducedModel fullPrior) depthControlBelief 0
    let own := fullAOHOwnLaw (reducedModel fullPrior) depthControlBelief 0
    let execution := pbsInformationDepthCFRTaggedExecution (reducedModel fullPrior) slice own
      pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
      (depthControlNoise (slice.mixture own).law) 2 opponents 1
    ¬ ∃ point ∈ (∅ : Set _), point ∈ execution.support := by
  intro slice own execution
  rintro ⟨point, impossible, _⟩
  exact Set.notMem_empty point impossible

end GameTheory.ReBeL.Examples.HiddenTypes
