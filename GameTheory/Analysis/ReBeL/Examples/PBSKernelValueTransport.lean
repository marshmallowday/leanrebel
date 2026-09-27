/-
# Changed joint kernels: sharp value drift and a real noisy parent

The two legal roots share the queried player's information and the public
trace, but differ in the opponent's hidden bit. Their conditional values can
differ by the full kernel allowance with unchanged opposing policies. A second
control uses the actual two-iterate noisy depth parent and completed full-AOH
slices, retaining off-path types after changing the modeled joint belief.
-/

import GameTheory.Analysis.ReBeL.PBSDepthKernelGap
import GameTheory.Analysis.ReBeL.Examples.PBSDepthNativeGap

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

/-- The existing exhaustive physical-history domain is unchanged. -/
local instance kernelValueHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- A legal joint root law with a fixed own bit and one hidden opposing bit. -/
def kernelValueBelief (bit : Bool) : PublicBelief (model fullPrior).toInfoSignals
    (publicTrace (model fullPrior).toInfoSignals (fullDraw (false, false)).trace) where
  law := FinDist.pure (fullDraw (false, bit))
  supported history member := by
    have equal := FinDist.mem_support_pure.mp member
    subst history
    cases bit <;> rfl

/-- A coarse remembered type is local and persistent; no hidden bit is exposed. -/
def kernelValueSlice (bit : Bool) : TypeBeliefSlice (model fullPrior)
    (publicTrace (model fullPrior).toInfoSignals (fullDraw (false, false)).trace) 0 Unit where
  memory := { typeAt := fun _ => (), persistent := by intros; rfl }
  kernel := fun _ => kernelValueBelief bit
  typed := by intro type _ _; cases type; rfl

/-- A bounded history observable of the root's hidden opposing bit.
This is a payoff, not an information-local policy reading hidden state. -/
def kernelValueObservable (history : (protocol fullPrior).History) : ℝ :=
  match history.state with
  | .first types => if types.2 then 1 else -1
  | _ => 0

/-- The payoff magnitude bound holds on every legal history, not just one root. -/
theorem kernelValueObservable_bound (history : (protocol fullPrior).History) :
    |kernelValueObservable history| ≤ 1 := by
  unfold kernelValueObservable
  cases history.state with
  | first types => cases types.2 <;> norm_num
  | _ => norm_num

/-- At zero continuation fuel the two compatible kernels really disagree,
for every fixed policy. This boundary does not assert zero-game payoff. -/
theorem kernelValue_payoff_zero (bit : Bool)
    (opponents : Profile (model fullPrior).behavioralSignature)
    (replacement : (model fullPrior).BehavioralPolicy 0) :
    (kernelValueSlice bit).conditionalPayoff opponents 0 kernelValueObservable replacement () =
      if bit then 1 else -1 := by
  simp [TypeBeliefSlice.conditionalPayoff, PublicBelief.continuationLaw,
    kernelValueSlice, kernelValueBelief, InformationModel.runBehavioralFrom,
    kernelValueObservable, fullDraw, drawHistory, History.extend]

/-- The actual attained conditional optimum has the same explicit value;
no equilibrium or numerical optimizer certificate is assumed. -/
theorem kernelValue_optimum_zero (bit : Bool)
    (fallback : Profile (model fullPrior).strategicSignature)
    (opponents : Profile (model fullPrior).behavioralSignature) :
    (kernelValueSlice bit).infoValue fallback 0 kernelValueObservable opponents () =
      if bit then 1 else -1 := by
  unfold TypeBeliefSlice.infoValue
  exact kernelValue_payoff_zero bit opponents _

/-- Value stability's coefficient is sharp on compatible protocol kernels.
The full discrepancy includes the new-only history absent from the old root. -/
theorem kernelValue_variation_two
    (opponents : Profile (model fullPrior).behavioralSignature)
    (replacement : (model fullPrior).BehavioralPolicy 0) :
    FinDist.atomVariation (kernelValueBelief false).law (kernelValueBelief true).law = 2 := by
  have lower := (kernelValueSlice false).conditionalPayoff_abs_sub_le_kernelVariation
    (kernelValueSlice true) opponents 0 kernelValueObservable replacement () () 1
    kernelValueObservable_bound
  have upper := FinDist.atomVariation_le_two
    (kernelValueBelief false).law (kernelValueBelief true).law
  norm_num [kernelValue_payoff_zero, kernelValueSlice] at lower
  exact le_antisymm upper lower

/-- Identical own-type weights, public observation and opposing policies do
not imply identical conditional values when the full kernels change. -/
theorem kernelValue_same_query_different_values
    (fallback : Profile (model fullPrior).strategicSignature)
    (opponents : Profile (model fullPrior).behavioralSignature) :
    (kernelValueSlice false).infoValue fallback 0 kernelValueObservable opponents () ≠
      (kernelValueSlice true).infoValue fallback 0 kernelValueObservable opponents () := by
  rw [kernelValue_optimum_zero, kernelValue_optimum_zero]
  norm_num

/-- A genuinely noisy parent from the four-root joint PBS is evaluated at
changed completed full-AOH kernels, using the actual selected joint query.
The fresh absent types retain physical off-path completions, not fake posteriors. -/
theorem depthKernel_changed_query
    (opponents : Profile (model fullPrior).behavioralSignature) :
    let M := reducedModel fullPrior
    let slice := fullAOHBeliefSlice M depthControlBelief 0
    let own := fullAOHOwnLaw M depthControlBelief 0
    let fresh := fullAOHBeliefSlice M (kernelValueBelief true) 0
    let noise := depthControlNoise (slice.mixture own).law
    let average := pbsInformationDepthCFR M (slice.mixture own) pbsRootControlFallback
      cfrPayoff 1 1 2 (1 / 4) noise 2
    let execution := pbsInformationDepthCFRTaggedExecution M slice own pbsRootControlFallback
      cfrPayoff 1 1 2 (1 / 4) noise 2 opponents 1
    ∃ possible : ∃ point ∈ (Set.univ : Set _), point ∈ execution.support,
      let query := (execution.condOn Set.univ possible).map Prod.fst
      query.expect (fun pair =>
        |fresh.infoValue (fun player => liftPolicy M player (pbsRootControlFallback player))
            2 (cfrPayoff 0) average pair.2 -
          fresh.conditionalPayoff average 2 (cfrPayoff 0)
            (pbsInformationDepthCFRIterate M (slice.mixture own) pbsRootControlFallback
              cfrPayoff 1 1 2 (1 / 4) noise pair.1.val 0) pair.2|) ≤
        pbsRootDepthBudget M (slice.mixture own).law pbsRootControlFallback
          1 1 2 (1 / 8) (1 / 4) 2 +
        4 * query.expect (fun pair =>
          FinDist.atomVariation (slice.kernel pair.2).law (fresh.kernel pair.2).law) := by
  intro M slice own fresh noise average execution
  obtain ⟨point, reached⟩ := execution.support_nonempty
  let possible : ∃ point ∈ (Set.univ : Set _), point ∈ execution.support :=
    ⟨point, Set.mem_univ _, reached⟩
  refine ⟨possible, ?_⟩
  have unitMass : execution.probOf Set.univ = 1 := by
    rw [← FinDist.expect_indicator_eq_probOf]
    simp only [Set.mem_univ, if_true, FinDist.expect_const]
  have estimate := pbsInformationDepthCFR_conditioned_kernelGap_le M slice own
    pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior) 1 1 2 (1 / 8) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) cfrPayoff_abs_le_two noise
    (by intro n trunk player info; norm_num [noise, depthControlNoise]) 2 opponents 1
    Set.univ possible (fun _ => fresh) Prod.snd
  dsimp only [execution] at unitMass
  simpa only [unitMass, div_one, Nat.reduceAdd, show (2 : ℝ) * 2 = 4 by norm_num] using estimate

end GameTheory.ReBeL.Examples.HiddenTypes
