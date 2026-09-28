/-
# Controls for stopped mass in a public posterior

The finite control attains the two-bound discarded-mass estimate exactly.
The original noisy hidden-type parent exercises the actual stored-state API.
-/

import GameTheory.Analysis.ReBeL.CFRDStoredChildDefect
import GameTheory.Analysis.ReBeL.Examples.PBSStoredChildReplay

noncomputable section

namespace GameTheory.ReBeL.Examples.StoredChildDefect

open GameTheory.Math.Probability

/-- A quarter live, three quarters stopped, all at the same public query. -/
def mixed : FinDist Bool :=
  FinDist.mix (1 / 4) (by norm_num) (by norm_num) (FinDist.pure true) (FinDist.pure false)

/-- The live branch has positive model mass. -/
theorem livePossible : ∃ x ∈ ({true} : Set Bool), x ∈ mixed.support := by
  refine ⟨true, rfl, ?_⟩
  exact FinDist.mem_support_mix_left _ _ _ (by norm_num) (FinDist.mem_support_pure.mpr rfl)

/-- Filtering changes the law even though the public query is the same. -/
theorem liveLaw : mixed.condOn {true} livePossible = FinDist.pure true := by
  apply FinDist.eq_pure_of_support_subset_singleton
  intro x reached
  exact (FinDist.support_condOn mixed {true} livePossible reached).1

/-- Opposite extreme values attain the estimate: 3 = 2 * 2 * (3/4). -/
theorem discarded_bound_tight :
    |mixed.expect (fun x => if x then (-2 : ℝ) else 2) -
      (mixed.condOn {true} livePossible).expect (fun x => if x then (-2 : ℝ) else 2)| =
      2 * 2 * mixed.probOf ({true} : Set Bool)ᶜ := by
  classical
  rw [liveLaw, ← FinDist.expect_indicator_eq_probOf]
  norm_num [mixed, FinDist.expect_mix, FinDist.expect_pure]

/-- A constant payoff has no bias even though the posterior laws differ. -/
theorem constant_value :
    mixed.expect (fun _ => (7 : ℝ)) =
      (mixed.condOn {true} livePossible).expect (fun _ => (7 : ℝ)) := by
  rw [FinDist.expect_const, FinDist.expect_const]

end GameTheory.ReBeL.Examples.StoredChildDefect

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Canonical enumeration includes all original game histories. -/
local instance defectHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Use the same finite legal menus as the existing noisy parent. -/
local instance defectChoice (who : Player) (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Equality for the real-valued reference solver is classical. -/
local instance defectInfo (who : Player) : DecidableEq ((model fullPrior).InfoState who) :=
  Classical.decEq _

/-- The actual noisy recursive parent satisfies the unconditional public
posterior theorem. Its visibility theorem is not used as a premise here. -/
theorem hiddenStoredPublic (loss : ℝ) (round : Nat)
    (history : (protocol fullPrior).History)
    (possible : CFRDFactualChildPossible (reducedModel fullPrior)
      (cfrDComposedTrunk (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 1 loss
        (pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
          (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2) storedChildNoise round)
      2 1 (publicTrace (model fullPrior).toInfoSignals history.trace)) :
    let solve : PBSChildSolve (reducedModel fullPrior) :=
      pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
        (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
    let trunk : Profile (model fullPrior).behavioralSignature :=
      cfrDComposedTrunk (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
        2 1 loss solve storedChildNoise round
    (cfrDComposedNextState (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 1 loss
      solve storedChildNoise round storedChildInitial history).belief =
    some (PublicBelief.condition (S := (model fullPrior).toInfoSignals)
      ((model fullPrior).runBehavioral trunk 2)
      (publicTrace (model fullPrior).toInfoSignals history.trace)
      (cfrDFactualChildPossible_public (reducedModel fullPrior) trunk 2 1 _ possible)) := by
  intro solve trunk
  exact cfrDComposedRound_storedPublic (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
    2 1 loss solve storedChildNoise round storedChildInitial recursiveInitialBelief rfl rfl
    history (cfrDFactualChildPossible_public (reducedModel fullPrior) trunk 2 1 _ possible)

/-- The complete future kernel may be evaluated under the actual noisy
parent's two posteriors. Its discarded-mass error vanishes in this game's
public phase model; no equality with an unknown opponent's posterior is used. -/
theorem hiddenStoredPublic_future_error {Outcome : Type*}
    (loss : ℝ) (round : Nat) (history : (protocol fullPrior).History)
    (possible : CFRDFactualChildPossible (reducedModel fullPrior)
      (cfrDComposedTrunk (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 1 loss
        (pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
          (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2) storedChildNoise round)
      2 1 (publicTrace (model fullPrior).toInfoSignals history.trace))
    (continuation : (protocol fullPrior).History → FinDist Outcome)
    (value : Outcome → ℝ) (bound : ℝ) (bounded : ∀ outcome, |value outcome| ≤ bound) :
    let solve : PBSChildSolve (reducedModel fullPrior) :=
      pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
        (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
    let trunk : Profile (model fullPrior).behavioralSignature :=
      cfrDComposedTrunk (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
        2 1 loss solve storedChildNoise round
    let obs := publicTrace (model fullPrior).toInfoSignals history.trace
    let posterior := PublicBelief.condition (S := (model fullPrior).toInfoSignals)
      ((model fullPrior).runBehavioral trunk 2) obs
      (cfrDFactualChildPossible_public (reducedModel fullPrior) trunk 2 1 obs possible)
    let child := cfrDFactualChildBelief (reducedModel fullPrior) trunk 2 1 obs possible
    (cfrDComposedNextState (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 1 loss
      solve storedChildNoise round storedChildInitial history).belief = some posterior ∧
      |(posterior.law.bind continuation).expect value -
        (child.law.bind continuation).expect value| ≤ 0 := by
  intro solve trunk obs posterior child
  have result := cfrDComposedRound_storedPublic_continuation_error (reducedModel fullPrior)
    pbsRootControlFallback cfrPayoff 2 1 loss solve storedChildNoise round
    storedChildInitial recursiveInitialBelief rfl rfl history possible
    continuation value bound bounded
  dsimp only at result
  have stopped := cfrDFactualChild_stoppedMass_eq_zero (reducedModel fullPrior)
    (hiddenTypes_publicTermination fullPrior) trunk 2 1 obs possible
  refine ⟨result.1, ?_⟩
  have estimate := result.2
  rw [stopped, zero_div, mul_zero] at estimate
  exact estimate

end GameTheory.ReBeL.Examples.HiddenTypes
