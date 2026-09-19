/-
# Genuine live-cut child sampling and a mismatched-table control

Two distinct deterministic child policies are sampled at the live second
round. The actual parent CFR-D recurrence and its numerical reference oracle
share that table. Replacing the fair child draw by a different constant table
changes the canonical outcome law and loses one unit at a legal cut history.
-/

import GameTheory.Analysis.ReBeL.CFRDChildOracle
import GameTheory.Analysis.ReBeL.Examples.CFRDResolveNegative

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Decidable information equality for the child-table execution control. -/
local instance childControlInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _
/-- Finite legal menus for the actual child-table parent recurrence. -/
local instance childControlChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- This live oracle has two genuinely different deterministic children. -/
def childControlFamily : CFRDChildOracle (model fullPrior) Bool :=
  cfrDExactChildFamily (model fullPrior) decisionClock cfrFallback cfrPayoff 2 1
    (fun _ _ => carriedBitLaw) (fun _ _ => carriedBitProfile)

/-- The reference oracle is plugged into the existing coupled parent driver. -/
def childControlOracle : CFRDValueOracle (model fullPrior) :=
  cfrDChildValueOracle (model fullPrior) decisionClock 2 cfrFallback childControlFamily

/-- Numerical accuracy is proved for every actual parent iteration. This is
not a claim of counterfactual optimality at zero-own-reach fallback states. -/
theorem childControl_accurate :
    CFRDDepthAccurate (model fullPrior) decisionClock cfrFallback cfrPayoff 2 1
      childControlOracle 0 :=
  cfrDExactChildFamily_accurate (model fullPrior) decisionClock cfrFallback cfrPayoff 2 1
    (fun _ _ => carriedBitLaw) (fun _ _ => carriedBitProfile)

/-- Every positive parent iteration count yields exact outcome equivalence
against every fixed unknown opponent at this genuinely live cut. -/
theorem childControl_resolve_law
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (t : Nat) [NeZero t] :
    privateCarriedResolve (model fullPrior) (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay (model fullPrior) decisionClock cfrFallback
          cfrPayoff 2 1 childControlOracle n.val)
        (cfrDChildDepthResolver (model fullPrior) decisionClock cfrFallback cfrPayoff
          2 1 childControlFamily t) unknown who 2 1 =
      privateIterationLaw (model fullPrior) (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay (model fullPrior) decisionClock cfrFallback
          cfrPayoff 2 1 childControlOracle n.val) unknown who 3 :=
  cfrDChildDepth_resolve_eq (model fullPrior) decisionClock (perfectRecall fullPrior)
    cfrFallback cfrPayoff 2 1 childControlFamily unknown who t

/-- The new private child and updated model posterior can be retained without
changing the actual original-game law of this concrete coupled solver. -/
theorem childControl_carried_law
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (t : Nat) [NeZero t] :
    (privateCarriedResolveStep (model fullPrior) (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay (model fullPrior) decisionClock cfrFallback
          cfrPayoff 2 1 childControlOracle n.val)
        (cfrDChildDepthResolver (model fullPrior) decisionClock cfrFallback cfrPayoff
          2 1 childControlFamily t) unknown who 2 1).map (fun state => state.history) =
      privateIterationLaw (model fullPrior) (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay (model fullPrior) decisionClock cfrFallback
          cfrPayoff 2 1 childControlOracle n.val) unknown who 3 := by
  rw [privateCarriedResolveStep_history, childControl_resolve_law]

/-- A fixed public-query table used to compute the mismatch control. -/
def childTableResolver : CarriedPublicResolver (model fullPrior) Unit :=
  cfrDChildPublicResolver (model fullPrior) decisionClock 2 (fun _ => carriedBitLaw)
    (fun _ => cfrDControlBaseline) (fun _ => carriedBitProfile)

/-- This legal live history is referee state, not a hidden policy input. -/
def childTableState : PrivateIterationState (model fullPrior) Unit :=
  privateIterationState (model fullPrior) (fun _ => cfrDControlBaseline) 2 ()
    (decode (.second false false false false))

/-- Clamping the past does not change either child's actual live action. -/
theorem childTable_bit_law (bit x y a b : Bool) (who : Player) :
    liveSecondLaw
      (cfrDChildProfiles (model fullPrior) decisionClock 2 cfrDControlBaseline
        carriedBitProfile bit) x y a b who = FinDist.pure bit := by
  have depth : decisionClock.depth who
      ((model fullPrior).infoOf who (decode (.second x y a b)).trace) = 2 := by
    rw [decisionClock.correct]
    rfl
  have same : cfrDChildProfiles (model fullPrior) decisionClock 2 cfrDControlBaseline
        carriedBitProfile bit who
        ((model fullPrior).infoOf who (decode (.second x y a b)).trace) =
      carriedBitProfile bit who
        ((model fullPrior).infoOf who (decode (.second x y a b)).trace) := by
    simp [cfrDChildProfiles, cfrDDepthProfile, cfrDDepthTrunk, depth]
  unfold liveSecondLaw
  rw [same]
  exact carriedBit_second_law bit x y a b who

/-- The two children have different actual continuation payoffs, zero and two. -/
theorem childTable_bit_value (bit : Bool) :
    ((model fullPrior).runBehavioralFrom
      (Profile.update (carriedBitProfile false) 0
        (cfrDChildProfiles (model fullPrior) decisionClock 2 cfrDControlBaseline
          carriedBitProfile bit 0)) 1
      (decode (.second false false false false))).expect (cfrPayoff 0) =
        if bit then 2 else 0 := by
  have own : liveSecondLaw
      (Profile.update (carriedBitProfile false) 0
        (cfrDChildProfiles (model fullPrior) decisionClock 2 cfrDControlBaseline
          carriedBitProfile bit 0)) false false false false 0 = FinDist.pure bit := by
    unfold liveSecondLaw
    rw [Profile.update_same]
    exact childTable_bit_law bit false false false false 0
  have opponent : liveSecondLaw
      (Profile.update (carriedBitProfile false) 0
        (cfrDChildProfiles (model fullPrior) decisionClock 2 cfrDControlBaseline
          carriedBitProfile bit 0)) false false false false 1 = FinDist.pure false := by
    unfold liveSecondLaw
    rw [Profile.update_of_ne _ _ (by decide : (1 : Player) ≠ 0)]
    exact carriedBit_second_law false false false false false 1
  rw [liveSecond_value, own, opponent]
  cases bit <;> norm_num [FinDist.expect_pure, signed, winValue]

/-- The fair child table gives value one under the actual resolver execution. -/
theorem childTable_resolver_value :
    (carriedResolvedTail (model fullPrior) childTableResolver
      (carriedBitProfile false) 0 1 childTableState).expect (cfrPayoff 0) = 1 := by
  rw [childTableResolver, cfrDChildResolvedTail_eq, FinDist.expect_bind]
  dsimp only [childTableState, privateIterationState]
  simp_rw [childTable_bit_value]
  norm_num [carriedBitLaw, FinDist.expect_mix, FinDist.expect_pure]

/-- A different legal child table gives zero at the identical carried state. -/
theorem childTable_wrong_value :
    (carriedResolvedTail (model fullPrior) (wrongPublicResolver Unit)
      (carriedBitProfile false) 0 1 childTableState).expect (cfrPayoff 0) = 0 := by
  have live : cfrDCutLive 1 childTableState.history = true := by
    simp only [cfrDCutLive, decide_eq_true_eq]
    exact ⟨by decide, fun impossible => impossible⟩
  unfold carriedResolvedTail
  rw [if_pos live]
  simpa only [wrongPublicResolver, FinDist.pure_bind, Profile.update_eq_self,
    childTableState, privateIterationState] using wrongResolver_after

/-- Numerical backup and execution cannot silently use different child tables. -/
theorem childTable_mismatch_changes_law :
    carriedResolvedTail (model fullPrior) (wrongPublicResolver Unit)
        (carriedBitProfile false) 0 1 childTableState ≠
      carriedResolvedTail (model fullPrior) childTableResolver
        (carriedBitProfile false) 0 1 childTableState := by
  intro same
  have values := congrArg (fun law => law.expect (cfrPayoff 0)) same
  rw [childTable_wrong_value, childTable_resolver_value] at values
  norm_num at values

end GameTheory.ReBeL.Examples.HiddenTypes
