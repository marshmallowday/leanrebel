/-
# An unsafe but information-local public continuation replacement

Legality and information locality alone do not imply a safe re-solve. In the
same canonical live-cut game, replacing fair focal play by a constant legal
bit loses one unit at an explicit legal history against a seed-blind opponent.
This is a continuation-history control, not a claim that this bad resolver is
itself the recursive CFR-D solver or an equilibrium solver.
-/

import GameTheory.Analysis.ReBeL.Examples.CFRDResolveControl

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Decidable information-state equality for the proof-only negative control. -/
local instance badResolveInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _
/-- Finite canonical menus for the negative control's actual solver trace. -/
local instance badResolveChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- A legal resolver that ignores its public query and returns a constant bit. -/
def wrongPublicResolver (K : Type*) : CarriedPublicResolver (model fullPrior) K :=
  fun _ _ _ => FinDist.pure (carriedBitProfile false)

/-- A constant legal policy really produces the corresponding canonical bit. -/
theorem carriedBit_second_law (bit x y a b : Bool) (who : Player) :
    liveSecondLaw (carriedBitProfile bit) x y a b who = FinDist.pure bit := by
  unfold liveSecondLaw
  rw [show carriedBitProfile bit who
      ((model fullPrior).infoOf who (decode (.second x y a b)).trace) =
      FinDist.pure (liveSecondEquiv x y a b who bit) from rfl,
    FinDist.map_pure, Equiv.symm_apply_apply]

/-- The selected solver continuation retains its fair focal law against the
actual constant opponent, so its value at this live history is one. -/
theorem wrongResolver_before (n : Nat) :
    ((model fullPrior).runBehavioralFrom
      (Profile.update (carriedBitProfile false) 0
        (cfrDDepthPlay (model fullPrior) decisionClock cfrFallback cfrPayoff
          2 1 liveControlOracle n 0)) 1
      (decode (.second false false false false))).expect (cfrPayoff 0) = 1 := by
  have own : liveSecondLaw
      (Profile.update (carriedBitProfile false) 0
        (cfrDDepthPlay (model fullPrior) decisionClock cfrFallback cfrPayoff
          2 1 liveControlOracle n 0)) false false false false 0 = carriedBitLaw := by
    unfold liveSecondLaw
    rw [Profile.update_same, liveControl_second_policy]
    exact liveFairSecondLaw false false false false 0
  have opponent : liveSecondLaw
      (Profile.update (carriedBitProfile false) 0
        (cfrDDepthPlay (model fullPrior) decisionClock cfrFallback cfrPayoff
          2 1 liveControlOracle n 0)) false false false false 1 = FinDist.pure false := by
    unfold liveSecondLaw
    rw [Profile.update_of_ne _ _ (by decide : (1 : Player) ≠ 0)]
    exact carriedBit_second_law false false false false false 1
  rw [liveSecond_value, own, opponent]
  norm_num [carriedBitLaw, FinDist.expect_mix, FinDist.expect_pure, signed, winValue]

/-- After the legal but unsuitable replacement the actual continuation value is zero. -/
theorem wrongResolver_after :
    ((model fullPrior).runBehavioralFrom (carriedBitProfile false) 1
      (decode (.second false false false false))).expect (cfrPayoff 0) = 0 := by
  rw [liveSecond_value, carriedBit_second_law, carriedBit_second_law]
  norm_num [FinDist.expect_pure, signed, winValue]

/-- The loss is computed by the SAME carried public-resolver execution used
in the security theorem, not by an independent numerical payoff table. -/
theorem wrongResolver_loss_one (n : Nat) :
    privateResolvedLoss (model fullPrior) (liveResolvePlays (fun _ : Unit => n))
      (wrongPublicResolver Unit) (carriedBitProfile false) 0 2 1 (cfrPayoff 0) ()
      (decode (.second false false false false)) = 1 := by
  have live : cfrDCutLive 1 (decode (.second false false false false)) = true := by
    simp only [cfrDCutLive, decide_eq_true_eq]
    exact ⟨by decide, fun impossible => impossible⟩
  have tail : carriedResolvedTail (model fullPrior) (wrongPublicResolver Unit)
      (carriedBitProfile false) 0 1
      (privateIterationState (model fullPrior) (liveResolvePlays (fun _ : Unit => n)) 2 ()
        (decode (.second false false false false))) =
      (model fullPrior).runBehavioralFrom (carriedBitProfile false) 1
        (decode (.second false false false false)) := by
    unfold carriedResolvedTail
    rw [if_pos (show cfrDCutLive 1
      (privateIterationState (model fullPrior) (liveResolvePlays (fun _ : Unit => n)) 2 ()
        (decode (.second false false false false))).history = true from live)]
    simp only [wrongPublicResolver, FinDist.pure_bind, Profile.update_eq_self,
      privateIterationState]
  unfold privateResolvedLoss
  rw [tail]
  dsimp only [liveResolvePlays]
  rw [wrongResolver_before, wrongResolver_after]
  norm_num

/-- In particular, zero replacement loss is not automatic from a legal
public-only resolver interface, even with exact original leaf evaluation. -/
theorem wrongResolver_not_lossless :
    ¬ privateResolvedLoss (model fullPrior) (liveResolvePlays (fun _ : Unit => 0))
      (wrongPublicResolver Unit) (carriedBitProfile false) 0 2 1 (cfrPayoff 0) ()
      (decode (.second false false false false)) ≤ 0 := by
  rw [wrongResolver_loss_one]
  norm_num

end GameTheory.ReBeL.Examples.HiddenTypes
