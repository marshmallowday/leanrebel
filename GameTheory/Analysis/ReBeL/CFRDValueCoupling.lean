/-
# Value-sensitive source bounds for actual-prefix fresh re-solving

One joint continuation law at each history preserves the old and new outcome
marginals. Only its positive opponent-payoff change is charged. This is a
source-level sufficient condition, not a claim that Nash supplies a coupling
with small cost or that the native iteration sampler has been replaced.
-/

import GameTheory.Math.Probability.FinDistValueCoupling
import GameTheory.Analysis.ReBeL.CFRDSourceRates

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [∀ who info, Fintype (M.Choice who info)]
variable {K : Type*}

/-- A small directed coupling cost bounds the OLD-query positive value change.
This needs neither a payoff magnitude bound nor convergence of outcome laws. -/
theorem cfrDFreshValueChange_le_couplingRate
    (base next : Profile M.behavioralSignature) (fallback : Profile M.strategicSignature)
    (opponent : Fin 2) (payoff : E.History → ℝ) (cut remaining : Nat)
    (joint : E.History → FinDist (E.History × E.History)) (rate : ℝ) (hr : 0 ≤ rate)
    (oldMarginal : ∀ h, (joint h).map Prod.fst = M.runBehavioralFrom base remaining h)
    (newMarginal : ∀ h, (joint h).map Prod.snd = M.runBehavioralFrom next remaining h)
    (small : ∀ h, FinDist.directedValueCost (joint h) payoff payoff ≤ rate)
    (info : M.InfoState opponent) :
    max 0 (cfrDFreshValueChange M base next fallback opponent payoff cut remaining info) ≤
      rate := by
  apply max_le hr
  unfold cfrDFreshValueChange conditionalOracleValue
  apply FinDist.expect_le_of_forall
  intro h _
  exact (FinDist.expect_sub_le_directedValueCost
    (M.runBehavioralFrom base remaining h) (M.runBehavioralFrom next remaining h)
    (joint h) payoff payoff (oldMarginal h) (newMarginal h)).trans (small h)

variable [Fintype E.History]

/-- The supported query charge uses a directed payoff rate, not B times an
outcome L1 rate. Reference transport still includes NEW-only atoms. -/
theorem cfrDFreshTransportCharge_le_valueCoupling
    (plays next : K → Profile M.behavioralSignature) (fallback : Profile M.strategicSignature)
    (opponent : Fin 2) (payoff : E.History → ℝ) (cut remaining : Nat)
    (bound loss valueRate referenceRate : ℝ)
    (hb : 0 ≤ bound) (hl : 0 ≤ loss) (hv : 0 ≤ valueRate) (hr : 0 ≤ referenceRate)
    (n : K) (tag : M.InfoState opponent × Bool)
    (sampled : tag ∈ ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).support)
    (joint : E.History → FinDist (E.History × E.History))
    (oldMarginal : ∀ h, (joint h).map Prod.fst =
      M.runBehavioralFrom (plays n) remaining h)
    (newMarginal : ∀ h, (joint h).map Prod.snd =
      M.runBehavioralFrom (next n) remaining h)
    (small : ∀ h, FinDist.directedValueCost (joint h) payoff payoff ≤ valueRate)
    (fiberSmall : FinDist.fiberAtomVariation
      (unilateralReferenceLaw M (plays n) fallback opponent cut)
      (unilateralReferenceLaw M (next n) fallback opponent cut)
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h)) tag ≤
        referenceRate * ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
          (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).prob tag) :
    cfrDFreshTransportCharge M plays next fallback opponent payoff
        cut remaining bound loss n tag ≤ loss + valueRate + 4 * bound * referenceRate := by
  rcases tag with ⟨info, flag⟩
  cases flag
  · exact add_nonneg (add_nonneg hl hv)
      (mul_nonneg (mul_nonneg (by norm_num) hb) hr)
  · have drift := cfrDFreshValueChange_le_couplingRate M (plays n) (next n) fallback
      opponent payoff cut remaining joint valueRate hv oldMarginal newMarginal small info
    have transport := FinDist.conditionalTransportDefect_le_of_fiberRate
      (unilateralReferenceLaw M (plays n) fallback opponent cut)
      (unilateralReferenceLaw M (next n) fallback opponent cut)
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h)) (info, true)
      sampled referenceRate fiberSmall
    have scaled := mul_le_mul_of_nonneg_left transport
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb)
    unfold cfrDFreshTransportCharge
    dsimp only
    rw [if_pos rfl]
    nlinarith only [drift, scaled]

/-- Integrate over the original private seed/history joint law. Perfect recall
supplies supported OLD queries for every actually reached opposing prefix. -/
theorem cfrDWeightedTransportLoss_le_valueCoupling (hrecall : M.PerfectRecall)
    (seed : FinDist K) (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (different : opponent ≠ who) (payoff : E.History → ℝ)
    (cut remaining : Nat) (bound loss valueRate referenceRate : ℝ)
    (hb : 0 ≤ bound) (hl : 0 ≤ loss) (hv : 0 ≤ valueRate) (hr : 0 ≤ referenceRate)
    (joint : K → E.History → FinDist (E.History × E.History))
    (oldMarginal : ∀ n h, (joint n h).map Prod.fst =
      M.runBehavioralFrom (plays n) remaining h)
    (newMarginal : ∀ n h, (joint n h).map Prod.snd =
      M.runBehavioralFrom (next n) remaining h)
    (small : ∀ n h, FinDist.directedValueCost (joint n h) payoff payoff ≤ valueRate)
    (fiberSmall : ∀ n tag, tag ∈
      ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).support →
      FinDist.fiberAtomVariation (unilateralReferenceLaw M (plays n) fallback opponent cut)
        (unilateralReferenceLaw M (next n) fallback opponent cut)
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h)) tag ≤
      referenceRate * ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).prob tag) :
    cfrDWeightedEnvelopeLoss M seed plays unknown who opponent cut remaining
        (cfrDFreshTransportCharge M plays next fallback opponent payoff cut remaining bound loss) ≤
      loss + valueRate + 4 * bound * referenceRate := by
  unfold cfrDWeightedEnvelopeLoss privateCarriedPrefix
  rw [FinDist.expect_bind]
  apply FinDist.expect_le_of_forall
  intro n _
  rw [FinDist.expect_map]
  apply FinDist.expect_le_of_forall
  intro h reached
  have sampled : (M.infoOf opponent h.trace, cfrDCutLive remaining h) ∈
      ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
        (fun history =>
          (M.infoOf opponent history.trace, cfrDCutLive remaining history))).support := by
    rw [privateOpponent_profile M (plays n) unknown who opponent different] at reached
    rw [FinDist.support_map]
    exact ⟨h, informationReweight_support
        (unilateralReferenceLaw M (plays n) fallback opponent cut)
        (M.runBehavioral (Profile.update (plays n) opponent (unknown opponent)) cut)
        (fun history => (M.infoOf opponent history.trace, cfrDCutLive remaining history))
        (fun tag => unilateralDensity M (plays n) fallback opponent (unknown opponent) tag.1)
        (unilateralReference_density M hrecall (plays n) fallback opponent (unknown opponent) cut)
        reached, rfl⟩
  exact cfrDFreshTransportCharge_le_valueCoupling M plays next fallback opponent payoff
    cut remaining bound loss valueRate referenceRate hb hl hv hr n
    (M.infoOf opponent h.trace, cfrDCutLive remaining h) sampled (joint n)
    (oldMarginal n) (newMarginal n) (small n) (fiberSmall n _ sampled)

end GameTheory.ReBeL
