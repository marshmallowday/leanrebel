/-
# Opponent-uniform rates from actual source laws

Structural uniform-policy reach removes the unknown-opponent density from the
bound. Explicit outcome and reference-law radii are still hypotheses, not
consequences of accurate scalar Nash values or of independent re-solving.
-/

import GameTheory.Analysis.ReBeL.DominatingReachBound
import GameTheory.Analysis.ReBeL.CFRDSourceRates

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who info, Fintype (M.Choice who info)]
variable {K : Type*}

/-- Explicit opponent-uniform source rate. The continuation radius is a bound
on actual outcome laws, not on scalar equilibrium values. The reference radius
bounds unnormalized atoms, including NEW-only support. Neither radius is
asserted to decay merely because independently computed children are accurate. -/
theorem cfrDFreshSourceCost_le_uniform_rate
    (base next : Profile M.behavioralSignature) (fallback : Profile M.strategicSignature)
    (unknown : Profile M.behavioralSignature) (who opponent : Fin 2) (cut remaining : Nat)
    (bound loss outcomeRate referenceRate : ℝ) (hb : 0 ≤ bound) (hl : 0 ≤ loss)
    (hr : 0 ≤ outcomeRate)
    (outcomes : ∀ h, cfrDFreshOutcomeVariation M base next remaining h ≤ outcomeRate)
    (references : FinDist.atomVariation (unilateralReferenceLaw M base fallback opponent cut)
      (unilateralReferenceLaw M next fallback opponent cut) ≤ referenceRate) :
    cfrDFreshSourceCost M base next fallback unknown who opponent cut remaining bound loss ≤
      loss + bound * outcomeRate +
        4 * bound * unilateralDensityCap M fallback opponent * referenceRate := by
  classical
  have localBound :
      (M.runBehavioral (Profile.update unknown who (base who)) cut).expect
        (fun h => if cfrDCutLive remaining h then
          loss + bound * cfrDFreshOutcomeVariation M base next remaining h else 0) ≤
        loss + bound * outcomeRate := by
    apply FinDist.expect_le_of_forall
    intro h _
    split_ifs
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (outcomes h) hb)
    · exact add_nonneg hl (mul_nonneg hb hr)
  have atoms :
      (∑ h, (unilateralDensity M base fallback opponent (unknown opponent)
          (M.infoOf opponent h.trace) * (if cfrDCutLive remaining h then 1 else 0)) *
        |(unilateralReferenceLaw M base fallback opponent cut).prob h -
          (unilateralReferenceLaw M next fallback opponent cut).prob h|) ≤
      unilateralDensityCap M fallback opponent * referenceRate := by
    calc
      _ ≤ ∑ h, unilateralDensityCap M fallback opponent *
          |(unilateralReferenceLaw M base fallback opponent cut).prob h -
            (unilateralReferenceLaw M next fallback opponent cut).prob h| := by
        apply Finset.sum_le_sum
        intro h _
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        split_ifs
        · simpa only [mul_one] using
            unilateralDensity_le_cap M base fallback opponent (unknown opponent) h
        · simpa only [mul_zero] using unilateralDensityCap_nonneg M fallback opponent
      _ = unilateralDensityCap M fallback opponent *
          FinDist.atomVariation (unilateralReferenceLaw M base fallback opponent cut)
            (unilateralReferenceLaw M next fallback opponent cut) := by
        rw [FinDist.atomVariation, Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left references
        (unilateralDensityCap_nonneg M fallback opponent)
  unfold cfrDFreshSourceCost
  have scaled := mul_le_mul_of_nonneg_left atoms (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hb)
  simpa only [mul_assoc] using add_le_add localBound scaled

/-- The private parent seed is retained while integrating a source-law rate
that is uniform over every unknown opponent. The hypotheses are source-law
inequalities; none assumes the desired security or resolver envelope. -/
theorem cfrDSourceEnvelopeLoss_le_uniform_rate
    (seed : FinDist K) (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (cut remaining : Nat) (bound loss outcomeRate referenceRate : ℝ)
    (hb : 0 ≤ bound) (hl : 0 ≤ loss) (hr : 0 ≤ outcomeRate)
    (outcomes : ∀ n ∈ seed.support, ∀ h,
      cfrDFreshOutcomeVariation M (plays n) (next n) remaining h ≤ outcomeRate)
    (references : ∀ n ∈ seed.support,
      FinDist.atomVariation (unilateralReferenceLaw M (plays n) fallback opponent cut)
        (unilateralReferenceLaw M (next n) fallback opponent cut) ≤ referenceRate) :
    cfrDSourceEnvelopeLoss M seed plays next fallback unknown
        who opponent cut remaining bound loss ≤
      loss + bound * outcomeRate +
        4 * bound * unilateralDensityCap M fallback opponent * referenceRate := by
  unfold cfrDSourceEnvelopeLoss
  apply FinDist.expect_le_of_forall
  intro n reached
  exact cfrDFreshSourceCost_le_uniform_rate M (plays n) (next n) fallback unknown
    who opponent cut remaining bound loss outcomeRate referenceRate hb hl hr
    (outcomes n reached) (references n reached)

end GameTheory.ReBeL
