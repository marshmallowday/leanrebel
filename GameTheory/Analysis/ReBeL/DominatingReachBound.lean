/-
# Structural finite-game cap for arbitrary unilateral densities

This cap depends on uniform legal own reach, never on current query mass.
It is a real-valued proof bound, not an executable computation or a sharp rate.
-/

import GameTheory.Analysis.ReBeL.DominatingReach

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [∀ who info, Fintype (M.Choice who info)]
variable [Fintype ι] [DecidableEq ι] [Fintype E.History]

/-- A finite game-dependent density cap. This uses uniform legal own reach,
not a minimum probability of the current model or of its public queries. -/
def unilateralDensityCap (fallback : (who : ι) → M.Policy who) (who : ι) : ℝ :=
  ∑ history : E.History,
    (informationOwnReach M (uniformLegalProfile M fallback) who
      (M.infoOf who history.trace))⁻¹

/-- The cap is nonnegative and independent of every current policy. -/
theorem unilateralDensityCap_nonneg (fallback : (who : ι) → M.Policy who) (who : ι) :
    0 ≤ unilateralDensityCap M fallback who := by
  apply Finset.sum_nonneg
  intro history _
  exact inv_nonneg.mpr (uniformInformationReach_positive M fallback who _ ⟨history, rfl⟩).le

/-- Every unilateral behavioral policy obeys one structural cap, including
histories with zero current-model probability. No recall premise is needed to
bound the ratio; recall is still required for the change-of-measure theorem. -/
theorem unilateralDensity_le_cap (base : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι) (policy : M.BehavioralPolicy who)
    (history : E.History) :
    unilateralDensity M base fallback who policy (M.infoOf who history.trace) ≤
      unilateralDensityCap M fallback who := by
  classical
  have numerator := (informationOwnReach_unitInterval M
    (Profile.update base who policy) who (M.infoOf who history.trace)).2
  have denominator := uniformInformationReach_positive M fallback who _ ⟨history, rfl⟩
  calc
    _ ≤ (informationOwnReach M (uniformLegalProfile M fallback) who
        (M.infoOf who history.trace))⁻¹ := by
      simpa only [unilateralDensity, div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_right numerator (inv_nonneg.mpr denominator.le)
    _ ≤ unilateralDensityCap M fallback who := by
      apply Finset.single_le_sum _ (Finset.mem_univ history)
      intro other _
      exact inv_nonneg.mpr
        (uniformInformationReach_positive M fallback who _ ⟨other, rfl⟩).le

end GameTheory.ReBeL
