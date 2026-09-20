/-
# Reach compatibility of the actual unilateral reference queries

The reference law changes only the focal player to uniform legal play.
Its supported histories therefore have nonzero original opponent own reach.
Perfect recall also identifies factual observation support with nonzero focal
own reach inside each sampled conditional. No posterior is claimed at an
unsampled reference fiber, and no positivity of factual own reach is assumed.
-/

import GameTheory.Analysis.ReBeL.DominatingReach

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

/-- A sampled conditional is supported by the original law. Unsampled fibers
are excluded because their total fallback need not satisfy this property. -/
theorem cfrD_conditional_support_source {Leaf Tag : Type*}
    (law : FinDist Leaf) (observe : Leaf → Tag) (tag : Tag)
    (sampled : tag ∈ (law.map observe).support) (leaf : Leaf)
    (reached : leaf ∈ (law.condOnFibre observe tag).support) : leaf ∈ law.support := by
  classical
  have possible : ∃ item ∈ observe ⁻¹' {tag}, item ∈ law.support := by
    rw [FinDist.support_map] at sampled
    obtain ⟨item, positive, same⟩ := sampled
    exact ⟨item, same, positive⟩
  unfold FinDist.condOnFibre at reached
  rw [dif_pos possible] at reached
  exact (FinDist.support_condOn law _ possible reached).2

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι]

/-- Positive canonical outcome probability forces each own-reach factor to
be nonzero, including early terminal outcomes at a longer requested horizon. -/
theorem cfrD_run_support_ownReach (base : Profile M.behavioralSignature)
    (cut : Nat) (history : E.History)
    (reached : history ∈ (M.runBehavioral base cut).support) (who : ι) :
    M.playerReachProbability base who history.trace ≠ 0 := by
  classical
  intro zero
  have product : (∏ player, M.playerReachProbability base player history.trace) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ who) zero
  have positive := FinDist.prob_pos_iff.mpr reached
  rw [run_probability_factorization M, product, mul_zero] at positive
  exact (lt_irrefl 0) positive

variable [DecidableEq ι] [∀ who info, Fintype (M.Choice who info)]

/-- A supported unilateral reference history has nonzero ORIGINAL own reach
for every opponent. This is derived from execution, not a kernel certificate. -/
theorem cfrDReference_support_opponents (base : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι) (cut : Nat) (history : E.History)
    (reached : history ∈ (unilateralReferenceLaw M base fallback who cut).support)
    (other : ι) (different : other ≠ who) :
    M.playerReachProbability base other history.trace ≠ 0 := by
  have positive := cfrD_run_support_ownReach M
    (Profile.update base who (uniformLegalPolicy M who (fallback who))) cut history reached other
  rw [ownReach_eq_of_policy_eq M _ base other (Profile.update_of_ne _ _ different)] at positive
  exact positive

variable {Tag : Type*}

/-- Conditioning an actual sampled reference query retains the derived
opponent-positivity property. The observation may include a public trace,
private information, remaining fuel, or a live/terminal flag. -/
theorem cfrDReference_conditional_opponents (base : Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι) (cut : Nat)
    (observe : E.History → Tag) (tag : Tag)
    (sampled : tag ∈ ((unilateralReferenceLaw M base fallback who cut).map observe).support)
    (history : E.History)
    (reached : history ∈
      ((unilateralReferenceLaw M base fallback who cut).condOnFibre observe tag).support)
    (other : ι) (different : other ≠ who) :
    M.playerReachProbability base other history.trace ≠ 0 :=
  cfrDReference_support_opponents M base fallback who cut history
    (cfrD_conditional_support_source _ observe tag sampled history reached) other different

/-- Within a sampled reference fiber, factual support is exactly nonzero
focal own reach. The observation must determine the focal information state;
a public observation alone is not silently treated as sufficient information. -/
theorem cfrDReference_factual_support_iff (hrecall : M.PerfectRecall)
    (base : Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (who : ι) (cut : Nat) (observe : E.History → Tag) (readInfo : Tag → M.InfoState who)
    (information : ∀ history, M.infoOf who history.trace = readInfo (observe history))
    (tag : Tag)
    (sampled : tag ∈ ((unilateralReferenceLaw M base fallback who cut).map observe).support)
    (history : E.History)
    (reached : history ∈
      ((unilateralReferenceLaw M base fallback who cut).condOnFibre observe tag).support) :
    tag ∈ ((M.runBehavioral base cut).map observe).support ↔
      M.playerReachProbability base who history.trace ≠ 0 := by
  classical
  have original := cfrD_conditional_support_source
    (unilateralReferenceLaw M base fallback who cut) observe tag sampled history reached
  have same := conditionalOracle_support
    (unilateralReferenceLaw M base fallback who cut) observe tag sampled history reached
  constructor
  · intro factual
    rw [FinDist.support_map] at factual
    obtain ⟨witness, positive, witnessTag⟩ := factual
    have nonzero := cfrD_run_support_ownReach M base cut witness positive who
    have equal : M.playerReachProbability base who witness.trace =
        M.playerReachProbability base who history.trace := by
      rw [← informationOwnReach_eq_player M hrecall base who witness,
        ← informationOwnReach_eq_player M hrecall base who history,
        information witness, information history, witnessTag, same]
    exact fun zero => nonzero (equal.trans zero)
  · intro nonzero
    have factual : history ∈ (M.runBehavioral base cut).support := by
      by_contra absent
      have zero := FinDist.prob_eq_zero_iff.mpr absent
      have density := unilateralReference_density M hrecall base fallback who (base who)
        cut history
      simp only [Profile.update_eq_self, unilateralDensity,
        informationOwnReach_eq_player M hrecall] at density
      have referenceNe := ne_of_gt (FinDist.prob_pos_iff.mpr original)
      have uniformNe := ne_of_gt (uniformOwnReach_positive M fallback who history.trace)
      exact (mul_ne_zero referenceNe (div_ne_zero nonzero uniformNe)) (density.symm.trans zero)
    rw [FinDist.support_map]
    exact ⟨history, factual, same⟩

/-- A factual zero-mass type in a sampled reference query has ZERO original
focal own reach on its whole conditional kernel, not merely zero joint reach. -/
theorem cfrDReference_factual_absent_own_zero (hrecall : M.PerfectRecall)
    (base : Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (who : ι) (cut : Nat) (observe : E.History → Tag) (readInfo : Tag → M.InfoState who)
    (information : ∀ history, M.infoOf who history.trace = readInfo (observe history))
    (tag : Tag)
    (sampled : tag ∈ ((unilateralReferenceLaw M base fallback who cut).map observe).support)
    (absent : tag ∉ ((M.runBehavioral base cut).map observe).support)
    (history : E.History)
    (reached : history ∈
      ((unilateralReferenceLaw M base fallback who cut).condOnFibre observe tag).support) :
    M.playerReachProbability base who history.trace = 0 := by
  by_contra nonzero
  exact absent ((cfrDReference_factual_support_iff M hrecall base fallback who cut
    observe readInfo information tag sampled history reached).mpr nonzero)

end GameTheory.ReBeL
