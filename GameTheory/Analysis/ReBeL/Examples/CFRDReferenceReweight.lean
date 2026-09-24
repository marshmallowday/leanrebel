/-
# Unequal-law, supported-fiber and actual-chain controls

Two genuinely correlated four-point laws have different public marginals but
the same hidden conditional on each public tag. Opposite one-point supports
show why the direction of domination cannot be omitted. The final control
instantiates the bridge on the existing two-stage hidden-type solver chain.
These finite-law guards are not counterexamples to source Theorem 3.
-/

import GameTheory.Analysis.ReBeL.CFRDReferenceReweight
import GameTheory.Analysis.ReBeL.Examples.CFRDFreshChain

noncomputable section

namespace GameTheory.ReBeL.Examples.ReferenceReweight

open GameTheory.Math.Probability

/-- Hidden mass depends on the public tag, so the joint law is not a product. -/
def hiddenAtFalse : FinDist Bool :=
  FinDist.mix (2 / 3) (by norm_num) (by norm_num) (FinDist.pure false) (FinDist.pure true)

/-- The other tag has a different hidden conditional. -/
def hiddenAtTrue : FinDist Bool :=
  FinDist.mix (1 / 5) (by norm_num) (by norm_num) (FinDist.pure false) (FinDist.pure true)

/-- The newer law has equal public masses but nontrivial hidden correlations. -/
def newReference : FinDist (Bool × Bool) :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.product (FinDist.pure false) hiddenAtFalse)
    (FinDist.product (FinDist.pure true) hiddenAtTrue)

/-- The old public masses are one quarter and three quarters. -/
def oldReference : FinDist (Bool × Bool) :=
  FinDist.mix (1 / 4) (by norm_num) (by norm_num)
    (FinDist.product (FinDist.pure false) hiddenAtFalse)
    (FinDist.product (FinDist.pure true) hiddenAtTrue)

/-- The normalized OLD-from-NEW density depends only on the observed tag. -/
def publicDensity (tag : Bool) : ℝ := if tag then 3 / 2 else 1 / 2

/-- Exact atomwise density, checked at all four hidden histories. -/
theorem oldReference_density (leaf : Bool × Bool) :
    oldReference.prob leaf = newReference.prob leaf * publicDensity leaf.1 := by
  rcases leaf with ⟨tag, hidden⟩
  cases tag <;> cases hidden <;>
    norm_num [oldReference, newReference, hiddenAtFalse, hiddenAtTrue,
      publicDensity, FinDist.prob_mix, FinDist.prob_product, FinDist.prob_pure_eq_ite]

/-- Both tags are actually supported; no fallback is used as a posterior. -/
theorem oldReference_tag_supported (tag : Bool) :
    tag ∈ (oldReference.map Prod.fst).support := by
  rw [FinDist.support_map]
  refine ⟨(tag, false), ?_, rfl⟩
  apply FinDist.prob_pos_iff.mp
  cases tag <;> norm_num [oldReference, hiddenAtFalse, hiddenAtTrue,
    FinDist.prob_mix, FinDist.prob_product, FinDist.prob_pure_eq_ite]

/-- The complete reference laws really differ, unlike the fixed-cut predecessor. -/
theorem oldReference_ne_newReference : oldReference ≠ newReference := by
  intro same
  have atom := congrArg (fun law : FinDist (Bool × Bool) => law.prob (false, false)) same
  norm_num [oldReference, newReference, hiddenAtFalse, hiddenAtTrue,
    FinDist.prob_mix, FinDist.prob_product, FinDist.prob_pure_eq_ite] at atom

/-- Every observable, not merely the hidden-bit mean, has the same conditional value. -/
theorem reweighted_value (value : Bool × Bool → ℝ) (tag : Bool) :
    conditionalOracleValue oldReference Prod.fst value tag =
      conditionalOracleValue newReference Prod.fst value tag :=
  conditionalOracle_reweight_value newReference oldReference Prod.fst publicDensity
    oldReference_density tag (oldReference_tag_supported tag) value

/-- Signed changes telescope despite genuinely different full reference laws. -/
theorem reweighted_signed_change (first middle last : Bool × Bool → ℝ) (tag : Bool) :
    conditionalOracleValue oldReference Prod.fst (fun leaf => last leaf - first leaf) tag =
      conditionalOracleValue oldReference Prod.fst (fun leaf => middle leaf - first leaf) tag +
        conditionalOracleValue newReference Prod.fst (fun leaf => last leaf - middle leaf) tag := by
  rw [← reweighted_value]
  unfold conditionalOracleValue
  rw [← FinDist.expect_add]
  apply FinDist.expect_congr
  intro leaf _
  ring

/-- An old-supported tag missing from the new law cannot satisfy the density.
The contradiction is witnessed before evaluating a zero-mass conditional. -/
theorem disappearing_tag_has_no_density :
    ¬ ∃ weight : Bool → ℝ, ∀ leaf : Bool × Bool,
      (FinDist.pure (true, false)).prob leaf =
        (FinDist.pure (false, false)).prob leaf * weight leaf.1 := by
  rintro ⟨weight, density⟩
  have absent := density (true, false)
  norm_num [FinDist.prob_pure_eq_ite] at absent

/-- Equal observed laws are not enough when the hidden conditionals differ. -/
theorem hidden_change_has_no_information_density :
    (FinDist.pure (false, false)).map Prod.fst =
        (FinDist.pure (false, true)).map Prod.fst ∧
      ¬ ∃ weight : Bool → ℝ, ∀ leaf : Bool × Bool,
        (FinDist.pure (false, false)).prob leaf =
          (FinDist.pure (false, true)).prob leaf * weight leaf.1 := by
  constructor
  · simp only [FinDist.map_pure]
  · rintro ⟨weight, density⟩
    have absent := density (false, false)
    norm_num [FinDist.prob_pure_eq_ite] at absent

end GameTheory.ReBeL.Examples.ReferenceReweight

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- All legal histories, including counterfactual ones, occur in the maximum. -/
local instance reweightControlHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Inactive menus remain part of the existing full-information strategy carrier. -/
local instance reweightControlChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- The new transport bridge retains the actual twice-recomputed hidden-type
chain. Here reference preservation DERIVES density one, rather than receiving it. -/
theorem freshChainControl_reweighted_drift (who : Player) :
    cfrDFreshValueDrift (model fullPrior) (freshControlModels ()) (freshChainControlProfiles 2 ())
        informationControlFullFallback who (cfrPayoff who) 2 1 ≤
      cfrDFreshValueDrift (model fullPrior) (freshControlModels ()) (freshChainControlProfiles 1 ())
        informationControlFullFallback who (cfrPayoff who) 2 1 +
      cfrDFreshValueDrift (model fullPrior) (freshChainControlProfiles 1 ())
        (freshChainControlProfiles 2 ()) informationControlFullFallback who
        (cfrPayoff who) 2 1 := by
  apply cfrDFreshValueDrift_le_add_of_informationReweight (model fullPrior)
    (freshControlModels ()) (freshChainControlProfiles 1 ()) (freshChainControlProfiles 2 ())
    informationControlFullFallback who (cfrPayoff who) 2 1 (fun _ => 1)
  intro history
  have same : unilateralReferenceLaw (model fullPrior) (freshChainControlProfiles 1 ())
      informationControlFullFallback who 2 =
      unilateralReferenceLaw (model fullPrior) (freshControlModels ())
        informationControlFullFallback who 2 :=
    cfrDFreshInformationChain_referenceLaw (reducedModel fullPrior) pbsRootControlFallback
      cfrPayoff 2 1 2 freshChainControlLoss (freshControlModels ()) who 1
  rw [same, mul_one]

end GameTheory.ReBeL.Examples.HiddenTypes
