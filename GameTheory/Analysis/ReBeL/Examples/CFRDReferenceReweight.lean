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


/-- Equal queried conditionals give exactly zero cost even when public masses differ. -/
theorem reweighted_transport_zero (tag : Bool) :
    FinDist.conditionalTransportDefect oldReference newReference Prod.fst tag = 0 := by
  apply FinDist.conditionalTransportDefect_eq_zero
  · intro sampled
    rw [FinDist.support_map] at sampled ⊢
    obtain ⟨leaf, reached, same⟩ := sampled
    exact ⟨leaf, informationReweight_support newReference oldReference Prod.fst
      publicDensity oldReference_density reached, same⟩
  · intro sampled
    exact informationReweight_conditional newReference oldReference Prod.fst
      publicDensity oldReference_density tag sampled

private theorem pure_transport_fibre (bit : Bool) :
    (FinDist.pure bit).condOnFibre (fun _ => ()) () = FinDist.pure bit := by
  simpa only [FinDist.map_pure, FinDist.pure_bind] using
    (FinDist.eq_bind_condOnFibre (FinDist.pure bit) (fun _ => ())).symm

/-- The same observation may conceal a maximal, nonzero conditional transport cost. -/
theorem hidden_flip_transport_two :
    FinDist.conditionalTransportDefect (FinDist.pure false) (FinDist.pure true)
      (fun _ => ()) () = 2 := by
  simp only [FinDist.conditionalTransportDefect, FinDist.map_pure, FinDist.mem_support_pure,
    pure_transport_fibre]
  norm_num [show (Finset.univ : Finset Bool) = {false, true} from by decide,
    FinDist.prob_pure_eq_ite]

/-- An OLD-only query is charged directly, without evaluating a NEW fallback. -/
theorem disappearing_query_transport_one :
    FinDist.conditionalTransportDefect (FinDist.pure true) (FinDist.pure false) id true = 1 := by
  simp [FinDist.conditionalTransportDefect, FinDist.map_pure, FinDist.mem_support_pure]

/-- A query not sampled under OLD is excluded, not interpreted as a posterior. -/
theorem absent_old_query_transport_zero :
    FinDist.conditionalTransportDefect (FinDist.pure false) (FinDist.pure true) id true = 0 := by
  simp [FinDist.conditionalTransportDefect, FinDist.map_pure, FinDist.mem_support_pure]

/-- NEW quality alone fails to bound OLD value when hidden conditionals change. -/
theorem hidden_flip_invalid_zero_transport :
    conditionalOracleValue (FinDist.pure true) (fun _ => ())
        (fun bit => if bit then (-1 : ℝ) else 1) () ≤ 0 ∧
      ¬ conditionalOracleValue (FinDist.pure false) (fun _ => ())
        (fun bit => if bit then (-1 : ℝ) else 1) () ≤ 0 := by
  norm_num [conditionalOracleValue, pure_transport_fibre, FinDist.expect_pure]

/-- A bounded arbitrary observable transfers with the computed nonzero charge. -/
theorem hidden_flip_bounded_transfer (value : Bool → ℝ) (bound loss : ℝ)
    (nonneg : 0 ≤ loss) (bounded : ∀ bit, |value bit| ≤ bound)
    (quality : value true ≤ loss) : value false ≤ loss + bound * 2 := by
  have transfer := FinDist.condOnFibre_expect_le_add_transport
    (FinDist.pure false) (FinDist.pure true) (fun _ => ()) ()
    (by simp only [FinDist.map_pure, FinDist.mem_support_pure]) value bound loss
    nonneg bounded (by
      intro _
      simpa only [pure_transport_fibre, FinDist.expect_pure] using quality)
  simpa only [pure_transport_fibre, FinDist.expect_pure, hidden_flip_transport_two] using transfer

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


/-- The actual two-solve chain has zero reference transport, proved from its
computed reference preservation. Its continuation-value drift still remains. -/
theorem freshChainControl_transport_zero (who : Player) :
    cfrDReferenceTransportDefect (model fullPrior) freshControlModels
      (freshChainControlProfiles 2) informationControlFullFallback who 2 1 = 0 := by
  apply cfrDReferenceTransportDefect_eq_zero_of_informationReweight (model fullPrior)
    freshControlModels (freshChainControlProfiles 2) informationControlFullFallback who 2 1
    (fun _ _ => 1)
  intro k history
  cases k
  have same := freshChainControl_reference who
  rw [same, mul_one]
  rfl

/-- The general transport-aware envelope consumes derived local quality from
the actual child solver, and applies against an arbitrary unknown opponent. -/
theorem freshChainControl_transport_envelope
    (unknown : Profile (model fullPrior).behavioralSignature) :
    CFRDResolverEnvelope (model fullPrior) freshControlModels freshChainControlResolver
      informationControlFullFallback unknown 0 1 2 1 (cfrPayoff 1)
      (freshChainControlLoss 1 +
        cfrDFreshUniformDrift (model fullPrior) freshControlModels (freshChainControlProfiles 2)
          informationControlFullFallback 1 (cfrPayoff 1) 2 1 +
        2 * 2 * cfrDReferenceTransportDefect (model fullPrior) freshControlModels
          (freshChainControlProfiles 2) informationControlFullFallback 1 2 1) := by
  apply cfrDFreshCoherentResolver_envelope_with_transport (model fullPrior)
    (perfectRecall fullPrior)
    freshControlModels (freshChainControlProfiles 2) informationControlFullFallback
    unknown 0 1 (by decide) 2 1 (cfrPayoff 1) 2 (freshChainControlLoss 1)
    (by norm_num) (le_of_lt (freshChainControlLoss_pos 1))
    (fun h => cfrPayoff_abs_le_two 1 h)
  intro k
  cases k
  exact freshChainControl_leafOptimal 1

end GameTheory.ReBeL.Examples.HiddenTypes
