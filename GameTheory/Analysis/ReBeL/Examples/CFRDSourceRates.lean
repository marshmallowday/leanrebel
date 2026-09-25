/-
# Source-rate controls and the actual noisy-parent security consumer

The finite counterexample retains one common observation of two joint laws.
It rules out dropping the unknown-opponent density, not source Theorem 3.
The game consumer keeps finite parent time, positive bias and two fresh solves.
-/

import GameTheory.Analysis.ReBeL.CFRDSourceRates
import GameTheory.Analysis.ReBeL.Examples.CFRDWeightedTransport

noncomputable section

namespace GameTheory.ReBeL.Examples.SourceRates

open GameTheory.Math.Probability

private theorem fourAtoms : (Finset.univ : Finset (Bool × Bool)) =
    {(false, false), (false, true), (true, false), (true, true)} := by decide

/-- One joint reference law makes the true query rare and its hidden bit false. -/
def oldJoint : FinDist (Bool × Bool) :=
  FinDist.mix (1 / 100) (by norm_num) (by norm_num)
    (FinDist.pure (true, false)) (FinDist.pure (false, false))

/-- Only the rare fiber changes, and its newly supported hidden atom is included. -/
def newJoint : FinDist (Bool × Bool) :=
  FinDist.mix (1 / 100) (by norm_num) (by norm_num)
    (FinDist.pure (true, true)) (FinDist.pure (false, false))

/-- OLD observation masses come from the joint source, not a separate sampler. -/
theorem oldJoint_mass (tag : Bool) :
    (oldJoint.map Prod.fst).prob tag = if tag then 1 / 100 else 99 / 100 := by
  rw [FinDist.map_eq_bind, FinDist.prob_bind]
  cases tag <;> norm_num [oldJoint, FinDist.expect_mix, FinDist.expect_pure,
    FinDist.prob_pure_eq_ite]

/-- NEW observations have the same marginal, despite their different conditional. -/
theorem newJoint_mass (tag : Bool) :
    (newJoint.map Prod.fst).prob tag = if tag then 1 / 100 else 99 / 100 := by
  rw [FinDist.map_eq_bind, FinDist.prob_bind]
  cases tag <;> norm_num [newJoint, FinDist.expect_mix, FinDist.expect_pure,
    FinDist.prob_pure_eq_ite]

/-- Both OLD queries are genuinely supported. -/
theorem oldJoint_reached (tag : Bool) : tag ∈ (oldJoint.map Prod.fst).support := by
  rw [← FinDist.prob_pos_iff, oldJoint_mass]
  cases tag <;> norm_num

/-- Both NEW queries are genuinely supported. -/
theorem newJoint_reached (tag : Bool) : tag ∈ (newJoint.map Prod.fst).support := by
  rw [← FinDist.prob_pos_iff, newJoint_mass]
  cases tag <;> norm_num

/-- Normalization is tested through the public real-probability interface. -/
theorem oldJoint_conditional (tag : Bool) :
    oldJoint.condOnFibre Prod.fst tag = FinDist.pure (tag, false) := by
  apply FinDist.ext_of_prob
  rintro ⟨query, hidden⟩
  have factor := FinDist.observation_prob_mul_conditional_prob
    oldJoint Prod.fst tag (query, hidden)
  rw [oldJoint_mass] at factor
  cases tag <;> cases query <;> cases hidden <;>
    norm_num [oldJoint, FinDist.prob_pure_eq_ite] at factor ⊢ <;> linarith

/-- The new hidden atom is seen by the actual NEW conditional. -/
theorem newJoint_conditional (tag : Bool) :
    newJoint.condOnFibre Prod.fst tag = FinDist.pure (tag, tag) := by
  apply FinDist.ext_of_prob
  rintro ⟨query, hidden⟩
  have factor := FinDist.observation_prob_mul_conditional_prob
    newJoint Prod.fst tag (query, hidden)
  rw [newJoint_mass] at factor
  cases tag <;> cases query <;> cases hidden <;>
    norm_num [newJoint, FinDist.prob_pure_eq_ite] at factor ⊢ <;> linarith

/-- The rare conditional changes maximally, while the common one is unchanged. -/
theorem joint_defect (tag : Bool) :
    FinDist.conditionalTransportDefect oldJoint newJoint Prod.fst tag =
      if tag then 2 else 0 := by
  classical
  rw [FinDist.conditionalTransportDefect, if_pos (oldJoint_reached tag),
    if_pos (newJoint_reached tag), oldJoint_conditional, newJoint_conditional]
  cases tag <;> norm_num [fourAtoms, FinDist.prob_pure_eq_ite]

/-- Before conditioning the entire reference law changes by only one fiftieth. -/
theorem joint_variation : FinDist.atomVariation oldJoint newJoint = 1 / 50 := by
  norm_num [FinDist.atomVariation, fourAtoms, oldJoint, newJoint,
    FinDist.prob_pure_eq_ite]

/-- OLD observation weighting cancels the rare conditional normalization. -/
theorem old_weighted_defect :
    (oldJoint.map Prod.fst).expect
      (FinDist.conditionalTransportDefect oldJoint newJoint Prod.fst) = 1 / 50 := by
  rw [FinDist.expect_map]
  simp_rw [joint_defect]
  norm_num [oldJoint, FinDist.expect_mix, FinDist.expect_pure]

/-- An opponent may concentrate entirely on the rare supported OLD query. -/
def concentrated : FinDist (Bool × Bool) := FinDist.pure (true, false)

/-- The exact information-local density, including its zero on the other query. -/
def concentrationDensity (tag : Bool) : ℝ := if tag then 100 else 0

/-- The concentrated law satisfies the source theorem's change-of-measure premise. -/
theorem concentrated_density (atom : Bool × Bool) :
    concentrated.prob atom = oldJoint.prob atom * concentrationDensity atom.1 := by
  rcases atom with ⟨query, hidden⟩
  cases query <;> cases hidden <;> norm_num [concentrated, oldJoint, concentrationDensity,
    FinDist.prob_pure_eq_ite]

/-- The actual charge is two, not the OLD-model mean of one fiftieth. -/
theorem concentrated_defect :
    concentrated.expect (fun atom =>
      FinDist.conditionalTransportDefect oldJoint newJoint Prod.fst atom.1) = 2 := by
  simp only [concentrated, FinDist.expect_pure, joint_defect, if_true]

/-- Dropping the density from the source bound would give a false inequality. -/
theorem density_cannot_be_dropped :
    2 * FinDist.atomVariation oldJoint newJoint <
      concentrated.expect (fun atom =>
        FinDist.conditionalTransportDefect oldJoint newJoint Prod.fst atom.1) := by
  rw [joint_variation, concentrated_defect]
  norm_num

/-- The correct source term accounts for both changed atoms with their density. -/
theorem density_weighted_variation :
    (∑ atom, concentrationDensity atom.1 * |oldJoint.prob atom - newJoint.prob atom|) = 2 := by
  norm_num [fourAtoms, concentrationDensity, oldJoint, newJoint,
    FinDist.prob_pure_eq_ite]

/-- The proved bound remains valid for the concentrated actual law. -/
theorem concentrated_source_bound :
    concentrated.expect (fun atom =>
      FinDist.conditionalTransportDefect oldJoint newJoint Prod.fst atom.1) ≤
      2 * ∑ atom, concentrationDensity atom.1 * |oldJoint.prob atom - newJoint.prob atom| := by
  simpa only [one_mul, mul_one] using FinDist.expect_transport_le_of_density
    oldJoint newJoint concentrated Prod.fst concentrationDensity (fun _ => 1)
    (by intro tag; cases tag <;> norm_num [concentrationDensity])
    (fun _ => by norm_num) concentrated_density

/-- If NEW loses the OLD query, its defect is one rather than a fake conditional. -/
theorem disappearing_query :
    FinDist.conditionalTransportDefect oldJoint (FinDist.pure (false, false))
      Prod.fst true = 1 := by
  classical
  rw [FinDist.conditionalTransportDefect, if_pos (oldJoint_reached true)]
  simp

/-- An absent OLD query carries no charge, irrespective of NEW support. -/
theorem absent_old_query :
    FinDist.conditionalTransportDefect (FinDist.pure (false, false)) newJoint
      Prod.fst true = 0 := by
  classical
  simp [FinDist.conditionalTransportDefect]

/-- A small change inside the rare fiber introduces a genuinely new atom. -/
def softJoint : FinDist (Bool × Bool) :=
  FinDist.mix (99 / 100) (by norm_num) (by norm_num) oldJoint newJoint

/-- The fiber-relative source rate is one fiftieth, without a reach denominator. -/
theorem soft_fiber_rate (tag : Bool) :
    FinDist.fiberAtomVariation oldJoint softJoint Prod.fst tag ≤
      (1 / 50) * (oldJoint.map Prod.fst).prob tag := by
  rw [oldJoint_mass]
  cases tag <;> norm_num [FinDist.fiberAtomVariation, fourAtoms, softJoint,
    oldJoint, newJoint, FinDist.prob_pure_eq_ite]

/-- The relative-fiber theorem yields a small supported conditional error. -/
theorem soft_conditional_bound (tag : Bool) :
    FinDist.conditionalTransportDefect oldJoint softJoint Prod.fst tag ≤ 1 / 25 := by
  have bound := FinDist.conditionalTransportDefect_le_of_fiberRate
    oldJoint softJoint Prod.fst tag (oldJoint_reached tag) (1 / 50) (soft_fiber_rate tag)
  norm_num at bound ⊢
  exact bound

/-- Even concentration on the rare query does not amplify the uniform fiber rate. -/
theorem soft_actual_bound :
    concentrated.expect (fun atom =>
      FinDist.conditionalTransportDefect oldJoint softJoint Prod.fst atom.1) ≤ 1 / 25 := by
  simpa only [concentrated, FinDist.expect_pure] using soft_conditional_bound true

/-- The positive test includes NEW-only atoms, not hidden full support. -/
theorem soft_new_atom :
    oldJoint.prob (true, true) = 0 ∧ softJoint.prob (true, true) = 1 / 10000 := by
  norm_num [softJoint, oldJoint, newJoint, FinDist.prob_pure_eq_ite]

/-- No finite atom-relative rate is available here. The fiber hypothesis is
strictly weaker, rather than an atomwise absolute-continuity premise in disguise. -/
theorem soft_no_atom_rate (rate : ℝ) :
    ¬ ∀ atom, |oldJoint.prob atom - softJoint.prob atom| ≤ rate * oldJoint.prob atom := by
  intro small
  have impossible := small (true, true)
  rw [soft_new_atom.1, soft_new_atom.2] at impossible
  norm_num at impossible

end GameTheory.ReBeL.Examples.SourceRates

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Retain every legal and counterfactual history. -/
local instance sourceControlHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Retain inactive menus in the policy carrier. -/
local instance sourceControlChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Equality remains confined to the real-valued parent learner. -/
local instance sourceControlInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- The original finite parent term, positive bias and child loss remain visible.
The additional error is now expressed in actual continuation outcome laws and
unnormalized reference atoms, retaining the arbitrary opponent's exact density. -/
def freshChainControlSourceBudget
    (unknown : Profile (model fullPrior).behavioralSignature) (t : Nat) [NeZero t] : ℝ :=
  (cfrDDepthErrorConstant (model fullPrior) decisionClock informationControlFullFallback 2 1 0 +
      cfrDDepthErrorConstant (model fullPrior) decisionClock informationControlFullFallback 2 1 1) *
      (1 / 8) +
    (cfrDDepthFiniteConstant (model fullPrior) decisionClock informationControlFullFallback
        2 1 2 0 +
      cfrDDepthFiniteConstant (model fullPrior) decisionClock informationControlFullFallback
        2 1 2 1) / Real.sqrt t + 1 / 4 +
    cfrDSourceEnvelopeLoss (model fullPrior) (cfrIterationLaw t) (freshControlParentPlays t)
      (fun n => cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t n) 2)
      informationControlFullFallback unknown 0 1 2 1 2 (freshChainControlLoss 1)

/-- The source budget bounds the already established actual-prefix charge. -/
theorem freshChainControl_weightedBudget_le_source
    (unknown : Profile (model fullPrior).behavioralSignature) (t : Nat) [NeZero t] :
    freshChainControlWeightedBudget unknown t ≤ freshChainControlSourceBudget unknown t := by
  unfold freshChainControlWeightedBudget freshChainControlSourceBudget
  apply add_le_add (le_refl _)
  exact cfrDWeightedTransportLoss_le_source (model fullPrior) (perfectRecall fullPrior)
    (cfrIterationLaw t) (freshControlParentPlays t)
    (fun n => cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
      cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t n) 2)
    informationControlFullFallback unknown 0 1 (by decide) (cfrPayoff 1) 2 1 2
    (freshChainControlLoss 1) (by norm_num) (fun h => cfrPayoff_abs_le_two 1 h)

/-- This actual execution performs two fresh child solves and uses a biased
finite-time parent. No envelope, drift or root-security inequality is an input. -/
theorem freshChainControl_biased_source_security
    (reference : Profile (model fullPrior).behavioralSignature)
    (equilibrium : IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreference (fun h who => cfrPayoff who h)) reference)
    (unknown : Profile (model fullPrior).behavioralSignature) (t : Nat) [NeZero t] :
    ((model fullPrior).runBehavioral reference 3).expect (cfrPayoff 0) -
        freshChainControlSourceBudget unknown t ≤
      (privateCarriedResolve (model fullPrior) (cfrIterationLaw t) (freshControlParentPlays t)
        (cfrDFreshChainResolver (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t) 2)
        unknown 0 2 1).expect (cfrPayoff 0) := by
  have previous := freshChainControl_biased_weighted_security reference equilibrium unknown t
  have comparison := freshChainControl_weightedBudget_le_source unknown t
  linarith only [previous, comparison]

/-- No continuation fuel means no source cost, even when the references disagree. -/
theorem freshChainControl_source_zero_fuel
    (unknown : Profile (model fullPrior).behavioralSignature) :
    cfrDSourceEnvelopeLoss (model fullPrior) (FinDist.pure ()) freshControlModels
      (freshChainControlProfiles 2) informationControlFullFallback unknown 0 1 2 0 2
      (freshChainControlLoss 1) = 0 := by
  simp [cfrDSourceEnvelopeLoss, cfrDFreshSourceCost, cfrDCutLive_zero,
    FinDist.expect_const]

/-- The actual two-solve construction discharges its reference rate with zero.
This is equality of unilateral source laws, not model/actual posterior equality. -/
theorem freshChainControl_parent_fiber_zero (t : Nat) (n : Fin t)
    (tag : (model fullPrior).InfoState 1 × Bool) :
    FinDist.fiberAtomVariation
      (unilateralReferenceLaw (model fullPrior) (freshControlParentPlays t n)
        informationControlFullFallback 1 2)
      (unilateralReferenceLaw (model fullPrior)
        (cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t n) 2)
        informationControlFullFallback 1 2)
      (fun h => ((model fullPrior).infoOf 1 h.trace, cfrDCutLive 1 h)) tag = 0 := by
  have referenceLaw : unilateralReferenceLaw (model fullPrior)
      (cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t n) 2)
      informationControlFullFallback 1 2 =
        unilateralReferenceLaw (model fullPrior) (freshControlParentPlays t n)
          informationControlFullFallback 1 2 :=
    cfrDFreshInformationChain_referenceLaw (reducedModel fullPrior)
      pbsRootControlFallback cfrPayoff 2 1 2 freshChainControlLoss
      (freshControlParentPlays t n) 1 2
  rw [referenceLaw]
  simp [FinDist.fiberAtomVariation]

/-- The explicit budget retains finite outer T, positive parent bias and both
child tolerances. It contains no unknown-opponent density or minimum reach. -/
def freshChainControlRateBudget (t : Nat) (outcomeRate : ℝ) : ℝ :=
  (cfrDDepthErrorConstant (model fullPrior) decisionClock informationControlFullFallback 2 1 0 +
      cfrDDepthErrorConstant (model fullPrior) decisionClock informationControlFullFallback 2 1 1) *
      (1 / 8) +
    (cfrDDepthFiniteConstant (model fullPrior) decisionClock informationControlFullFallback
        2 1 2 0 +
      cfrDDepthFiniteConstant (model fullPrior) decisionClock informationControlFullFallback
        2 1 2 1) / Real.sqrt t + 1 / 4 +
    (freshChainControlLoss 1 + 2 * outcomeRate)

/-- Only continuation outcome variation remains an input source rate. The
reference-rate premise is discharged by the real two-solve implementation. -/
theorem freshChainControl_weightedBudget_le_rate
    (unknown : Profile (model fullPrior).behavioralSignature) (t : Nat) [NeZero t]
    (outcomeRate : ℝ) (nonneg : 0 ≤ outcomeRate)
    (small : ∀ n h, cfrDFreshOutcomeVariation (model fullPrior) (freshControlParentPlays t n)
      (cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t n) 2) 1 h ≤ outcomeRate) :
    freshChainControlWeightedBudget unknown t ≤ freshChainControlRateBudget t outcomeRate := by
  unfold freshChainControlWeightedBudget freshChainControlRateBudget
  apply add_le_add (le_refl _)
  have charge := cfrDWeightedTransportLoss_le_fiberRates (model fullPrior)
    (perfectRecall fullPrior) (cfrIterationLaw t) (freshControlParentPlays t)
    (fun n => cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
      cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t n) 2)
    informationControlFullFallback unknown 0 1 (by decide) (cfrPayoff 1) 2 1 2
    (freshChainControlLoss 1) outcomeRate 0 (by norm_num)
    (le_of_lt (freshChainControlLoss_pos 1)) nonneg (by norm_num)
    (fun h => cfrPayoff_abs_le_two 1 h) small (by
      intro n tag _
      rw [freshChainControl_parent_fiber_zero]
      simp)
  simpa only [mul_zero, add_zero] using charge

/-- Quantitative source rates are consumed by the actual biased finite parent
and two fresh children. Small continuation variation is NOT inferred from Nash. -/
theorem freshChainControl_biased_rate_security
    (reference : Profile (model fullPrior).behavioralSignature)
    (equilibrium : IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreference (fun h who => cfrPayoff who h)) reference)
    (unknown : Profile (model fullPrior).behavioralSignature) (t : Nat) [NeZero t]
    (outcomeRate : ℝ) (nonneg : 0 ≤ outcomeRate)
    (small : ∀ n h, cfrDFreshOutcomeVariation (model fullPrior) (freshControlParentPlays t n)
      (cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t n) 2) 1 h ≤ outcomeRate) :
    ((model fullPrior).runBehavioral reference 3).expect (cfrPayoff 0) -
        freshChainControlRateBudget t outcomeRate ≤
      (privateCarriedResolve (model fullPrior) (cfrIterationLaw t) (freshControlParentPlays t)
        (cfrDFreshChainResolver (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t) 2)
        unknown 0 2 1).expect (cfrPayoff 0) := by
  have previous := freshChainControl_biased_weighted_security reference equilibrium unknown t
  have comparison := freshChainControl_weightedBudget_le_rate unknown t outcomeRate nonneg small
  linarith only [previous, comparison]

end GameTheory.ReBeL.Examples.HiddenTypes
