/-
# Directed payoff controls and an actual two-solve consumer

A nonconstant payoff is preserved while all outcome mass changes labels.
Direction and both marginals are essential. The game consumer retains the
noisy finite parent and two fresh child solves; their small directed cost is
still an explicit source obligation, not a consequence of approximate Nash.
-/

import GameTheory.Analysis.ReBeL.CFRDValueCoupling
import GameTheory.Analysis.ReBeL.Examples.CFRDSourceRates

noncomputable section

namespace GameTheory.ReBeL.Examples.ValueCoupling

open GameTheory.Math.Probability

private theorem fourAtoms : (Finset.univ : Finset (Bool × Bool)) =
    {(false, false), (false, true), (true, false), (true, true)} := by decide

/-- Two equally likely payoff types change only their payoff-irrelevant label. -/
def joint : FinDist ((Bool × Bool) × (Bool × Bool)) :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure ((false, false), (false, true)))
    (FinDist.pure ((true, false), (true, true)))

/-- The old marginal puts all mass on the false label. -/
def old : FinDist (Bool × Bool) := joint.map Prod.fst

/-- The new marginal puts all mass on the true label. -/
def fresh : FinDist (Bool × Bool) := joint.map Prod.snd

/-- The payoff varies with the first bit, so this is not a constant-payoff test. -/
def value (outcome : Bool × Bool) : ℝ := if outcome.1 then 1 else -1

/-- Exact masses certify both disjoint supports and the nonzero type weights. -/
theorem old_mass (outcome : Bool × Bool) :
    old.prob outcome = if outcome.2 then 0 else 1 / 2 := by
  rcases outcome with ⟨type, label⟩
  rw [old, FinDist.map_eq_bind, FinDist.prob_bind]
  cases type <;> cases label <;> norm_num [joint, FinDist.expect_mix,
    FinDist.expect_pure, FinDist.prob_pure_eq_ite]

/-- The fresh marginal has the same payoff types, with entirely new labels. -/
theorem fresh_mass (outcome : Bool × Bool) :
    fresh.prob outcome = if outcome.2 then 1 / 2 else 0 := by
  rcases outcome with ⟨type, label⟩
  rw [fresh, FinDist.map_eq_bind, FinDist.prob_bind]
  cases type <;> cases label <;> norm_num [joint, FinDist.expect_mix,
    FinDist.expect_pure, FinDist.prob_pure_eq_ite]

/-- The older L1 route pays the maximum possible outcome variation. -/
theorem outcome_variation_two : FinDist.atomVariation old fresh = 2 := by
  classical
  rw [FinDist.atomVariation, fourAtoms]
  norm_num [old_mass, fresh_mass]

/-- The directed source cost nevertheless vanishes exactly. -/
theorem directed_cost_zero : FinDist.directedValueCost joint value value = 0 := by
  norm_num [FinDist.directedValueCost, joint, value, FinDist.expect_mix,
    FinDist.expect_pure]

/-- Consume the public marginal-preserving theorem, not a numerical assertion. -/
theorem payoff_change_nonpositive : fresh.expect value - old.expect value ≤ 0 := by
  have comparison := FinDist.expect_sub_le_directedValueCost old fresh joint value value rfl rfl
  rw [directed_cost_zero] at comparison
  exact comparison

/-- Positive and negative payoff types both occur in this example. -/
theorem payoff_nonconstant : value (false, false) ≠ value (true, true) := by
  norm_num [value]

/-- The cost is directed: a harmless decrease cannot justify the reverse move. -/
theorem reverse_cost_not_valid :
    FinDist.directedValueCost (FinDist.pure (true, false))
      (fun b => if b then (1 : ℝ) else 0) (fun b => if b then (1 : ℝ) else 0) = 0 ∧
    FinDist.directedValueCost (FinDist.pure (false, true))
      (fun b => if b then (1 : ℝ) else 0) (fun b => if b then (1 : ℝ) else 0) = 1 := by
  norm_num [FinDist.directedValueCost, FinDist.expect_pure]

/-- A fabricated zero-cost joint law with the wrong new marginal is not a
valid certificate for an actual increase from zero to one. -/
theorem wrong_marginal_rejected :
    (FinDist.pure (false, false)).map Prod.snd ≠ FinDist.pure true := by
  intro equal
  have masses := congrArg (fun law : FinDist Bool => law.prob true) equal
  norm_num [FinDist.map_pure, FinDist.prob_pure_eq_ite] at masses

end GameTheory.ReBeL.Examples.ValueCoupling

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Keep every legal history, including factually absent reference histories. -/
local instance couplingControlHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Inactive singleton menus remain in the full policy carrier. -/
local instance couplingControlChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Equality is restricted to the real-valued proof learner. -/
local instance couplingControlInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- The existing concrete budget with B=2 now charges valueRate, not 2*valueRate. -/
def freshChainControlValueBudget (t : Nat) (valueRate : ℝ) : ℝ :=
  freshChainControlRateBudget t (valueRate / 2)

/-- Both marginal equations refer to the actual finite parent and actual two
fresh solves. Same-cut preservation discharges referenceRate=0 inside the proof. -/
theorem freshChainControl_weightedBudget_le_valueCoupling
    (unknown : Profile (model fullPrior).behavioralSignature) (t : Nat) [NeZero t]
    (valueRate : ℝ) (nonneg : 0 ≤ valueRate)
    (joint : Fin t → (protocol fullPrior).History →
      FinDist ((protocol fullPrior).History × (protocol fullPrior).History))
    (oldMarginal : ∀ n h, (joint n h).map Prod.fst =
      (model fullPrior).runBehavioralFrom (freshControlParentPlays t n) 1 h)
    (newMarginal : ∀ n h, (joint n h).map Prod.snd = (model fullPrior).runBehavioralFrom
      (cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t n) 2) 1 h)
    (small : ∀ n h, FinDist.directedValueCost (joint n h) (cfrPayoff 1) (cfrPayoff 1) ≤
      valueRate) :
    freshChainControlWeightedBudget unknown t ≤ freshChainControlValueBudget t valueRate := by
  have comparison := cfrDWeightedTransportLoss_le_valueCoupling (model fullPrior)
    (perfectRecall fullPrior) (cfrIterationLaw t) (freshControlParentPlays t)
    (fun n => cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
      cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t n) 2)
    informationControlFullFallback unknown 0 1 (by decide) (cfrPayoff 1) 2 1 2
    (freshChainControlLoss 1) valueRate 0 (by norm_num) (by norm_num [freshChainControlLoss])
    nonneg (le_refl _) joint oldMarginal newMarginal small
    (fun n tag _ => by rw [freshChainControl_parent_fiber_zero]; simp)
  unfold freshChainControlWeightedBudget freshChainControlValueBudget
    freshChainControlRateBudget
  linarith only [comparison]

/-- Actual unknown-opponent security keeps positive parent noise, finite T,
and distinct child tolerances. A small coupling cost remains an explicit
source premise; neither native stability nor all of M06 is asserted here. -/
theorem freshChainControl_biased_valueCoupling_security
    (reference : Profile (model fullPrior).behavioralSignature)
    (equilibrium : IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreference (fun h who => cfrPayoff who h)) reference)
    (unknown : Profile (model fullPrior).behavioralSignature) (t : Nat) [NeZero t]
    (valueRate : ℝ) (nonneg : 0 ≤ valueRate)
    (joint : Fin t → (protocol fullPrior).History →
      FinDist ((protocol fullPrior).History × (protocol fullPrior).History))
    (oldMarginal : ∀ n h, (joint n h).map Prod.fst =
      (model fullPrior).runBehavioralFrom (freshControlParentPlays t n) 1 h)
    (newMarginal : ∀ n h, (joint n h).map Prod.snd = (model fullPrior).runBehavioralFrom
      (cfrDFreshInformationChain (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t n) 2) 1 h)
    (small : ∀ n h, FinDist.directedValueCost (joint n h) (cfrPayoff 1) (cfrPayoff 1) ≤
      valueRate) :
    ((model fullPrior).runBehavioral reference 3).expect (cfrPayoff 0) -
        freshChainControlValueBudget t valueRate ≤
      (privateCarriedResolve (model fullPrior) (cfrIterationLaw t) (freshControlParentPlays t)
        (cfrDFreshChainResolver (reducedModel fullPrior) pbsRootControlFallback
          cfrPayoff 2 1 2 freshChainControlLoss (freshControlParentPlays t) 2)
        unknown 0 2 1).expect (cfrPayoff 0) := by
  have security := freshChainControl_biased_weighted_security reference equilibrium unknown t
  have comparison := freshChainControl_weightedBudget_le_valueCoupling unknown t valueRate
    nonneg joint oldMarginal newMarginal small
  linarith only [security, comparison]

end GameTheory.ReBeL.Examples.HiddenTypes
