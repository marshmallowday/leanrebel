/-
# Envelope controls: real finite children and a strict replacement boundary

The positive instance uses the actual noisy finite-child CFR-D trace at a
live cut. The canonical equilibrium-replacement game separately demonstrates
that an opponent model ceiling need not preserve fixed-opponent exploitation.
-/

import GameTheory.Analysis.ReBeL.CFRDEnvelopeSafety
import GameTheory.Analysis.ReBeL.Examples.CFRDFiniteChild
import GameTheory.Analysis.ReBeL.Examples.CFRDEquilibriumReplacement

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Finite canonical histories for a genuinely live continuation. -/
local instance envelopeHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Finite legal choices include off-policy and inactive information states. -/
local instance envelopeChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Information equality is used by the actual coupled learner. -/
local instance envelopeInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- Child tolerance 1/4 and numerical bias 1/8 are distinct nonzero inputs. -/
def envelopeControlOracle :=
  cfrDConstructedFiniteOracle (reducedModel fullPrior) cfrFallback cfrPayoff 2 1
    2 (1 / 4) (fun _ _ _ _ => 1 / 8)

/-- The actual generated trace, not a sequence supplied as a regret witness. -/
def envelopeControlPlays (t : Nat) : Fin t → Profile (model fullPrior).behavioralSignature :=
  fun n => cfrDDepthPlay (model fullPrior) decisionClock cfrFallback cfrPayoff 2 1
    envelopeControlOracle n.val

/-- Retention instantiates the new interface at a live cut, even for arbitrary
unknown opponents. Its child loss is derived from the finite recurrence. -/
theorem finite_retained_envelope (t : Nat)
    (unknown : Profile (model fullPrior).behavioralSignature) (who opponent : Player)
    (different : opponent ≠ who) :
    CFRDResolverEnvelope (model fullPrior) (envelopeControlPlays t)
      (fun n _ _ => FinDist.pure (envelopeControlPlays t n)) cfrFallback unknown
      who opponent 2 1 (cfrPayoff opponent) (1 / 4) := by
  apply cfrDResolverEnvelope_retained
  · exact different
  · intro n
    exact finiteChildControl_driver_leafOptimal (1 / 4) (by norm_num)
      (fun _ _ _ _ => 1 / 8) n.val opponent

/-- The actual outer learner discharges both regret premises in the envelope
security theorem. Only the original game-value comparison equilibrium is supplied. -/
theorem finite_retained_envelope_security (t : Nat) [NeZero t]
    (reference : Profile (model fullPrior).behavioralSignature)
    (equilibrium : IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreference (fun h who => cfrPayoff who h)) reference)
    (unknown : Profile (model fullPrior).behavioralSignature) (who opponent : Player)
    (different : opponent ≠ who) :
    ((model fullPrior).runBehavioral reference 3).expect (cfrPayoff who) -
      ((cfrDDepthErrorConstant (model fullPrior) decisionClock cfrFallback 2 1 who +
          cfrDDepthErrorConstant (model fullPrior) decisionClock cfrFallback 2 1 opponent) *
          (1 / 8) +
        (cfrDDepthFiniteConstant (model fullPrior) decisionClock cfrFallback 2 1 2 who +
          cfrDDepthFiniteConstant (model fullPrior) decisionClock cfrFallback 2 1 2 opponent) /
          Real.sqrt t + (1 / 4) + (1 / 4)) ≤
      (privateCarriedResolve (model fullPrior) (cfrIterationLaw t) (envelopeControlPlays t)
        (fun n _ _ => FinDist.pure (envelopeControlPlays t n)) unknown who 2 1).expect
          (cfrPayoff who) := by
  exact cfrDDepth_resolve_envelope_security (model fullPrior) decisionClock
    (perfectRecall fullPrior) cfrFallback cfrPayoff (cumulative_zeroSum fullPrior)
    2 1 envelopeControlOracle 2 (1 / 8) (1 / 4) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) cfrPayoff_abs_le_two
    finiteChildControl_biased_accuracy
    (finiteChildControl_driver_leafOptimal (1 / 4) (by norm_num) (fun _ _ _ _ => 1 / 8))
    reference equilibrium unknown who opponent different t _
    (finite_retained_envelope t unknown who opponent different)

/-- Every resolver is irrelevant with zero remaining fuel, including at an
actual history that has no factual model posterior. -/
theorem envelope_zero_fuel (t : Nat) (resolver : CarriedPublicResolver (model fullPrior) (Fin t))
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (n : Fin t) (history : (protocol fullPrior).History) :
    privateResolvedEnvelopeGap (model fullPrior) (envelopeControlPlays t) resolver unknown
      who 2 0 (cfrPayoff who) n history = 0 := by
  apply privateResolvedEnvelopeGap_stopped
  rw [cfrDCutLive_zero]
  decide

end GameTheory.ReBeL.Examples.HiddenTypes

namespace GameTheory.ReBeL.Examples.EquilibriumReplacement

open GameTheory.Math.Probability
open GameTheory.ReBeL.Examples.EquilibriumValue

/-- The replacement obeys the incumbent model's opponent ceiling at every
opposing action. It need not preserve exploitation of the same weak opponent. -/
theorem replacement_opponent_model_ceiling (opponent : Fin 3) :
    expectedUtility replacementUtility 1
        (form.play (Profile.update (strategy 0) 1 opponent)) ≤
      expectedUtility replacementUtility 1 (form.play (strategy 1)) := by
  have bounded := replacement_security 0 (Or.inl rfl) opponent
  rw [replacement_zeroSum.expectedUtility_one, replacement_zeroSum.expectedUtility_one]
  have baseline : expectedUtility replacementUtility 0 (form.play (strategy 1)) = 0 := by
    norm_num [form, strategy, replacementUtility, replacementPayoff]
  rw [baseline]
  linarith

/-- A concrete strict distinction: the model ceiling holds universally while
old-minus-new payoff against one weak opponent is exactly one, not zero. -/
theorem model_ceiling_not_pointwise_retention :
    (∀ opponent : Fin 3,
      expectedUtility replacementUtility 1
          (form.play (Profile.update (strategy 0) 1 opponent)) ≤
        expectedUtility replacementUtility 1 (form.play (strategy 1))) ∧
    expectedUtility replacementUtility 0
        (form.play (Profile.update (strategy 1) 1 (1 : Fin 3))) -
      expectedUtility replacementUtility 0
        (form.play (Profile.update (strategy 0) 1 (1 : Fin 3))) = 1 :=
  ⟨replacement_opponent_model_ceiling, replacement_loses_one⟩

/-- Merely being a legal candidate does not suffice for the model ceiling. -/
theorem bad_candidate_breaks_model_ceiling :
    ¬ expectedUtility replacementUtility 1
        (form.play (Profile.update (strategy 2) 1 (0 : Fin 3))) ≤
      expectedUtility replacementUtility 1 (form.play (strategy 1)) := by
  norm_num [form, strategy, replacementUtility, replacementPayoff]

end GameTheory.ReBeL.Examples.EquilibriumReplacement
