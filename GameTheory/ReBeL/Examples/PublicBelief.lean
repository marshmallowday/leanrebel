/-
# Hostile public beliefs on one fixed canonical game

The two correlated beliefs below inhabit the SAME history carrier, unlike a
comparison of two differently parameterized games. They have equal full-AOH
marginals and unequal actual continuation rewards. The fully revealing dice
control tests the stronger public-history premise needed for degeneration.
-/

import GameTheory.ReBeL.Examples.HiddenTypesHistories
import GameTheory.ReBeL.Examples.ObservedDice
import GameTheory.ReBeL.StrategicEquivalence
import GameTheory.ReBeL.PublicSubgame

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

/-- An arbitrary joint type law lifted to actual histories of the fixed full-support game. -/
def drawBelief (law : FinDist Types) :
    PublicBelief (model fullPrior).toInfoSignals [Phase.first, Phase.initial] where
  law := law.map fullDraw
  supported h positive := by
    rw [FinDist.support_map] at positive
    obtain ⟨types, _, rfl⟩ := positive
    rfl

/-- Each full private AOH marginal is still only a function of that player's own type. -/
theorem drawBelief_marginal (law : FinDist Types) (i : Player) :
    (drawBelief law).marginal i =
      (law.map (ownType i)).map (fun own =>
        AOH.step (AOH.initial none Phase.initial) (none : Option Bool) (some own) Phase.first) := by
  simp only [PublicBelief.marginal, drawBelief, FinDist.map_comp]
  rfl

/-- Equal local marginals do not determine the joint PBS, even on the same public fiber. -/
theorem drawBelief_same_marginals (i : Player) :
    (drawBelief correlated).marginal i = (drawBelief anticorrelated).marginal i := by
  rw [drawBelief_marginal, drawBelief_marginal, same_marginals]

/-- A legal total fallback and play profile; no menu nonemptiness oracle is assumed. -/
def pbsProfile : Profile (model fullPrior).behavioralSignature :=
  fun i => (fullPlanPolicy fullPrior i (correlationPlans i)).toBehavioral

/-- State simplification is proved from the canonical history runner at every root. -/
theorem map_state_plan_continuation (plans : Player → Plan) (fuel : Nat)
    (history : (protocol fullPrior).History) :
    ((model fullPrior).runBehavioralFrom
      (fun i => (fullPlanPolicy fullPrior i (plans i)).toBehavioral) fuel history).map
        History.state = (protocol fullPrior).runFor (planChooser fullPrior plans)
          fuel history.state := by
  rw [InformationModel.runBehavioralFrom_toBehavioral]
  unfold fullPlanPolicy
  rw [liftPolicy_runFrom]
  unfold InformationModel.runFrom
  rw [plan_historyChooser]
  exact map_state_runHistoryFor (planChooser fullPrior plans) fuel history

/-- The PBS continuation evaluates the two remaining stages of the original game. -/
theorem drawBelief_value (law : FinDist Types) :
    (PublicBelief.continuationLaw (model fullPrior) pbsProfile 2 (drawBelief law)).expect
        (fun h => cumulativeUtility (reward fullPrior) h 0) =
      law.expect (fun types => 1 + winValue (types.1 == types.2)) := by
  rw [PublicBelief.continuationLaw, drawBelief, FinDist.expect_bind, FinDist.expect_map]
  apply FinDist.expect_congr
  intro types _
  calc
    _ = (((model fullPrior).runBehavioralFrom pbsProfile 2 (fullDraw types)).map
          History.state).expect (fun state => potential state 0) := by
      rw [FinDist.expect_map]
      exact FinDist.expect_congr fun h _ => cumulative_eq fullPrior h 0
    _ = _ := by
      rw [pbsProfile, map_state_plan_continuation, run_first, FinDist.expect_pure]
      simp [potential, signed, firstResult, finalResult, firstJoint, secondJoint,
        action, correlationPlans, ownType, winValue]

/-- Concrete downstream values are 2 and 0, despite identical one-player marginals. -/
theorem drawBelief_payoff_separation :
    (PublicBelief.continuationLaw (model fullPrior) pbsProfile 2
      (drawBelief correlated)).expect (fun h => cumulativeUtility (reward fullPrior) h 0) = 2 ∧
    (PublicBelief.continuationLaw (model fullPrior) pbsProfile 2
      (drawBelief anticorrelated)).expect (fun h => cumulativeUtility (reward fullPrior) h 0) = 0 := by
  constructor <;> rw [drawBelief_value] <;>
    norm_num [correlated, anticorrelated, FinDist.expect_mix, FinDist.expect_pure, winValue]

/-- The actual iterative Bayesian referee has those same computed values. -/
theorem drawBelief_referee_value (law : FinDist Types) :
    (PublicBelief.run (model fullPrior) pbsProfile 2 ⟨_, drawBelief law⟩).expect
        (fun next => next.2.law.expect (fun h => cumulativeUtility (reward fullPrior) h 0)) =
      law.expect (fun types => 1 + winValue (types.1 == types.2)) := by
  rw [PublicBelief.run_expect, drawBelief_value]

/-- A false public observation has no fabricated posterior, for every input joint type law. -/
theorem drawBelief_impossible (law : FinDist Types) :
    PublicBelief.condition? (S := (model fullPrior).toInfoSignals)
      (drawBelief law).law [Phase.initial] = none := by
  rw [PublicBelief.condition?_eq_none]
  rintro ⟨h, observed, supported⟩
  have actual := (drawBelief law).supported h supported
  rw [actual] at observed
  cases observed

/-- A concrete nonempty legal game instantiates both Nash-preservation directions.
The quantifier is over ALL local behavioral policies, not the Plan test family. -/
theorem drawBelief_strategic_equivalence (law : FinDist Types)
    (profile : Profile (model fullPrior).behavioralSignature) :
    IsNash (Prescription.originalGame (reducedModel fullPrior) ⟨_, drawBelief law⟩ 2)
        (euPreference (cumulativeUtility (reward fullPrior))) profile ↔
      IsNash (Prescription.beliefGame (reducedModel fullPrior) pbsProfile
        ⟨_, drawBelief law⟩ 2) (euPreference (cumulativeUtility (reward fullPrior)))
          (Prescription.encodeProfile (reducedModel fullPrior) profile) :=
  Prescription.isNash_encode_iff (reducedModel fullPrior) pbsProfile
    ⟨_, drawBelief law⟩ 2 profile (cumulativeUtility (reward fullPrior))

/-- Zero reach under the reference policy does not remove a later deviation site. -/
theorem offPath_prescription_roundtrip (i : Player)
    (replacement : (model fullPrior).BehavioralPolicy i) :
    Prescription.decode (reducedModel fullPrior) i (pbsProfile i)
      (Prescription.encode (reducedModel fullPrior) i replacement)
        ((model fullPrior).infoOf i offPathHistory.trace) =
      replacement ((model fullPrior).infoOf i offPathHistory.trace) :=
  Prescription.decode_encode_at_history (reducedModel fullPrior) i
    (pbsProfile i) replacement offPathHistory

/-- The off-path state is live; returning it with zero fuel is a cut, not a terminal. -/
theorem offPath_is_cut :
    PublicBelief.CutLeaf (model fullPrior)
      (publicTrace (model fullPrior).toInfoSignals offPathHistory.trace) 0 offPathHistory :=
  PublicBelief.zero_fuel_cut (model fullPrior) offPathHistory offPath_nonterminal

end GameTheory.ReBeL.Examples.HiddenTypes

namespace GameTheory.ReBeL.Examples.ObservedDice

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

/-- The fully revealing control identifies histories publicly, not merely privately. -/
theorem revealing_public_injective :
    Function.Injective (fun h : protocol.History => publicTrace revealingSignals h.trace) := by
  intro first second equal
  rcases history_cases first with rfl | ⟨firstDice, rfl⟩ <;>
    rcases history_cases second with rfl | ⟨secondDice, rfl⟩
  · rfl
  · cases equal
  · cases equal
  · have observed : [some firstDice, none] = [some secondDice, none] := equal
    exact congrArg draw (Option.some.inj (List.cons.inj observed).1)

/-- Every PBS in the fully public control degenerates to its unique known history. -/
theorem revealing_pbs_degenerates (history : protocol.History)
    (belief : PublicBelief revealingSignals (publicTrace revealingSignals history.trace)) :
    belief.law = FinDist.pure history :=
  PublicBelief.eq_pure_of_public_injective revealing_public_injective belief history rfl

/-- Bayes conditioning, not just an already-pure initial law, has the same degeneration. -/
theorem revealing_posterior (law : FinDist protocol.History) (history : protocol.History)
    (possible : PublicBelief.Possible (S := revealingSignals) law
      (publicTrace revealingSignals history.trace)) :
    (PublicBelief.condition law (publicTrace revealingSignals history.trace) possible).law =
      FinDist.pure history :=
  revealing_pbs_degenerates history _

end GameTheory.ReBeL.Examples.ObservedDice
