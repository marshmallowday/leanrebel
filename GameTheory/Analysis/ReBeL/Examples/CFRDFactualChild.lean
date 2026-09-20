/-
# Constructed factual child equilibrium and boundary controls

The child is solved at a genuine live public root of the canonical two-stage
hidden-type protocol. Nash is consumed as a theorem about the constructed
profile, never an input. Unvisited factual public states still have no factual
posterior even when they are present in a unilateral reference query.
-/

import GameTheory.Analysis.ReBeL.CFRDFactualChild
import GameTheory.Analysis.ReBeL.Examples.CFRDPublicSplice

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Canonical finite history enumeration for the factual-child constructor. -/
local instance factualChildHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- A genuinely factual live history under the deterministic first-round trunk. -/
def factualChildHistory : (protocol fullPrior).History :=
  decode (.second false false false false)

/-- Actual support is derived from positive chance and both own-reach factors. -/
theorem factualChildHistory_supported :
    factualChildHistory ∈
      ((model fullPrior).runBehavioral (carriedBitProfile false) 2).support := by
  apply FinDist.prob_pos_iff.mp
  rw [run_probability_factorization (model fullPrior), Fin.prod_univ_two]
  have mask : outcomeChanceWeight 2 factualChildHistory =
      chanceReach factualChildHistory.trace := by
    unfold outcomeChanceWeight
    exact if_pos ⟨Nat.le_refl 2, Or.inl rfl⟩
  rw [mask, factualChildHistory, zeroControl_own_reach, zeroControl_own_reach]
  simpa [GameTheory.ReBeL.Rational.HiddenTypes.own] using
    chanceReach_pos (decode (.second false false false false)).trace

/-- The child constructor receives a proof from actual play, not a guessed PBS. -/
theorem factualChild_possible :
    CFRDFactualChildPossible (reducedModel fullPrior) (carriedBitProfile false) 2 1
      (publicTrace (model fullPrior).toInfoSignals factualChildHistory.trace) := by
  refine ⟨factualChildHistory, ⟨rfl, ?_⟩, factualChildHistory_supported⟩
  rw [cfrDCutLive, decide_eq_true_eq]
  exact ⟨by decide, fun impossible => impossible⟩

/-- One legal complete profile is obtained by the exact child construction. -/
def factualChildProfile : Profile (model fullPrior).behavioralSignature :=
  cfrDFactualChildProfile (reducedModel fullPrior) (carriedBitProfile false)
    cfrFallback 2 1 (fun history who => cfrPayoff who history)

/-- The entire original prefix law, including chance correlation, is unchanged. -/
theorem factualChild_prefix :
    (model fullPrior).runBehavioral factualChildProfile 2 =
      (model fullPrior).runBehavioral (carriedBitProfile false) 2 :=
  cfrDFactualChildProfile_prefixLaw (reducedModel fullPrior) (carriedBitProfile false)
    cfrFallback 2 1 (fun history who => cfrPayoff who history)

/-- Every complete behavioral deviation is controlled at this live joint PBS.
The theorem calls the constructor's Nash proof; no equilibrium is postulated. -/
theorem factualChild_isNash :
    IsNash (behavioralBeliefForm (model fullPrior)
        (cfrDFactualChildBelief (reducedModel fullPrior) (carriedBitProfile false) 2 1
          (publicTrace (model fullPrior).toInfoSignals factualChildHistory.trace)
          factualChild_possible) 1)
      (euPreference (fun history who => cfrPayoff who history)) factualChildProfile :=
  cfrDFactualChildProfile_isNash (reducedModel fullPrior) (carriedBitProfile false)
    cfrFallback 2 1 (fun history who => cfrPayoff who history) _ factualChild_possible

/-- A counterfactual-only public root is not mislabeled a factual live child. -/
theorem factualChild_unvisited_absent :
    ¬ CFRDFactualChildPossible (reducedModel fullPrior) (carriedBitProfile false) 2 1
      (publicTrace (model fullPrior).toInfoSignals zeroControlHistory.trace) := by
  rintro ⟨history, member, reached⟩
  apply publicSplice_unvisited_public
  rw [FinDist.support_map]
  exact ⟨history, reached, member.1⟩

/-- No terminal-horizon child is invented merely to invoke Nash existence. -/
theorem factualChild_zero_remaining_absent (observations : List Phase) :
    ¬ CFRDFactualChildPossible (reducedModel fullPrior) (carriedBitProfile false)
      2 0 observations :=
  cfrDFactualChildPossible_zero (reducedModel fullPrior) (carriedBitProfile false) 2 observations

end GameTheory.ReBeL.Examples.HiddenTypes
