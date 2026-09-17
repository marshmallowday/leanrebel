/-
# Chance and information-local reach factors

The factorization is derived from canonical behavioral execution. The chance
factor retains correlated transitions. Each strategic factor depends only on
one player's full AOH and its own policy, not on the hidden history or an
opponent's private information.
-/

import GameTheory.ReBeL.Information
import GameTheory.Protocol.BehavioralReach

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability
open scoped BigOperators

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

/-- The policy-independent product of actual chance-transition probabilities. -/
def chanceReach : {state : E.State} → E.Trace state → ℝ
  | _, .start => 1
  | target, .extend prior joint legal _ =>
      chanceReach prior * (E.step _ ⟨joint, legal⟩).prob target

/-- Canonical histories contain only chance-supported transitions. -/
theorem chanceReach_pos {state : E.State} (trace : E.Trace state) :
    0 < chanceReach trace := by
  induction trace with
  | start => exact zero_lt_one
  | extend prior joint legal realized ih =>
      exact mul_pos ih (FinDist.prob_pos_iff.mpr realized)

/-- Actual history reach is chance times all players' independent action factors. -/
theorem historyReach_factorization [Fintype ι] (M : InformationModel E)
    (profile : Profile M.behavioralSignature) {state : E.State} (trace : E.Trace state) :
    M.historyReachProbability profile ⟨state, trace⟩ =
      chanceReach trace * ∏ i, M.playerReachProbability profile i trace := by
  classical
  induction trace with
  | start =>
      simp [chanceReach, InformationModel.playerReachProbability,
        InformationModel.historyReachProbability, InformationModel.runBehavioral,
        InformationModel.runBehavioralFrom, Trace.length, initHistory]
  | @extend source target prior joint legal realized ih =>
      rw [InformationModel.historyReachProbability_extend M profile prior joint legal realized,
        ih, InformationModel.stepProb,
        InformationModel.behavioralJoint_prob_eq_prod M profile prior legal.1]
      simp only [chanceReach, InformationModel.playerReachProbability,
        InformationModel.playerStepProb, Finset.prod_mul_distrib]
      ring

variable (M : InformationModel E)

/-- An own-reach factor computed solely from a private AOH and its local policy.
Inactive `none` choices are included, as in the canonical behavioral runner. -/
def ownReach (i : ι) (policy : (fullInformation M).BehavioralPolicy i) :
    AOH (E.Action i) (M.PrivateSignal i) M.PublicSignal → ℝ
  | .initial _ _ => 1
  | .step prior action _ _ =>
      ownReach i policy prior * (policy prior |>.map Subtype.val).prob action

theorem ownReach_nonneg (i : ι) (policy : (fullInformation M).BehavioralPolicy i)
    (info : AOH (E.Action i) (M.PrivateSignal i) M.PublicSignal) :
    0 ≤ ownReach M i policy info := by
  induction info with
  | initial => exact zero_le_one
  | step prior action _ _ ih =>
      exact mul_nonneg ih (FinDist.prob_nonneg _ _)

/-- The AOH-only computation equals the canonical own reach at every legal history,
including histories of zero probability under the current profile. -/
theorem ownReach_eq_player (profile : Profile (fullInformation M).behavioralSignature)
    (i : ι) {state : E.State} (trace : E.Trace state) :
    ownReach M i (profile i) ((fullInformation M).infoOf i trace) =
      (fullInformation M).playerReachProbability profile i trace := by
  classical
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih =>
      simp only [InfoSignals.infoOf, fullInformation, fullSignals, ownReach,
        InformationModel.playerReachProbability] at ih ⊢
      rw [ih]
      congr 1
      exact FinDist.prob_map_of_injective Subtype.val Subtype.val_injective
        (profile i ((fullInformation M).infoOf i prior))
        ((fullInformation M).choicesOfLegal prior ⟨joint, legal⟩ i)

/-- The complete, information-local reach representation of canonical execution. -/
theorem historyReach_eq_chance_mul_own [Fintype ι]
    (profile : Profile (fullInformation M).behavioralSignature)
    {state : E.State} (trace : E.Trace state) :
    (fullInformation M).historyReachProbability profile ⟨state, trace⟩ =
      chanceReach trace * ∏ i, ownReach M i (profile i) ((fullInformation M).infoOf i trace) := by
  rw [historyReach_factorization]
  congr 1
  exact Finset.prod_congr rfl fun i _ => (ownReach_eq_player M profile i trace).symm

/-- Equal local AOHs have equal own reach even if hidden states or chance paths differ. -/
theorem ownReach_eq_of_info_eq (profile : Profile (fullInformation M).behavioralSignature)
    (i : ι) (first second : E.History)
    (same : (fullInformation M).infoOf i first.trace =
      (fullInformation M).infoOf i second.trace) :
    (fullInformation M).playerReachProbability profile i first.trace =
      (fullInformation M).playerReachProbability profile i second.trace := by
  rw [← ownReach_eq_player M profile i, ← ownReach_eq_player M profile i, same]

/-- Public histories include the initial observation, so they determine execution depth. -/
theorem publicTrace_length (S : InfoSignals E) {state : E.State} (trace : E.Trace state) :
    (publicTrace S trace).length = trace.length + 1 := by
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih =>
      simpa only [publicTrace, List.length_cons, Trace.length] using congrArg Nat.succ ih

end GameTheory.ReBeL
