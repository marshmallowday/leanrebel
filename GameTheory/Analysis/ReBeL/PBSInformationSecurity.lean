/-
# One-sided safety of sampled information-set child execution

The actual CFR regret bounds imply security against every fixed behavioral
opponent with the same sum-of-regrets allowance, without doubling a generic
Nash error. The comparison equilibrium belongs to the ORIGINAL PBS game and
only names its value. Private child iterations and their carried state realize
that bound for any finite segmentation of the continuation fuel.
-/

import GameTheory.Analysis.ReBeL.PBSInformationCarried
import GameTheory.Analysis.ReBeL.PBSInformationBudget

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)

private theorem pbsSamplingPayoff_expect (roots : FinDist E.History) (cut : Nat)
    (rootDepth : ∀ history ∈ roots.support, history.trace.length = cut)
    (payoff : Fin 2 → E.History → ℝ)
    (profile : Profile (pbsRootFullInformation M roots).behavioralSignature)
    (fuel : Nat) (who : Fin 2) :
    ((pbsRootFullInformation M roots).runBehavioral profile (fuel + 1)).expect
        (pbsRootPayoff roots payoff who) =
      (roots.bind ((fullInformation M).runBehavioralFrom
        (pbsRootDecodeProfile M roots cut profile) fuel)).expect (payoff who) := by
  exact pbsRootDecodeProfile_expect M roots cut rootDepth profile fuel (payoff who)

variable {observations : List M.PublicSignal}

/-- Exact original-PBS equilibria lift against every new rooted deviation,
not merely against policies already obtained by lifting an original strategy. -/
theorem pbsRootLiftProfile_isNash
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (payoff : Fin 2 → E.History → ℝ) (fuel : Nat)
    (reference : Profile (fullInformation M).behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm (fullInformation M) belief fuel)
      (euPreference (fun history who => payoff who history)) reference) :
    IsNash ((pbsRootFullInformation M belief.law).toBehavioralGameForm (fuel + 1))
      (euPreference (fun history who => pbsRootPayoff belief.law payoff who history))
      (pbsRootBehavioralFullProfile M belief.law reference) := by
  rw [isNash_iff] at equilibrium ⊢
  intro who replacement
  have bound := equilibrium who
    (pbsRootDecodePolicy M belief.law (observations.length - 1) who replacement)
  change (belief.law.bind ((fullInformation M).runBehavioralFrom
      (Profile.update reference who
        (pbsRootDecodePolicy M belief.law (observations.length - 1) who replacement))
      fuel)).expect (payoff who) ≤
    (belief.law.bind ((fullInformation M).runBehavioralFrom reference fuel)).expect
      (payoff who) at bound
  change ((pbsRootFullInformation M belief.law).runBehavioral
      (Profile.update (pbsRootBehavioralFullProfile M belief.law reference) who replacement)
      (fuel + 1)).expect (pbsRootPayoff belief.law payoff who) ≤
    ((pbsRootFullInformation M belief.law).runBehavioral
      (pbsRootBehavioralFullProfile M belief.law reference) (fuel + 1)).expect
      (pbsRootPayoff belief.law payoff who)
  simpa only [pbsSamplingPayoff_expect M belief.law (observations.length - 1)
    (pbsRoot_publicBelief_depth M belief), pbsRootDecodeProfile_update,
    pbsRootDecodeProfile_lift] using bound

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

section Native

variable (roots : FinDist E.History)

local instance securityHistoryFintype : Fintype (pbsRootProtocol roots).History :=
  pbsRootHistoryFintype roots

local instance securityInfoDecidableEq (who : Fin 2) :
    DecidableEq ((pbsRootFullInformation M roots).InfoState who) := Classical.decEq _

local instance securityChoiceFintype (who : Fin 2)
    (info : (pbsRootFullInformation M roots).InfoState who) :
    Fintype ((pbsRootFullInformation M roots).Choice who info) := by
  classical
  infer_instance

/-- Native child security is derived from the actual two-player recurrence.
There is no supplied regret certificate and no extra factor of two. -/
theorem pbsRootCFR_security (fallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (bound : Fin 2 → ℝ) (hbound0 : ∀ who, 0 ≤ bound who)
    (hbound : ∀ who history, |payoff who history| ≤ bound who)
    (fuel t : Nat) [NeZero t]
    (reference : Profile (pbsRootFullInformation M roots).behavioralSignature)
    (equilibrium : IsNash ((pbsRootFullInformation M roots).toBehavioralGameForm (fuel + 1))
      (euPreference (fun history who => pbsRootPayoff roots payoff who history)) reference)
    (unknown : Profile (pbsRootFullInformation M roots).behavioralSignature) (who : Fin 2) :
    ((pbsRootFullInformation M roots).runBehavioral reference (fuel + 1)).expect
        (pbsRootPayoff roots payoff who) - pbsRootCFRBound M roots bound fuel t ≤
      ((pbsRootFullInformation M roots).runBehavioral
        (Profile.update unknown who (pbsRootCFR M roots fallback payoff fuel t who))
        (fuel + 1)).expect (pbsRootPayoff roots payoff who) := by
  apply ownReachAverage_security_of_regret (pbsRootFullInformation M roots)
    (fullSignals_perfectRecall (pbsRootInformation (fullInformation M) roots).toInfoSignals)
    (cfrIterationLaw t)
    (fun n : Fin t => pbsRootCFRIterate M roots fallback payoff fuel n.val)
    (pbsRootFallback M roots fallback) (fuel + 1) (pbsRootPayoff roots payoff)
    (pbsRootPayoff_zeroSum roots payoff hzero)
    (fun player => cfrCumulativeBound (pbsRootFullInformation M roots)
      (fullObservationClock (pbsRootInformation (fullInformation M) roots))
      (fuel + 1) player (bound player) t / t) _ reference equilibrium unknown who
  intro player target
  rw [cfrIterationLaw_expect t (fun n =>
    ((pbsRootFullInformation M roots).runBehavioral
      (Profile.update (pbsRootCFRIterate M roots fallback payoff fuel n) player target)
      (fuel + 1)).expect (pbsRootPayoff roots payoff player) -
    ((pbsRootFullInformation M roots).runBehavioral
      (pbsRootCFRIterate M roots fallback payoff fuel n) (fuel + 1)).expect
      (pbsRootPayoff roots payoff player))]
  exact cfr_average_root_regret_le (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (fullSignals_perfectRecall (pbsRootInformation (fullInformation M) roots).toInfoSignals)
    (pbsRootFallback M roots fallback) (pbsRootPayoff roots payoff) (fuel + 1) player
    (hbound0 player)
    (pbsRootPayoff_abs_le roots payoff player (bound player) (hbound0 player) (hbound player))
    target (Nat.pos_of_ne_zero (NeZero.ne t))

end Native

/-- The same sharp security allowance holds in the original continuation game.
The supplied PBS is held fixed while the opponent ranges over all legal policies. -/
theorem pbsInformationCFR_security
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (bound : Fin 2 → ℝ) (hbound0 : ∀ who, 0 ≤ bound who)
    (hbound : ∀ who history, |payoff who history| ≤ bound who)
    (fuel t : Nat) [NeZero t]
    (reference : Profile (fullInformation M).behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm (fullInformation M) belief fuel)
      (euPreference (fun history who => payoff who history)) reference)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) :
    (belief.law.bind ((fullInformation M).runBehavioralFrom reference fuel)).expect
        (payoff who) - pbsRootCFRBound M belief.law bound fuel t ≤
      (belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFR M belief fallback payoff fuel t who))
        fuel)).expect (payoff who) := by
  have security := pbsRootCFR_security M belief.law fallback payoff hzero bound hbound0 hbound
    fuel t (pbsRootBehavioralFullProfile M belief.law reference)
    (pbsRootLiftProfile_isNash M belief payoff fuel reference equilibrium)
    (pbsRootBehavioralFullProfile M belief.law unknown) who
  simp only [pbsSamplingPayoff_expect M belief.law (observations.length - 1)
    (pbsRoot_publicBelief_depth M belief), pbsRootDecodeProfile_update,
    pbsRootDecodeProfile_lift] at security
  simpa only [pbsInformationCFR, pbsRootDecodeProfile] using security

/-- Retained private iteration play inherits the same allowance for every
finite partition covering the training horizon, with no segment-count penalty. -/
theorem pbsInformationCarriedRun_security
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (bound : Fin 2 → ℝ) (hbound0 : ∀ who, 0 ≤ bound who)
    (hbound : ∀ who history, |payoff who history| ≤ bound who)
    (fuel t : Nat) [NeZero t]
    (reference : Profile (fullInformation M).behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm (fullInformation M) belief fuel)
      (euPreference (fun history who => payoff who history)) reference)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (segments : List Nat) (cover : segments.sum = fuel) :
    (belief.law.bind ((fullInformation M).runBehavioralFrom reference fuel)).expect
        (payoff who) - pbsRootCFRBound M belief.law bound fuel t ≤
      (pbsInformationCarriedRun M belief fallback payoff fuel t unknown who segments).expect
        (payoff who) := by
  rw [pbsInformationCarriedRun_eq_average, cover]
  exact pbsInformationCFR_security M belief fallback payoff hzero bound hbound0 hbound
    fuel t reference equilibrium unknown who

/-- A computed finite iteration count meets any positive prescribed security
budget for the actual sampled execution. It is not a per-iterate guarantee. -/
theorem pbsInformationCarriedRun_budget_security
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (bound : Fin 2 → ℝ) (hbound0 : ∀ who, 0 ≤ bound who)
    (hbound : ∀ who history, |payoff who history| ≤ bound who)
    (fuel : Nat) (error : ℝ) (positive : 0 < error)
    (reference : Profile (fullInformation M).behavioralSignature)
    (equilibrium : IsNash (behavioralBeliefForm (fullInformation M) belief fuel)
      (euPreference (fun history who => payoff who history)) reference)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (segments : List Nat) (cover : segments.sum = fuel) :
    (belief.law.bind ((fullInformation M).runBehavioralFrom reference fuel)).expect
        (payoff who) - error ≤
      (pbsInformationCarriedRun M belief fallback payoff fuel
        (pbsInformationBudgetRounds M belief.law bound fuel error) unknown who segments).expect
        (payoff who) := by
  have security := pbsInformationCarriedRun_security M belief fallback payoff hzero
    bound hbound0 hbound fuel (pbsInformationBudgetRounds M belief.law bound fuel error)
    reference equilibrium unknown who segments cover
  exact (sub_le_sub_left
    (pbsInformationBudgetRounds_error M belief.law bound fuel error positive) _).trans security

end GameTheory.ReBeL
