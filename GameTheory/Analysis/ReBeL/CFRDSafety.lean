/-
# One-sided safety against an unknown opponent

Private iteration sampling is unilateral: the arbitrary opposing policy is
chosen outside the seed binder. The two-player saddle bound is derived from
the same learned sequence, and a canonical equilibrium only anchors the game
value. It is not a certificate supplied by the depth-limited oracle.
-/

import GameTheory.Analysis.ReBeL.CFRDNash
import GameTheory.Analysis.ReBeL.CFRDConstants

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*} [Fintype K]

/-- The cross-profile is independent of which unused coordinate was kept. -/
theorem twoPlayer_cross_profile (first second : Profile M.behavioralSignature) :
    Profile.update first 0 (second 0) = Profile.update second 1 (first 1) := by
  funext who
  fin_cases who <;> simp

/-- The stronger saddle bound retains the sum of the two actual regret
allowances. Merely deriving an epsilon-Nash predicate and doubling epsilon
would unnecessarily lose this coefficient. -/
theorem ownReachAverage_saddle_of_regret (hrecall : M.PerfectRecall)
    (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (fallback : (who : Fin 2) → M.Policy who) (horizon : Nat)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history)) (error : Fin 2 → ℝ)
    (regret : ∀ who (target : M.BehavioralPolicy who),
      seed.expect (fun k =>
        (M.runBehavioral (Profile.update (plays k) who target) horizon).expect (payoff who) -
          (M.runBehavioral (plays k) horizon).expect (payoff who)) ≤ error who)
    (row : M.BehavioralPolicy 0) (column : M.BehavioralPolicy 1) :
    (M.runBehavioral (Profile.update
        (ownReachAverageProfile M (fun _ => seed) plays fallback) 0 row) horizon).expect
        (payoff 0) -
      (M.runBehavioral (Profile.update
        (ownReachAverageProfile M (fun _ => seed) plays fallback) 1 column) horizon).expect
        (payoff 0) ≤ error 0 + error 1 := by
  have rows := deviation_against_average M hrecall (fun _ => seed) plays fallback 0 1
    (by decide) (by intro who; fin_cases who <;> simp) row horizon
  have columns := deviation_against_average M hrecall (fun _ => seed) plays fallback 1 0
    (by decide) (by intro who; fin_cases who <;> simp) column horizon
  rw [rows, columns, FinDist.expect_bind, FinDist.expect_bind]
  have hr := regret 0 row
  have hc := regret 1 column
  have hz (profile : Profile M.behavioralSignature) :
      (M.runBehavioral profile horizon).expect (payoff 1) =
        -(M.runBehavioral profile horizon).expect (payoff 0) :=
    hzero.expectedUtility_one _
  simp_rw [hz, neg_sub_neg] at hc
  rw [FinDist.expect_sub] at hr hc
  linarith

/-- A solver satisfying both players' regret bounds yields a one-sided
security guarantee against ANY fixed behavioral opponent, without a claim
that the actual unknown opponent follows the internal search model. -/
theorem ownReachAverage_security_of_regret (hrecall : M.PerfectRecall)
    (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (fallback : (who : Fin 2) → M.Policy who) (horizon : Nat)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history)) (error : Fin 2 → ℝ)
    (regret : ∀ who (target : M.BehavioralPolicy who),
      seed.expect (fun k =>
        (M.runBehavioral (Profile.update (plays k) who target) horizon).expect (payoff who) -
          (M.runBehavioral (plays k) horizon).expect (payoff who)) ≤ error who)
    (reference : Profile M.behavioralSignature)
    (equilibrium : IsNash (M.toBehavioralGameForm horizon)
      (euPreference (fun history who => payoff who history)) reference)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) :
    (M.runBehavioral reference horizon).expect (payoff who) - (error 0 + error 1) ≤
      (M.runBehavioral (Profile.update unknown who
        (ownReachAverageProfile M (fun _ => seed) plays fallback who)) horizon).expect
        (payoff who) := by
  let average := ownReachAverageProfile M (fun _ => seed) plays fallback
  have hz (profile : Profile M.behavioralSignature) :
      (M.runBehavioral profile horizon).expect (payoff 1) =
        -(M.runBehavioral profile horizon).expect (payoff 0) :=
    hzero.expectedUtility_one _
  rcases (by decide : ∀ player : Fin 2, player = 0 ∨ player = 1) who with rfl | rfl
  · have hs := ownReachAverage_saddle_of_regret M hrecall seed plays fallback horizon payoff
      hzero error regret (reference 0) (unknown 1)
    have he : (M.runBehavioral (Profile.update reference 1 (average 1)) horizon).expect
        (payoff 1) ≤ (M.runBehavioral reference horizon).expect (payoff 1) :=
      (isNash_iff (F := M.toBehavioralGameForm horizon)
        (weaklyPrefers := euPreference (fun history who => payoff who history))
        reference).mp equilibrium 1 (average 1)
    rw [hz, hz, ← twoPlayer_cross_profile M average reference] at he
    rw [twoPlayer_cross_profile M unknown average]
    dsimp only [average] at he ⊢
    linarith
  · have hs := ownReachAverage_saddle_of_regret M hrecall seed plays fallback horizon payoff
      hzero error regret (unknown 0) (reference 1)
    have he : (M.runBehavioral (Profile.update reference 0 (average 0)) horizon).expect
        (payoff 0) ≤ (M.runBehavioral reference horizon).expect (payoff 0) :=
      (isNash_iff (F := M.toBehavioralGameForm horizon)
        (weaklyPrefers := euPreference (fun history who => payoff who history))
        reference).mp equilibrium 0 (average 0)
    rw [twoPlayer_cross_profile M reference average] at he
    rw [hz, hz, ← twoPlayer_cross_profile M average unknown]
    dsimp only [average] at he ⊢
    linarith

/-- One private seed selects the focal player's complete legal policy. The
opponent is arbitrary but is not permitted to inspect the private seed. -/
def privateIterationLaw (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (horizon : Nat) : FinDist E.History :=
  seed.bind (fun k => M.runBehavioral (Profile.update unknown who (plays k who)) horizon)

/-- Private iteration play is realization-equivalent against arbitrary
opponents to own-reach averaging, not to pointwise arithmetic averaging. -/
theorem privateIterationLaw_eq_average (hrecall : M.PerfectRecall)
    (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (fallback : (who : Fin 2) → M.Policy who)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (horizon : Nat) :
    privateIterationLaw M seed plays unknown who horizon =
      M.runBehavioral (Profile.update unknown who
        (ownReachAverageProfile M (fun _ => seed) plays fallback who)) horizon :=
  (run_unilateral_average M hrecall (fun _ => seed) plays fallback unknown who horizon).symm

variable [Fintype E.History]
variable [∀ who info, Fintype (M.Choice who info)]
variable [∀ who, DecidableEq (M.InfoState who)]

/-- Corrected finite-time test-time safety for the actual depth-limited
solver. The reference equilibrium only names the game value. Neither training
convergence nor a final guarantee from the value oracle is a premise. -/
theorem cfrDDepth_private_security (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (cut remaining : Nat) (oracle : CFRDValueOracle M) (bound error loss : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 ≤ loss)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error)
    (optimal : CFRDDepthLeafOptimal M clock fallback payoff cut remaining oracle loss)
    (reference : Profile M.behavioralSignature)
    (equilibrium : IsNash (M.toBehavioralGameForm (cut + remaining))
      (euPreference (fun history who => payoff who history)) reference)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (t : Nat) [NeZero t] :
    (M.runBehavioral reference (cut + remaining)).expect (payoff who) -
      ((cfrDDepthErrorConstant M clock fallback cut remaining 0 +
          cfrDDepthErrorConstant M clock fallback cut remaining 1) * error +
        (cfrDDepthFiniteConstant M clock fallback cut remaining bound 0 +
          cfrDDepthFiniteConstant M clock fallback cut remaining bound 1) / Real.sqrt t +
        2 * loss) ≤
      (privateIterationLaw M (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val)
        unknown who (cut + remaining)).expect (payoff who) := by
  rw [privateIterationLaw_eq_average M hrecall _ _ fallback]
  have security := ownReachAverage_security_of_regret M hrecall (cfrIterationLaw t)
    (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val)
    fallback (cut + remaining) payoff hzero
    (fun player => cfrDDepthErrorConstant M clock fallback cut remaining player * error +
      cfrDDepthFiniteConstant M clock fallback cut remaining bound player / Real.sqrt t + loss)
    (fun player target => cfrDDepth_mean_regret_le_constants M clock hrecall fallback payoff
      cut remaining oracle bound error loss hb he hl bounded accurate optimal player target t)
    reference equilibrium unknown who
  convert security using 1
  ring

end GameTheory.ReBeL
