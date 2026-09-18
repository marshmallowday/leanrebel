/-
# Averaging preserves unilateral deviations

A player's own-reach average may replace that player's law against arbitrary
fixed opponents. With two players this turns each deviation against the
averaged opponent into the mean of the original unilateral deviations.
-/

import GameTheory.Analysis.ReBeL.IndependentRealization

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- A player's own-reach function depends only on that player's complete
policy, not on the arbitrary opponents stored in the surrounding profile. -/
theorem ownReach_eq_of_policy_eq (first second : Profile M.behavioralSignature)
    (who : ι) (hpolicy : first who = second who)
    {state : E.State} (trace : E.Trace state) :
    M.playerReachProbability first who trace = M.playerReachProbability second who trace := by
  apply ownReach_eq_of_agree_before M _ _ who trace.length
  · intro history _ _ _
    exact congrFun hpolicy (M.infoOf who history.trace)
  · exact le_rfl

variable [Fintype ι] [DecidableEq ι]

/-- The root probability of a unilateral replacement factors into fixed
opponent/chance terms and the replacing player's own reach. -/
theorem unilateral_probability_factorization
    (base : Profile M.behavioralSignature) (who : ι) (replacement : M.BehavioralPolicy who)
    (horizon : ℕ) (history : E.History) :
    (M.runBehavioral (Profile.update base who replacement) horizon).prob history =
      (outcomeChanceWeight horizon history *
        ∏ other ∈ Finset.univ.erase who, M.playerReachProbability base other history.trace) *
        M.playerReachProbability (Profile.update base who replacement) who history.trace := by
  classical
  rw [run_probability_factorization M,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ who)]
  have hopponents :
      (∏ other ∈ Finset.univ.erase who,
        M.playerReachProbability (Profile.update base who replacement) other history.trace) =
      ∏ other ∈ Finset.univ.erase who, M.playerReachProbability base other history.trace := by
    apply Finset.prod_congr rfl
    intro other hother
    exact ownReach_eq_of_policy_eq M _ base other
      (Profile.update_of_ne _ _ (Finset.mem_erase.mp hother).1) history.trace
  rw [hopponents]
  ring

variable {K : Type*} [Fintype K]

/-- Replacing a single player's law by its reach-weighted average has exactly
the mean outcome law against any fixed opponents. This is a unilateral, not
merely on-policy, realization statement. -/
theorem run_unilateral_average (hrecall : M.PerfectRecall)
    (seeds : ι → FinDist K) (plays : K → Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who)
    (base : Profile M.behavioralSignature) (who : ι) (horizon : ℕ) :
    M.runBehavioral
        (Profile.update base who (ownReachAverageProfile M seeds plays fallback who)) horizon =
      (seeds who).bind (fun k =>
        M.runBehavioral (Profile.update base who (plays k who)) horizon) := by
  apply FinDist.ext_of_prob
  intro history
  rw [unilateral_probability_factorization M, FinDist.prob_bind]
  simp_rw [unilateral_probability_factorization M]
  have havg := ownReach_eq_of_policy_eq M
    (Profile.update base who (ownReachAverageProfile M seeds plays fallback who))
    (ownReachAverageProfile M seeds plays fallback) who
    (Profile.update_same _ _ _) history.trace
  rw [havg, ownReachAverage_playerReach M hrecall]
  have hselected (k : K) := ownReach_eq_of_policy_eq M
    (Profile.update base who (plays k who)) (plays k) who
    (Profile.update_same _ _ _) history.trace
  simp_rw [hselected]
  exact (FinDist.expect_smul _ _ _).symm

/-- In a two-player carrier, a deviation against the averaged opponent has
exactly the mean original deviation law. The carrier premise is structural;
no strategic preservation or regret result is assumed. -/
theorem deviation_against_average (hrecall : M.PerfectRecall)
    (seeds : ι → FinDist K) (plays : K → Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who)
    (who other : ι) (hne : other ≠ who)
    (hpair : ∀ player, player = who ∨ player = other)
    (replacement : M.BehavioralPolicy who) (horizon : ℕ) :
    M.runBehavioral
        (Profile.update (ownReachAverageProfile M seeds plays fallback) who replacement)
        horizon =
      (seeds other).bind (fun k =>
        M.runBehavioral (Profile.update (plays k) who replacement) horizon) := by
  let average := ownReachAverageProfile M seeds plays fallback
  let base := Profile.update average who replacement
  have hfix : Profile.update base other (average other) = base := by
    have hsame : average other = base other := (Profile.update_of_ne _ _ hne).symm
    rw [hsame, Profile.update_eq_self]
  have hswap (k : K) :
      Profile.update base other (plays k other) = Profile.update (plays k) who replacement := by
    funext player
    rcases hpair player with hequal | hequal
    · subst player
      simp [base, hne.symm]
    · subst player
      simp [base, hne]
  have h := run_unilateral_average M hrecall seeds plays fallback base other horizon
  rw [hfix] at h
  simpa only [hswap] using h

end GameTheory.ReBeL
