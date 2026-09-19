/-
# Canonical Nash guarantee for the constructed depth-limited solver

The output uses separate private own-reach averages, not one shared joint
iteration seed and not arithmetic averaging at every information state.
Local oracle contracts are passed through the actual recurrence and root
proof, then through the existing all-deviations realization theorem.
-/

import GameTheory.Analysis.ReBeL.CFRDRootRegret

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History]
variable [∀ who info, Fintype (M.Choice who info)]
variable [∀ who, DecidableEq (M.InfoState who)]

/-- Completed-round output of the actual coupled depth-limited recurrence. -/
def cfrDDepthAveragedProfile (clock : ObservationClock M)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (oracle : CFRDValueOracle M) (t : Nat) [NeZero t] :
    Profile M.behavioralSignature :=
  ownReachAverageProfile M (fun _ => cfrIterationLaw t)
    (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val) fallback

/-- Full-game canonical epsilon-Nash for a finite-time, actual depth-limited
solver. Every behavioral deviation is covered. The assumptions are structural
game properties, numerical payoff bounds, and LOCAL continuation/value contracts. -/
theorem cfrDDepthAveragedProfile_isNash (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (cut remaining : Nat) (oracle : CFRDValueOracle M) (bound error loss : ℝ)
    (hbound : 0 ≤ bound) (herror : 0 ≤ error) (hloss : 0 ≤ loss)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error)
    (optimal : CFRDDepthLeafOptimal M clock fallback payoff cut remaining oracle loss)
    (t : Nat) [NeZero t] :
    IsNash (M.toBehavioralGameForm (cut + remaining))
      (euPreferenceWithin
        (cfrDDepthMeanBudget M clock fallback cut remaining bound error loss 0 t +
          cfrDDepthMeanBudget M clock fallback cut remaining bound error loss 1 t)
        (fun history who => payoff who history))
      (cfrDDepthAveragedProfile M clock fallback payoff cut remaining oracle t) := by
  apply ownReachAverage_isNash_of_regret M hrecall (cfrIterationLaw t)
    (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val)
    fallback (cut + remaining) payoff hzero
    (fun who => cfrDDepthMeanBudget M clock fallback cut remaining bound error loss who t)
  intro who target
  exact cfrDDepth_mean_regret_le M clock hrecall fallback payoff cut remaining oracle
    bound error loss hbound herror hloss bounded accurate optimal who target t

/-- At full search depth the reference oracle needs no continuation optimality
assumption. Zero value error still leaves the finite-time matching allowance. -/
theorem cfrDDepth_fullSearch_isNash (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (cut : Nat) (bound : ℝ) (hbound : 0 ≤ bound)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (continuation : Nat → Profile M.behavioralSignature → Profile M.behavioralSignature)
    (t : Nat) [NeZero t] :
    IsNash (M.toBehavioralGameForm (cut + 0))
      (euPreferenceWithin
        (cfrDDepthMeanBudget M clock fallback cut 0 bound 0 0 0 t +
          cfrDDepthMeanBudget M clock fallback cut 0 bound 0 0 1 t)
        (fun history who => payoff who history))
      (cfrDDepthAveragedProfile M clock fallback payoff cut 0
        (cfrDExactValueOracle M clock fallback payoff cut 0 continuation) t) := by
  apply cfrDDepthAveragedProfile_isNash M clock hrecall fallback payoff hzero cut 0 _ bound 0 0
    hbound (le_refl _) (le_refl _) bounded
    (cfrDExactValueOracle_accurate M clock fallback payoff cut 0 continuation)
  intro n who
  exact cfrDLeafOptimal_zero_remaining M _ fallback who (payoff who) cut

end GameTheory.ReBeL
