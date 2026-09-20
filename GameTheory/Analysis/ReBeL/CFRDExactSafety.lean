/-
# Finite-iteration safety with constructed exact child continuations

The child oracle's two contracts are proved by construction. The outer solver
still has finite-T regret. The security statement covers a seed-blind unknown
opponent and actual carried execution retaining the selected iteration. It
is not a theorem about replacing children by independently re-solved policies.
-/

import GameTheory.Analysis.ReBeL.CFRDExactDriver
import GameTheory.Analysis.ReBeL.CFRDCarriedPlay

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]
variable [∀ who, DecidableEq ((fullInformation M).InfoState who)]

/-- Canonical full-game approximate Nash for the actual finite-T outer CFR-D
solver, with no caller-supplied oracle-accuracy or continuation-quality premise.
Each player's averaging seed is private and weighted by own reach. -/
theorem cfrDConstructedExactOracle_isNash
    (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (cut remaining : Nat) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ who history, |payoff who history| ≤ bound) (t : Nat) [NeZero t] :
    IsNash ((fullInformation M).toBehavioralGameForm (cut + remaining))
      (euPreferenceWithin
        (cfrDDepthMeanBudget (fullInformation M) (fullObservationClock M)
            fallback cut remaining bound 0 0 0 t +
          cfrDDepthMeanBudget (fullInformation M) (fullObservationClock M)
            fallback cut remaining bound 0 0 1 t)
        (fun history who => payoff who history))
      (cfrDDepthAveragedProfile (fullInformation M) (fullObservationClock M)
        fallback payoff cut remaining (cfrDConstructedExactOracle M fallback payoff cut remaining)
        t) :=
  cfrDDepthAveragedProfile_isNash (fullInformation M) (fullObservationClock M)
    (fullSignals_perfectRecall M.toInfoSignals) fallback payoff hzero cut remaining
    (cfrDConstructedExactOracle M fallback payoff cut remaining) bound 0 0 nonneg
    (le_refl _) (le_refl _) bounded
    (cfrDConstructedExactOracle_accurate M fallback payoff cut remaining)
    (cfrDConstructedExactOracle_leafOptimal M fallback payoff cut remaining) t

/-- Zero numerical and child error still leave an explicit finite-T term.
Only the comparison equilibrium naming the game value is supplied; all
child-game equilibria and the local contracts are constructed internally. -/
theorem cfrDConstructedExactOracle_carried_security
    (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (cut remaining : Nat) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (reference : Profile (fullInformation M).behavioralSignature)
    (equilibrium : IsNash ((fullInformation M).toBehavioralGameForm (cut + remaining))
      (euPreference (fun history who => payoff who history)) reference)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (t : Nat) [NeZero t] :
    ((fullInformation M).runBehavioral reference (cut + remaining)).expect (payoff who) -
        (cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
            fallback cut remaining bound 0 +
          cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
            fallback cut remaining bound 1) / Real.sqrt t ≤
      (privateCarriedContinue (fullInformation M) (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
          fallback payoff cut remaining
          (cfrDConstructedExactOracle M fallback payoff cut remaining) n.val)
        unknown who cut remaining).expect (payoff who) := by
  have security := cfrDDepth_carried_security (fullInformation M) (fullObservationClock M)
    (fullSignals_perfectRecall M.toInfoSignals) fallback payoff hzero cut remaining
    (cfrDConstructedExactOracle M fallback payoff cut remaining) bound 0 0 nonneg
    (le_refl _) (le_refl _) bounded
    (cfrDConstructedExactOracle_accurate M fallback payoff cut remaining)
    (cfrDConstructedExactOracle_leafOptimal M fallback payoff cut remaining)
    reference equilibrium unknown who t
  simpa only [mul_zero, zero_add, add_zero] using security

end GameTheory.ReBeL
