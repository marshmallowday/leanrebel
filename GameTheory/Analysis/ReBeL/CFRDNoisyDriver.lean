/-
# Bounded numerical perturbations of constructed child continuations

Predictions change the coupled CFR-D recurrence and therefore its future
trunks. Every perturbed round reconstructs its child games at its OWN trunk;
no equality with the exact driver's learning trace is assumed. Uniformly
bounded information-local prediction noise gives the corrected error bound.
The child solve remains exact noncomputable Nash, not finite-T child CFR.
-/

import GameTheory.Analysis.ReBeL.CFRDExactSafety

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

section Oracle

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- The additive numerical error depends on the model query and own information,
not the realized hidden history or an unknown opponent's private strategy. -/
abbrev CFRDPredictionNoise := Nat → Profile (fullInformation M).behavioralSignature →
  (who : ι) → (fullInformation M).InfoState who → ℝ

variable [Fintype ι] [DecidableEq ι] [Fintype E.History]
variable [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]
variable [∀ who, DecidableEq ((fullInformation M).InfoState who)]

/-- Predictions are perturbed, but the response's exact child construction is
still recomputed from the current queried trunk. -/
def cfrDConstructedNoisyOracle (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) (noise : CFRDPredictionNoise M) :
    CFRDValueOracle (fullInformation M) := fun n trunk =>
  let response := cfrDConstructedExactOracle M fallback payoff cut remaining n trunk
  { continuation := response.continuation
    prediction := fun who info => response.prediction who info + noise n trunk who info }

/-- A numerical error bound holds on this oracle's actual learning sequence.
No old unperturbed sequence is substituted for its current profile. -/
theorem cfrDConstructedNoisyOracle_accurate
    (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat)
    (noise : CFRDPredictionNoise M) (error : ℝ)
    (bounded : ∀ n trunk who info, |noise n trunk who info| ≤ error) :
    CFRDDepthAccurate (fullInformation M) (fullObservationClock M) fallback payoff cut remaining
      (cfrDConstructedNoisyOracle M fallback payoff cut remaining noise) error := by
  intro n who info _sampled
  let oracle := cfrDConstructedNoisyOracle M fallback payoff cut remaining noise
  let trunk := cfrProfile (fullInformation M) fallback
    (cfrDState (fullInformation M) (cfrDDepthTrunk (fullInformation M) (fullObservationClock M) cut)
      fallback (cfrDDepthOracle (fullInformation M) (fullObservationClock M) fallback payoff
        cut remaining oracle) n)
  let response := cfrDConstructedExactOracle M fallback payoff cut remaining n trunk
  have residual : |response.prediction who info + noise n trunk who info -
      response.prediction who info| ≤ error := by
    simpa only [add_sub_cancel_left] using bounded n trunk who info
  exact residual

/-- Prediction noise may change every future trunk, but each new trunk still
receives a constructed zero-loss continuation. -/
theorem cfrDConstructedNoisyOracle_leafOptimal
    (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) (noise : CFRDPredictionNoise M) :
    CFRDDepthLeafOptimal (fullInformation M) (fullObservationClock M) fallback payoff cut remaining
      (cfrDConstructedNoisyOracle M fallback payoff cut remaining noise) 0 := by
  intro n who
  rw [cfrDDepthPlay_eq]
  apply cfrDDepthProfile_leafOptimal
  · exact cfrDExactContinuation_referenceLaw M _ fallback cut remaining
      (fun history player => payoff player history) who
  · exact cfrDExactContinuation_leafOptimal M _ fallback cut remaining
      (fun history player => payoff player history) who

end Oracle

section Security

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]
variable [∀ who, DecidableEq ((fullInformation M).InfoState who)]

/-- The actual perturbed solver has an additive numerical-error term and a
finite-iteration term independent of that error. No child-quality premise is
supplied. This does not certify an arbitrary network's error or recursive solve. -/
theorem cfrDConstructedNoisyOracle_carried_security
    (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (cut remaining : Nat) (noise : CFRDPredictionNoise M) (bound error : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (reference : Profile (fullInformation M).behavioralSignature)
    (equilibrium : IsNash ((fullInformation M).toBehavioralGameForm (cut + remaining))
      (euPreference (fun history who => payoff who history)) reference)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (t : Nat) [NeZero t] :
    ((fullInformation M).runBehavioral reference (cut + remaining)).expect (payoff who) -
        ((cfrDDepthErrorConstant (fullInformation M) (fullObservationClock M)
              fallback cut remaining 0 +
            cfrDDepthErrorConstant (fullInformation M) (fullObservationClock M)
              fallback cut remaining 1) * error +
          (cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
              fallback cut remaining bound 0 +
            cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
              fallback cut remaining bound 1) / Real.sqrt t) ≤
      (privateCarriedContinue (fullInformation M) (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
          fallback payoff cut remaining
          (cfrDConstructedNoisyOracle M fallback payoff cut remaining noise) n.val)
        unknown who cut remaining).expect (payoff who) := by
  have security := cfrDDepth_carried_security (fullInformation M) (fullObservationClock M)
    (fullSignals_perfectRecall M.toInfoSignals) fallback payoff hzero cut remaining
    (cfrDConstructedNoisyOracle M fallback payoff cut remaining noise) bound error 0 hb he
    (le_refl _) bounded
    (cfrDConstructedNoisyOracle_accurate M fallback payoff cut remaining noise error noiseBound)
    (cfrDConstructedNoisyOracle_leafOptimal M fallback payoff cut remaining noise)
    reference equilibrium unknown who t
  simpa only [mul_zero, add_zero] using security

end Security
end GameTheory.ReBeL
