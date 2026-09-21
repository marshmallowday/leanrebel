/-
# Coupled depth-limited CFR-D with information-set child solvers

Every actual parent round computes its finite information-set CFR children
at the factual joint PBSs and completes the omitted counterfactual types.
Prediction error, child tolerance and outer finite-time regret remain separate.
This carried-policy guarantee is not independent recursive re-solving.
-/

import GameTheory.Analysis.ReBeL.CFRDInformationContinuation
import GameTheory.Analysis.ReBeL.CFRDNoisyDriver

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

/-- Supply the actual information-set continuation and its conditional values
with a visible local perturbation to the coupled parent recurrence. -/
def cfrDConstructedInformationOracle (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : CFRDPredictionNoise M) : CFRDValueOracle (fullInformation M) := fun n trunk =>
  let response := cfrDExactValueOracle (fullInformation M) (fullObservationClock M)
    (cfrDInformationFallback M fallback) payoff cut remaining (fun _ strategy =>
      cfrDInformationContinuation M strategy fallback cut remaining
        (fun h who => payoff who h) bound loss) n trunk
  { continuation := response.continuation
    prediction := fun who info => response.prediction who info + noise n trunk who info }

/-- Accuracy concerns the perturbed learner's actual sequence, not an unrelated
sequence of exact or previously unperturbed parent strategies. -/
theorem cfrDConstructedInformationOracle_accurate
    (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : CFRDPredictionNoise M) (error : ℝ)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error) :
    CFRDDepthAccurate (fullInformation M) (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut remaining
      (cfrDConstructedInformationOracle M fallback payoff cut remaining bound loss noise)
      error := by
  intro n who info _sampled
  let oracle := cfrDConstructedInformationOracle M fallback payoff cut remaining bound loss noise
  let trunk := cfrProfile (fullInformation M) (cfrDInformationFallback M fallback)
    (cfrDState (fullInformation M)
      (cfrDDepthTrunk (fullInformation M) (fullObservationClock M) cut)
      (cfrDInformationFallback M fallback)
      (cfrDDepthOracle (fullInformation M) (fullObservationClock M)
        (cfrDInformationFallback M fallback) payoff cut remaining oracle) n)
  let response := cfrDExactValueOracle (fullInformation M) (fullObservationClock M)
    (cfrDInformationFallback M fallback) payoff cut remaining (fun _ strategy =>
      cfrDInformationContinuation M strategy fallback cut remaining
        (fun h player => payoff player h) bound loss) n trunk
  have residual : |response.prediction who info + noise n trunk who info -
      response.prediction who info| ≤ error := by
    simpa only [add_sub_cancel_left] using noiseBound n trunk who info
  exact residual

/-- Every actual parent round derives its all-query child loss from finite
information-set solves and zero-own-reach completion, not a child certificate. -/
theorem cfrDConstructedInformationOracle_leafOptimal
    (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ who h, |payoff who h| ≤ bound) (noise : CFRDPredictionNoise M) :
    CFRDDepthLeafOptimal (fullInformation M) (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut remaining
      (cfrDConstructedInformationOracle M fallback payoff cut remaining bound loss noise)
      loss := by
  intro n who
  rw [cfrDDepthPlay_eq]
  apply cfrDDepthProfile_leafOptimal
  · exact cfrDInformationContinuation_referenceLaw M _ fallback cut remaining
      (fun h player => payoff player h) bound loss who
  · exact cfrDInformationContinuation_leafOptimal M _ fallback cut remaining
      (fun h player => payoff player h) zeroSum bound loss nonneg positive
      (fun h player => bounded player h) who

/-- Independent own-reach averages of the actual coupled information-set
backend satisfy the canonical full-game approximate Nash guarantee. -/
theorem cfrDConstructedInformationOracle_isNash
    (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (bound error loss : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ who h, |payoff who h| ≤ bound) (noise : CFRDPredictionNoise M)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (t : Nat) [NeZero t] :
    IsNash ((fullInformation M).toBehavioralGameForm (cut + remaining))
      (euPreferenceWithin
        (cfrDDepthMeanBudget (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut remaining bound error loss 0 t +
          cfrDDepthMeanBudget (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut remaining bound error loss 1 t)
        (fun h who => payoff who h))
      (cfrDDepthAveragedProfile (fullInformation M) (fullObservationClock M)
        (cfrDInformationFallback M fallback) payoff cut remaining
        (cfrDConstructedInformationOracle M fallback payoff cut remaining bound loss noise) t) :=
  cfrDDepthAveragedProfile_isNash (fullInformation M) (fullObservationClock M)
    (fullSignals_perfectRecall M.toInfoSignals) (cfrDInformationFallback M fallback)
    payoff zeroSum cut remaining
    (cfrDConstructedInformationOracle M fallback payoff cut remaining bound loss noise)
    bound error loss hb he hl.le bounded
    (cfrDConstructedInformationOracle_accurate M fallback payoff cut remaining bound loss noise
      error noiseBound)
    (cfrDConstructedInformationOracle_leafOptimal M fallback payoff zeroSum cut remaining
      bound loss hb hl bounded noise) t

/-- The private carried execution separates numerical, child and outer losses.
Only the comparison equilibrium names the game value; every child and its
counterfactual contract are constructed from the information-set recurrence. -/
theorem cfrDConstructedInformationOracle_carried_security
    (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (bound error loss : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ who h, |payoff who h| ≤ bound) (noise : CFRDPredictionNoise M)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (reference : Profile (fullInformation M).behavioralSignature)
    (equilibrium : IsNash ((fullInformation M).toBehavioralGameForm (cut + remaining))
      (euPreference (fun h who => payoff who h)) reference)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (t : Nat) [NeZero t] :
    ((fullInformation M).runBehavioral reference (cut + remaining)).expect (payoff who) -
      ((cfrDDepthErrorConstant (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut remaining 0 +
          cfrDDepthErrorConstant (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut remaining 1) * error +
        (cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut remaining bound 0 +
          cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut remaining bound 1) / Real.sqrt t +
        2 * loss) ≤
      (privateCarriedContinue (fullInformation M) (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
          (cfrDInformationFallback M fallback) payoff cut remaining
          (cfrDConstructedInformationOracle M fallback payoff cut remaining bound loss noise)
          n.val) unknown who cut remaining).expect (payoff who) :=
  cfrDDepth_carried_security (fullInformation M) (fullObservationClock M)
    (fullSignals_perfectRecall M.toInfoSignals) (cfrDInformationFallback M fallback)
    payoff zeroSum cut remaining
    (cfrDConstructedInformationOracle M fallback payoff cut remaining bound loss noise)
    bound error loss hb he hl.le bounded
    (cfrDConstructedInformationOracle_accurate M fallback payoff cut remaining bound loss noise
      error noiseBound)
    (cfrDConstructedInformationOracle_leafOptimal M fallback payoff zeroSum cut remaining
      bound loss hb hl bounded noise) reference equilibrium unknown who t

end GameTheory.ReBeL
