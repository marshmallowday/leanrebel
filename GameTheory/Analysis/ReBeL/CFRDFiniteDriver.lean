/-
# Depth-limited CFR-D with finite-budget child solves

Every actual outer iteration computes finite normal-form child responses
at its own PBSs and completes the off-path types. Numerical noise can change
the outer recurrence. Prediction error, positive child loss and outer finite
regret remain separate. This does not certify fresh independent re-solving
at later carried PBSs or identify this adaptive variant with child CFR.
-/

import GameTheory.Analysis.ReBeL.CFRDFiniteContinuation
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

/-- The coupled learner receives the finite constructed continuation and
its own conditional values, with a visible information-local numerical perturbation. -/
def cfrDConstructedFiniteOracle (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : CFRDPredictionNoise M) : CFRDValueOracle (fullInformation M) := fun n trunk =>
  let response := cfrDExactValueOracle (fullInformation M) (fullObservationClock M)
    fallback payoff cut remaining (fun _ strategy =>
      cfrDFiniteContinuation M strategy fallback cut remaining
        (fun h who => payoff who h) bound loss) n trunk
  { continuation := response.continuation
    prediction := fun who info => response.prediction who info + noise n trunk who info }

/-- Numerical accuracy holds for the perturbed recurrence itself, not for
an independently supplied or previously unperturbed sequence of strategies. -/
theorem cfrDConstructedFiniteOracle_accurate
    (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : CFRDPredictionNoise M) (error : ℝ)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error) :
    CFRDDepthAccurate (fullInformation M) (fullObservationClock M) fallback payoff cut remaining
      (cfrDConstructedFiniteOracle M fallback payoff cut remaining bound loss noise) error := by
  intro n who info _sampled
  let oracle := cfrDConstructedFiniteOracle M fallback payoff cut remaining bound loss noise
  let trunk := cfrProfile (fullInformation M) fallback
    (cfrDState (fullInformation M) (cfrDDepthTrunk (fullInformation M) (fullObservationClock M) cut)
      fallback (cfrDDepthOracle (fullInformation M) (fullObservationClock M) fallback payoff
        cut remaining oracle) n)
  let response := cfrDExactValueOracle (fullInformation M) (fullObservationClock M)
    fallback payoff cut remaining (fun _ strategy =>
      cfrDFiniteContinuation M strategy fallback cut remaining
        (fun h player => payoff player h) bound loss) n trunk
  have residual : |response.prediction who info + noise n trunk who info -
      response.prediction who info| ≤ error := by
    simpa only [add_sub_cancel_left] using noiseBound n trunk who info
  exact residual

/-- The finite child's all-query loss is derived at each actual outer round.
No child Nash, positive mass floor, budget or leaf-gain certificate is assumed. -/
theorem cfrDConstructedFiniteOracle_leafOptimal
    (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ who h, |payoff who h| ≤ bound) (noise : CFRDPredictionNoise M) :
    CFRDDepthLeafOptimal (fullInformation M) (fullObservationClock M) fallback payoff cut remaining
      (cfrDConstructedFiniteOracle M fallback payoff cut remaining bound loss noise) loss := by
  intro n who
  rw [cfrDDepthPlay_eq]
  apply cfrDDepthProfile_leafOptimal
  · exact cfrDFiniteContinuation_referenceLaw M _ fallback cut remaining
      (fun h player => payoff player h) bound loss who
  · exact cfrDFiniteContinuation_leafOptimal M _ fallback cut remaining
      (fun h player => payoff player h) zeroSum bound loss nonneg positive
      (fun h player => bounded player h) who

/-- Finite-budget children supply canonical full-game approximate Nash.
Independent own-reach averages, rather than a public shared iteration seed,
are used in the actual behavioral profile. -/
theorem cfrDConstructedFiniteOracle_isNash
    (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (bound error loss : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ who h, |payoff who h| ≤ bound) (noise : CFRDPredictionNoise M)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (t : Nat) [NeZero t] :
    IsNash ((fullInformation M).toBehavioralGameForm (cut + remaining))
      (euPreferenceWithin
        (cfrDDepthMeanBudget (fullInformation M) (fullObservationClock M)
            fallback cut remaining bound error loss 0 t +
          cfrDDepthMeanBudget (fullInformation M) (fullObservationClock M)
            fallback cut remaining bound error loss 1 t)
        (fun h who => payoff who h))
      (cfrDDepthAveragedProfile (fullInformation M) (fullObservationClock M)
        fallback payoff cut remaining
        (cfrDConstructedFiniteOracle M fallback payoff cut remaining bound loss noise) t) :=
  cfrDDepthAveragedProfile_isNash (fullInformation M) (fullObservationClock M)
    (fullSignals_perfectRecall M.toInfoSignals) fallback payoff zeroSum cut remaining
    (cfrDConstructedFiniteOracle M fallback payoff cut remaining bound loss noise)
    bound error loss hb he hl.le bounded
    (cfrDConstructedFiniteOracle_accurate M fallback payoff cut remaining bound loss noise
      error noiseBound)
    (cfrDConstructedFiniteOracle_leafOptimal M fallback payoff zeroSum cut remaining
      bound loss hb hl bounded noise) t

/-- The carried selected-policy execution has numerical, finite-child and
finite-outer losses explicitly separated. Only the comparison equilibrium
naming the game value is assumed; all child solves and local contracts are constructed. -/
theorem cfrDConstructedFiniteOracle_carried_security
    (fallback : Profile (fullInformation M).strategicSignature)
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
            fallback cut remaining 0 +
          cfrDDepthErrorConstant (fullInformation M) (fullObservationClock M)
            fallback cut remaining 1) * error +
        (cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
            fallback cut remaining bound 0 +
          cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
            fallback cut remaining bound 1) / Real.sqrt t + 2 * loss) ≤
      (privateCarriedContinue (fullInformation M) (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
          fallback payoff cut remaining
          (cfrDConstructedFiniteOracle M fallback payoff cut remaining bound loss noise) n.val)
        unknown who cut remaining).expect (payoff who) :=
  cfrDDepth_carried_security (fullInformation M) (fullObservationClock M)
    (fullSignals_perfectRecall M.toInfoSignals) fallback payoff zeroSum cut remaining
    (cfrDConstructedFiniteOracle M fallback payoff cut remaining bound loss noise)
    bound error loss hb he hl.le bounded
    (cfrDConstructedFiniteOracle_accurate M fallback payoff cut remaining bound loss noise
      error noiseBound)
    (cfrDConstructedFiniteOracle_leafOptimal M fallback payoff zeroSum cut remaining
      bound loss hb hl bounded noise) reference equilibrium unknown who t

end GameTheory.ReBeL
