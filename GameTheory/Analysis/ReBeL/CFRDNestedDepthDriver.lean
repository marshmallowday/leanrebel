/-
# Actual coupled parent recurrence with noisy depth-limited children

Each parent iteration queries its own factual joint PBSs and runs the budgeted
child depth solver there. Child predictions and the parent's prediction error
are separate inputs. The derived all-query child contract drives the existing
canonical CFR-D recurrence and its finite-time, all-deviation guarantee.
This is a constructed nesting step; arbitrary-depth recursion remains separate.
-/

import GameTheory.Analysis.ReBeL.CFRDDepthChild
import GameTheory.Analysis.ReBeL.CFRDInformationDriver

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

/-- Feed the constructed nested continuation into each actual parent's update.
Its conditional values and its distinct outer perturbation use that same trunk. -/
def cfrDNestedDepthOracle (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut childCut childRemaining : Nat) (bound loss : ℝ)
    (childNoise : PBSDepthNoiseFamily M) (noise : CFRDPredictionNoise M) :
    CFRDValueOracle (fullInformation M) := fun n trunk =>
  let response := cfrDExactValueOracle (fullInformation M) (fullObservationClock M)
    (cfrDInformationFallback M fallback) payoff cut (childCut + childRemaining)
    (fun _ strategy => cfrDDepthChildContinuation M strategy fallback cut
      childCut childRemaining (fun h who => payoff who h) bound loss childNoise) n trunk
  { continuation := response.continuation
    prediction := fun who info => response.prediction who info + noise n trunk who info }

/-- Parent prediction accuracy holds on its own coupled learning trace.
It is not borrowed from a separately trained or unperturbed parent sequence. -/
theorem cfrDNestedDepthOracle_accurate (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut childCut childRemaining : Nat) (bound loss : ℝ)
    (childNoise : PBSDepthNoiseFamily M) (noise : CFRDPredictionNoise M) (error : ℝ)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error) :
    CFRDDepthAccurate (fullInformation M) (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut (childCut + childRemaining)
      (cfrDNestedDepthOracle M fallback payoff cut childCut childRemaining
        bound loss childNoise noise) error := by
  intro n who info _sampled
  let oracle := cfrDNestedDepthOracle M fallback payoff cut childCut childRemaining
    bound loss childNoise noise
  let trunk := cfrProfile (fullInformation M) (cfrDInformationFallback M fallback)
    (cfrDState (fullInformation M)
      (cfrDDepthTrunk (fullInformation M) (fullObservationClock M) cut)
      (cfrDInformationFallback M fallback)
      (cfrDDepthOracle (fullInformation M) (fullObservationClock M)
        (cfrDInformationFallback M fallback) payoff cut (childCut + childRemaining) oracle) n)
  let response := cfrDExactValueOracle (fullInformation M) (fullObservationClock M)
    (cfrDInformationFallback M fallback) payoff cut (childCut + childRemaining)
    (fun _ strategy => cfrDDepthChildContinuation M strategy fallback cut
      childCut childRemaining (fun h player => payoff player h) bound loss childNoise) n trunk
  have residual : |response.prediction who info + noise n trunk who info -
      response.prediction who info| ≤ error := by
    simpa only [add_sub_cancel_left] using noiseBound n trunk who info
  exact residual

/-- Every actual iteration derives its counterfactual child loss from the
budgeted noisy child solve and zero-own-reach completion, not a supplied optimum. -/
theorem cfrDNestedDepthOracle_leafOptimal (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut childCut childRemaining : Nat)
    (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ who h, |payoff who h| ≤ bound) (childNoise : PBSDepthNoiseFamily M)
    (childBound : PBSDepthChildNoiseBound M fallback childCut childRemaining loss childNoise)
    (noise : CFRDPredictionNoise M) :
    CFRDDepthLeafOptimal (fullInformation M) (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut (childCut + childRemaining)
      (cfrDNestedDepthOracle M fallback payoff cut childCut childRemaining
        bound loss childNoise noise) loss := by
  intro n who
  rw [cfrDDepthPlay_eq]
  apply cfrDDepthProfile_leafOptimal
  · exact cfrDDepthChildContinuation_referenceLaw M _ fallback cut childCut childRemaining
      (fun h player => payoff player h) bound loss childNoise who
  · exact cfrDDepthChildContinuation_leafOptimal M _ fallback cut childCut childRemaining
      (fun h player => payoff player h) zeroSum bound loss nonneg positive
      (fun h player => bounded player h) childNoise childBound who

/-- The actual nested recurrence satisfies canonical approximate Nash against
all behavioral deviations. The outer count stays finite and is not sent to infinity. -/
theorem cfrDNestedDepthOracle_isNash (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut childCut childRemaining : Nat)
    (bound error loss : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ who h, |payoff who h| ≤ bound) (childNoise : PBSDepthNoiseFamily M)
    (childBound : PBSDepthChildNoiseBound M fallback childCut childRemaining loss childNoise)
    (noise : CFRDPredictionNoise M)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (t : Nat) [NeZero t] :
    IsNash ((fullInformation M).toBehavioralGameForm (cut + (childCut + childRemaining)))
      (euPreferenceWithin
        (cfrDDepthMeanBudget (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut (childCut + childRemaining)
            bound error loss 0 t +
          cfrDDepthMeanBudget (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut (childCut + childRemaining)
            bound error loss 1 t)
        (fun h who => payoff who h))
      (cfrDDepthAveragedProfile (fullInformation M) (fullObservationClock M)
        (cfrDInformationFallback M fallback) payoff cut (childCut + childRemaining)
        (cfrDNestedDepthOracle M fallback payoff cut childCut childRemaining
          bound loss childNoise noise) t) :=
  cfrDDepthAveragedProfile_isNash (fullInformation M) (fullObservationClock M)
    (fullSignals_perfectRecall M.toInfoSignals) (cfrDInformationFallback M fallback)
    payoff zeroSum cut (childCut + childRemaining)
    (cfrDNestedDepthOracle M fallback payoff cut childCut childRemaining
      bound loss childNoise noise) bound error loss hb he hl.le bounded
    (cfrDNestedDepthOracle_accurate M fallback payoff cut childCut childRemaining
      bound loss childNoise noise error noiseBound)
    (cfrDNestedDepthOracle_leafOptimal M fallback payoff zeroSum cut childCut childRemaining
      bound loss hb hl bounded childNoise childBound noise) t

/-- Private carried execution has the corrected additive finite-T security
bound. The opponent cannot read the sampled iteration. Both noise layers remain. -/
theorem cfrDNestedDepthOracle_carried_security (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut childCut childRemaining : Nat)
    (bound error loss : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ who h, |payoff who h| ≤ bound) (childNoise : PBSDepthNoiseFamily M)
    (childBound : PBSDepthChildNoiseBound M fallback childCut childRemaining loss childNoise)
    (noise : CFRDPredictionNoise M)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (reference : Profile (fullInformation M).behavioralSignature)
    (equilibrium : IsNash
      ((fullInformation M).toBehavioralGameForm (cut + (childCut + childRemaining)))
      (euPreference (fun h who => payoff who h)) reference)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (t : Nat) [NeZero t] :
    ((fullInformation M).runBehavioral reference (cut + (childCut + childRemaining))).expect
      (payoff who) -
      ((cfrDDepthErrorConstant (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut (childCut + childRemaining) 0 +
          cfrDDepthErrorConstant (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut (childCut + childRemaining) 1) * error +
        (cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut (childCut + childRemaining) bound 0 +
          cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut (childCut + childRemaining) bound 1) /
          Real.sqrt t + 2 * loss) ≤
    (privateCarriedContinue (fullInformation M) (cfrIterationLaw t)
      (fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
        (cfrDInformationFallback M fallback) payoff cut (childCut + childRemaining)
        (cfrDNestedDepthOracle M fallback payoff cut childCut childRemaining
          bound loss childNoise noise) n.val)
      unknown who cut (childCut + childRemaining)).expect (payoff who) :=
  cfrDDepth_carried_security (fullInformation M) (fullObservationClock M)
    (fullSignals_perfectRecall M.toInfoSignals) (cfrDInformationFallback M fallback)
    payoff zeroSum cut (childCut + childRemaining)
    (cfrDNestedDepthOracle M fallback payoff cut childCut childRemaining
      bound loss childNoise noise) bound error loss hb he hl.le bounded
    (cfrDNestedDepthOracle_accurate M fallback payoff cut childCut childRemaining
      bound loss childNoise noise error noiseBound)
    (cfrDNestedDepthOracle_leafOptimal M fallback payoff zeroSum cut childCut childRemaining
      bound loss hb hl bounded childNoise childBound noise) reference equilibrium unknown who t

end GameTheory.ReBeL
