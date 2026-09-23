/-
# Fresh finite information-set re-solving with an explicit value-drift term

The new child tolerance is independent of the parent's child tolerance.
Each retained parent model recomputes all public child games, including its
zero-own-reach completion. A fresh private finite-plan draw realizes that NEW
averaged solution on every legal history. This is not a draw of the old family,
or a claim that an actual CFR iterate is optimal or valid off its model support.
The source's multi-level error-rate theorem remains a separate obligation.
-/

import GameTheory.Analysis.ReBeL.CFRDFreshValueDrift
import GameTheory.Analysis.ReBeL.CFRDInformationSampledDriver
import GameTheory.Analysis.ReBeL.CFRDEnvelopeSafety

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

section Construction

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]
variable {K : Type*}

/-- Recompute the completed information-set CFR child at each retained parent
model, using the new positive tolerance rather than retaining its old solution. -/
def cfrDFreshInformationProfiles (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (plays : K → Profile (fullInformation M).behavioralSignature) :
    K → Profile (fullInformation M).behavioralSignature := fun n =>
  cfrDInformationContinuation M (plays n) fallback cut remaining
    (fun h who => payoff who h) bound loss

/-- The public resolver independently draws a legal finite plan of the NEW
computed child average. Neither actual hidden history nor the unknown opposing
policy is used to solve the child. Absent model posteriors are not fabricated. -/
def cfrDFreshInformationResolver (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (plays : K → Profile (fullInformation M).behavioralSignature) :
    CarriedPublicResolver (fullInformation M) K :=
  cfrDCoherentResolver (fullInformation M) (cfrDInformationFallback M fallback)
    (cfrDFreshInformationProfiles M fallback payoff cut remaining bound loss plays)

/-- New solving and predrawing realize the new averaged policy on ANY carried
state. No support domination, posterior equality or per-iterate guarantee is input. -/
theorem cfrDFreshInformationResolver_tail (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (state : PrivateIterationState (fullInformation M) K) :
    carriedResolvedTail (fullInformation M)
        (cfrDFreshInformationResolver M fallback payoff cut remaining bound loss plays)
        unknown who remaining state =
      (fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (cfrDFreshInformationProfiles M fallback payoff cut remaining bound loss plays
            state.iteration who)) remaining state.history :=
  cfrDCoherentResolver_tail (fullInformation M) (fullSignals_perfectRecall M.toInfoSignals)
    (cfrDInformationFallback M fallback)
    (cfrDFreshInformationProfiles M fallback payoff cut remaining bound loss plays)
    unknown who remaining state

/-- A stopped state bypasses the fresh solve/draw branch, also with no model PBS. -/
theorem cfrDFreshInformationResolver_stopped (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (state : PrivateIterationState (fullInformation M) K)
    (stopped : cfrDCutLive remaining state.history ≠ true) :
    carriedResolvedTail (fullInformation M)
        (cfrDFreshInformationResolver M fallback payoff cut remaining bound loss plays)
        unknown who remaining state = FinDist.pure state.history := by
  exact if_neg stopped

variable [Fintype K] [Nonempty K]

/-- The actual new-minus-old conditional model drift, uniformly over the retained
finite parent family. This abstract real-valued expression is not a numeric backend. -/
def cfrDFreshInformationDrift (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (plays : K → Profile (fullInformation M).behavioralSignature) (opponent : Fin 2) : ℝ :=
  cfrDFreshUniformDrift (fullInformation M) plays
    (cfrDFreshInformationProfiles M fallback payoff cut remaining bound loss plays)
    (cfrDInformationFallback M fallback) opponent (payoff opponent) cut remaining

/-- The model-comparison term is always a nonnegative allowance. -/
theorem cfrDFreshInformationDrift_nonneg (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (plays : K → Profile (fullInformation M).behavioralSignature) (opponent : Fin 2) :
    0 ≤ cfrDFreshInformationDrift M fallback payoff cut remaining bound loss plays opponent :=
  cfrDFreshUniformDrift_nonneg (fullInformation M) plays _
    (cfrDInformationFallback M fallback) opponent (payoff opponent) cut remaining

/-- All strategic premises of the fresh-family envelope are discharged by the
actual finite information-set child solver and its off-path completion. No caller
supplies an envelope, child Nash, counterfactual quality, support or value certificate. -/
theorem cfrDFreshInformationResolver_envelope (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h who => payoff who h))
    (cut remaining : Nat) (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ who h, |payoff who h| ≤ bound)
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who opponent : Fin 2)
    (different : opponent ≠ who) :
    CFRDResolverEnvelope (fullInformation M) plays
      (cfrDFreshInformationResolver M fallback payoff cut remaining bound loss plays)
      (cfrDInformationFallback M fallback) unknown who opponent cut remaining (payoff opponent)
      (loss + cfrDFreshInformationDrift M fallback payoff cut remaining bound loss
        plays opponent) :=
  cfrDFreshCoherentResolver_envelope (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals) plays
    (cfrDFreshInformationProfiles M fallback payoff cut remaining bound loss plays)
    (cfrDInformationFallback M fallback) unknown who opponent different cut remaining
    (payoff opponent) loss
    (fun n => cfrDInformationContinuation_referenceLaw M (plays n) fallback cut remaining
      (fun h player => payoff player h) bound loss opponent)
    (fun n => cfrDInformationContinuation_leafOptimal M (plays n) fallback cut remaining
      (fun h player => payoff player h) zeroSum bound loss nonneg positive
      (fun h player => bounded player h) opponent)

end Construction

section Security

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]
variable [∀ who, DecidableEq ((fullInformation M).InfoState who)]

/-- Fresh independent child solving for the actual noisy sampled-value parent.
Prediction error, finite outer T, old/new child tolerances and measured model
drift are all explicit. This is one fresh public-cut solve, not the paper's
unrestricted multi-level recursion or a vanishing drift-rate theorem. -/
theorem cfrDFreshInformation_security (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h who => payoff who h))
    (cut remaining : Nat) (bound error oldLoss newLoss : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (ho : 0 < oldLoss) (hn : 0 < newLoss)
    (bounded : ∀ who h, |payoff who h| ≤ bound) (noise : CFRDPredictionNoise M)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (reference : Profile (fullInformation M).behavioralSignature)
    (equilibrium : IsNash ((fullInformation M).toBehavioralGameForm (cut + remaining))
      (euPreference (fun h who => payoff who h)) reference)
    (unknown : Profile (fullInformation M).behavioralSignature) (who opponent : Fin 2)
    (different : opponent ≠ who) (t : Nat) [NeZero t] :
    let plays := fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut remaining
      (cfrDConstructedSampledInformationOracle M fallback payoff cut remaining bound oldLoss noise)
      n.val
    ((fullInformation M).runBehavioral reference (cut + remaining)).expect (payoff who) -
      ((cfrDDepthErrorConstant (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut remaining who +
          cfrDDepthErrorConstant (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut remaining opponent) * error +
        (cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut remaining bound who +
          cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
            (cfrDInformationFallback M fallback) cut remaining bound opponent) / Real.sqrt t +
        oldLoss + newLoss +
        cfrDFreshInformationDrift M fallback payoff cut remaining bound newLoss plays opponent) ≤
      (privateCarriedResolve (fullInformation M) (cfrIterationLaw t) plays
        (cfrDFreshInformationResolver M fallback payoff cut remaining bound newLoss plays)
        unknown who cut remaining).expect (payoff who) := by
  dsimp only
  let oracle := cfrDConstructedSampledInformationOracle M fallback payoff cut remaining
    bound oldLoss noise
  let plays := fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
    (cfrDInformationFallback M fallback) payoff cut remaining oracle n.val
  have accurate : CFRDDepthAccurate (fullInformation M) (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut remaining oracle error := by
    dsimp only [oracle]
    rw [cfrDConstructedSampledInformationOracle_eq]
    exact cfrDConstructedInformationOracle_accurate M fallback payoff cut remaining
      bound oldLoss noise error noiseBound
  have optimal : CFRDDepthLeafOptimal (fullInformation M) (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut remaining oracle oldLoss := by
    dsimp only [oracle]
    rw [cfrDConstructedSampledInformationOracle_eq]
    exact cfrDConstructedInformationOracle_leafOptimal M fallback payoff zeroSum cut remaining
      bound oldLoss hb ho bounded noise
  have envelope := cfrDFreshInformationResolver_envelope M fallback payoff zeroSum cut remaining
    bound newLoss hb hn bounded plays unknown who opponent different
  have security := cfrDDepth_resolve_envelope_security (fullInformation M)
    (fullObservationClock M) (fullSignals_perfectRecall M.toInfoSignals)
    (cfrDInformationFallback M fallback) payoff zeroSum cut remaining oracle bound error oldLoss
    (newLoss + cfrDFreshInformationDrift M fallback payoff cut remaining bound newLoss plays
      opponent) hb he ho.le
    (add_nonneg hn.le (cfrDFreshInformationDrift_nonneg M fallback payoff cut remaining
      bound newLoss plays opponent)) bounded accurate optimal reference equilibrium unknown
    who opponent different t
    (cfrDFreshInformationResolver M fallback payoff cut remaining bound newLoss plays) envelope
  simpa only [plays, oracle, add_assoc] using security

end Security
end GameTheory.ReBeL
