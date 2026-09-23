/-
# Completed sampled values in the actual noisy parent recurrence

Supported live queries use the expectation of the actual retained child draw,
including computed zero-factual-reach completion. Unsupported vector entries
retain the reference convention; no posterior or sampling claim is made there.
The resulting oracle, and hence its entire coupled state sequence, agrees with
the constructed information-set parent with the SAME prediction perturbation.
This is not a single-draw concentration bound or recursive re-solving safety.
-/

import GameTheory.Analysis.ReBeL.CFRDInformationQuerySampling
import GameTheory.Analysis.ReBeL.CFRDInformationDriver

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

section Clamp

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι]
variable [∀ who info, Fintype (M.Choice who info)]

/-- Restoring the trunk preserves conditional values on supported LIVE cut
fibers. The support premise rules out early terminal and fallback histories. -/
theorem cfrDDepthProfile_live_value (clock : ObservationClock M)
    (trunk continuation : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι) (payoff : E.History → ℝ)
    (cut remaining : Nat) (info : M.InfoState who)
    (sampled : (info, true) ∈ ((unilateralReferenceLaw M trunk fallback who cut).map
      (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h))).support) :
    conditionalOracleValue (unilateralReferenceLaw M
        (cfrDDepthProfile M clock cut trunk continuation) fallback who cut)
      (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h))
      (fun h => (M.runBehavioralFrom
        (cfrDDepthProfile M clock cut trunk continuation) remaining h).expect payoff) (info, true) =
    conditionalOracleValue (unilateralReferenceLaw M trunk fallback who cut)
      (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h))
      (fun h => (M.runBehavioralFrom continuation remaining h).expect payoff) (info, true) := by
  rw [cfrDDepthProfile_referenceLaw]
  unfold conditionalOracleValue
  apply FinDist.expect_congr
  intro history reached
  have original := cfrD_conditional_support_source _ _ _ sampled history reached
  have live : cfrDCutLive remaining history = true := congrArg Prod.snd
    (conditionalOracle_support _ _ _ sampled history reached)
  have nonterminal : ¬ E.terminal history.state :=
    (show remaining ≠ 0 ∧ ¬ E.terminal history.state from by
      simpa only [cfrDCutLive, decide_eq_true_eq] using live).2
  have atCut : history.trace.length = cut := by
    rcases M.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
        (Profile.update trunk who (uniformLegalPolicy M who (fallback who)))
        cut E.initHistory history original with stopped | depth
    · exact (nonterminal stopped).elim
    · simpa only [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length,
        Nat.zero_add] using depth
  rw [cfrDDepthProfile_continuation_atCut M clock trunk continuation cut remaining history atCut]

end Clamp

section Parent

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]

/-- The completed child sampler computes the same live prediction consumed by
the noisy parent. This is an expectation identity, not per-iterate optimality. -/
theorem cfrDInformationQuerySample_prediction
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : CFRDPredictionNoise M) (n : Nat)
    (who : Fin 2) (info : (fullInformation M).InfoState who)
    (sampled : CFRDInformationQuerySampled M trunk fallback cut remaining who info) :
    (cfrDInformationQuerySample M trunk fallback cut remaining
        (fun h player => payoff player h) bound loss who info
        (cfrDInformationContinuation M trunk fallback cut remaining
          (fun h player => payoff player h) bound loss) remaining).expect (payoff who) +
        noise n trunk who info =
      (cfrDConstructedInformationOracle M fallback payoff cut remaining bound loss noise
        n trunk).prediction who info := by
  unfold cfrDConstructedInformationOracle
  dsimp only [cfrDExactValueOracle]
  apply congrArg (fun value : ℝ => value + noise n trunk who info)
  rw [cfrDInformationQuerySample_law M trunk fallback cut remaining
    (fun h player => payoff player h) bound loss who info sampled,
    Profile.update_eq_self, FinDist.expect_bind]
  rw [cfrDDepthProfile_live_value (fullInformation M) (fullObservationClock M)
    trunk _ (cfrDInformationFallback M fallback) who (payoff who) cut remaining info sampled]
  rfl

/-- A total parent response whose supported predictions are computed from the
completed child sampling law. Only unsupported entries use the old convention.
No continuation-quality, root-regret or safety certificate is supplied. -/
def cfrDConstructedSampledInformationOracle (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : CFRDPredictionNoise M) : CFRDValueOracle (fullInformation M) := by
  classical
  exact fun n trunk =>
    let response := cfrDConstructedInformationOracle M fallback payoff cut remaining
      bound loss noise n trunk
    { continuation := response.continuation
      prediction := fun who info =>
        if CFRDInformationQuerySampled M trunk fallback cut remaining who info then
          (cfrDInformationQuerySample M trunk fallback cut remaining
            (fun h player => payoff player h) bound loss who info
            (cfrDInformationContinuation M trunk fallback cut remaining
              (fun h player => payoff player h) bound loss) remaining).expect (payoff who) +
                noise n trunk who info
        else response.prediction who info }

/-- Every supported reference query, including a zero-factual-mass query,
really selects the sampled-value branch of this parent's response. -/
theorem cfrDConstructedSampledInformationOracle_prediction
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : CFRDPredictionNoise M) (n : Nat)
    (trunk : Profile (fullInformation M).behavioralSignature)
    (who : Fin 2) (info : (fullInformation M).InfoState who)
    (sampled : CFRDInformationQuerySampled M trunk fallback cut remaining who info) :
    (cfrDConstructedSampledInformationOracle M fallback payoff cut remaining bound loss noise
        n trunk).prediction who info =
      (cfrDInformationQuerySample M trunk fallback cut remaining
        (fun h player => payoff player h) bound loss who info
        (cfrDInformationContinuation M trunk fallback cut remaining
          (fun h player => payoff player h) bound loss) remaining).expect (payoff who) +
            noise n trunk who info := by
  classical
  exact if_pos sampled

/-- Equality holds for every round and queried trunk. It is proved before
recursing, so future noisy trunks are not replaced by an independent trace. -/
theorem cfrDConstructedSampledInformationOracle_eq
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : CFRDPredictionNoise M) :
    cfrDConstructedSampledInformationOracle M fallback payoff cut remaining bound loss noise =
      cfrDConstructedInformationOracle M fallback payoff cut remaining bound loss noise := by
  classical
  funext n trunk
  let response := cfrDConstructedInformationOracle M fallback payoff cut remaining
    bound loss noise n trunk
  have predictions :
      (cfrDConstructedSampledInformationOracle M fallback payoff cut remaining
        bound loss noise n trunk).prediction = response.prediction := by
    funext who info
    by_cases sampled : CFRDInformationQuerySampled M trunk fallback cut remaining who info
    · rw [cfrDConstructedSampledInformationOracle_prediction M fallback payoff cut remaining
        bound loss noise n trunk who info sampled]
      exact cfrDInformationQuerySample_prediction M trunk fallback payoff cut remaining
        bound loss noise n who info sampled
    · exact if_neg sampled
  exact congrArg (fun vector => (⟨response.continuation, vector⟩ :
    CFRDValueResponse (fullInformation M))) predictions

variable [∀ who, DecidableEq ((fullInformation M).InfoState who)]

/-- The actual recursively updated regret state agrees at EVERY finite round,
with positive or zero perturbations kept in both constructions. -/
theorem cfrDConstructedSampledInformationOracle_state_eq
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : CFRDPredictionNoise M) (n : Nat) :
    cfrDState (fullInformation M)
        (cfrDDepthTrunk (fullInformation M) (fullObservationClock M) cut)
        (cfrDInformationFallback M fallback)
        (cfrDDepthOracle (fullInformation M) (fullObservationClock M)
          (cfrDInformationFallback M fallback) payoff cut remaining
          (cfrDConstructedSampledInformationOracle M fallback payoff cut remaining
            bound loss noise)) n =
      cfrDState (fullInformation M)
        (cfrDDepthTrunk (fullInformation M) (fullObservationClock M) cut)
        (cfrDInformationFallback M fallback)
        (cfrDDepthOracle (fullInformation M) (fullObservationClock M)
          (cfrDInformationFallback M fallback) payoff cut remaining
          (cfrDConstructedInformationOracle M fallback payoff cut remaining
            bound loss noise)) n := by
  rw [cfrDConstructedSampledInformationOracle_eq]

/-- The same sampled-value parent has the corrected finite-time carried-play
bound. Prediction error, positive child tolerance and finite outer iterations
remain separate. The unknown opponent is fixed outside the private seed.
This preserves the chosen continuation; independently re-solving later PBSs
is a further obligation, not an implicit premise of this result. -/
theorem cfrDConstructedSampledInformationOracle_carried_security
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
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
          (cfrDConstructedSampledInformationOracle M fallback payoff cut remaining
            bound loss noise) n.val) unknown who cut remaining).expect (payoff who) := by
  rw [cfrDConstructedSampledInformationOracle_eq]
  exact cfrDConstructedInformationOracle_carried_security M fallback payoff zeroSum cut remaining
    bound error loss hb he hl bounded noise noiseBound reference equilibrium unknown who t

end Parent
end GameTheory.ReBeL
