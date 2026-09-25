/-
# Exact value and actual-law safety for same-setting child recomputation

A real information-CFR parent round is used, not an arbitrary continuation
with a supplied stability certificate. Re-solving at its original cut with
identical settings gives zero signed live-query change. The final coherent
private-plan draw preserves the actual seed/history law against any opponent.
This does not identify a native child-iteration draw with that plan draw.
-/

import GameTheory.Analysis.ReBeL.CFRDQueryReplay
import GameTheory.Analysis.ReBeL.CFRDFreshChain

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

section Clamp

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)

/-- Replacing only the focal policy by its tail preserves execution from a
cut history against every unchanged information-local opposing policy. -/
theorem cfrDDepthProfile_focal_atCut (clock : ObservationClock M)
    (trunk continuation unknown : Profile M.behavioralSignature) (who : Fin 2)
    (cut fuel : Nat) (history : E.History) (atCut : history.trace.length = cut) :
    M.runBehavioralFrom
        (Profile.update unknown who ((cfrDDepthProfile M clock cut trunk continuation) who))
        fuel history =
      M.runBehavioralFrom (Profile.update unknown who (continuation who)) fuel history := by
  apply M.runBehavioralFrom_congr
  intro later reaches _ player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    have after : ¬ clock.depth who (M.infoOf who later.trace) < cut := by
      rw [clock.correct]
      have monotone := reaches.trace_length_le
      omega
    simp only [cfrDDepthProfile, cfrDDepthTrunk, decide_eq_true_eq, if_neg after]
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]

variable [∀ who info, Fintype (M.Choice who info)]

/-- Only a supported live OLD reference query is evaluated. Restoring the
trunk cannot change its continuation value, even at zero factual reach. -/
theorem cfrDDepthProfile_valueChange_zero (clock : ObservationClock M)
    (trunk continuation : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) (info : M.InfoState who)
    (sampled : (info, true) ∈ ((unilateralReferenceLaw M trunk fallback who cut).map
      (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h))).support) :
    cfrDFreshValueChange M (cfrDDepthProfile M clock cut trunk continuation)
      continuation fallback who payoff cut remaining info = 0 := by
  have value := cfrDDepthProfile_live_value M clock trunk continuation fallback who
    payoff cut remaining info sampled
  unfold cfrDFreshValueChange conditionalOracleValue
  unfold conditionalOracleValue at value
  rw [cfrDDepthProfile_referenceLaw] at value ⊢
  rw [FinDist.expect_sub, value, sub_self]

end Clamp

section Native

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]
variable [∀ who, DecidableEq ((fullInformation M).InfoState who)]

/-- The computed maximum of positive live-query value changes is ZERO for
an actual noisy parent round followed by one identical-setting recomputation.
There is no small-drift, output-equality or child-Nash input. -/
theorem cfrDInformationReplay_drift_zero (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : CFRDPredictionNoise M) (n : Nat) (who : Fin 2) :
    let base := cfrDDepthPlay (fullInformation M) (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut remaining
      (cfrDConstructedSampledInformationOracle M fallback payoff cut remaining bound loss noise) n
    cfrDFreshValueDrift (fullInformation M) base
      (cfrDInformationContinuation M base fallback cut remaining
        (fun h player => payoff player h) bound loss)
      (cfrDInformationFallback M fallback) who (payoff who) cut remaining = 0 := by
  dsimp only
  apply le_antisymm
  · apply cfrDFreshValueDrift_le _ _ _ _ _ _ _ _ 0 (le_refl _)
    intro info sampled
    rw [cfrDConstructedSampledInformationOracle_replay]
    rw [cfrDDepthPlay_eq] at sampled ⊢
    rw [cfrDDepthProfile_referenceLaw] at sampled
    exact (cfrDDepthProfile_valueChange_zero (fullInformation M) (fullObservationClock M)
      _ _ (cfrDInformationFallback M fallback) who (payoff who) cut remaining info sampled).le
  · exact cfrDFreshValueDrift_nonneg _ _ _ _ _ _ _ _

/-- The zero rate holds uniformly over the actual finite parent family, not
only at a hand-picked round or under an unrelated sequence of sampled trunks. -/
theorem cfrDInformationReplay_uniformDrift_zero (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : CFRDPredictionNoise M) (who : Fin 2) (t : Nat) [NeZero t] :
    let plays := fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut remaining
      (cfrDConstructedSampledInformationOracle M fallback payoff cut remaining bound loss noise)
      n.val
    cfrDFreshUniformDrift (fullInformation M) plays
      (fun n => cfrDInformationContinuation M (plays n) fallback cut remaining
        (fun h player => payoff player h) bound loss)
      (cfrDInformationFallback M fallback) who (payoff who) cut remaining = 0 := by
  dsimp only
  apply le_antisymm
  · apply cfrDFreshUniformDrift_le _ _ _ _ _ _ _ _ 0 (le_refl _)
    intro n
    exact (cfrDInformationReplay_drift_zero M fallback payoff cut remaining bound loss
      noise n.val who).le
  · exact cfrDFreshUniformDrift_nonneg _ _ _ _ _ _ _ _

/-- One freshly computed child followed by its coherent private-plan draw
preserves the COMPLETE actual law. Prefixes retain their original private
iteration and hidden history; the unknown opponent is never conditioned away.
No model posterior is required, and early terminals are included. -/
theorem cfrDInformationReplay_resolve_law (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : CFRDPredictionNoise M) (t : Nat) (seed : FinDist (Fin t))
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) :
    let plays := fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut remaining
      (cfrDConstructedSampledInformationOracle M fallback payoff cut remaining bound loss noise)
      n.val
    privateCarriedResolve (fullInformation M) seed plays
        (cfrDFreshChainResolver M fallback payoff cut remaining bound (fun _ => loss) plays 1)
        unknown who cut remaining =
      privateCarriedContinue (fullInformation M) seed plays unknown who cut remaining := by
  dsimp only
  unfold privateCarriedResolve privateCarriedContinue
  apply FinDist.bind_congr
  intro state reached
  rw [cfrDFreshChainResolver_tail]
  unfold privateCarriedPrefix at reached
  rw [FinDist.support_bind] at reached
  obtain ⟨n, _, reached⟩ := reached
  rw [FinDist.support_map] at reached
  obtain ⟨history, reached, equal⟩ := reached
  rw [← equal]
  dsimp only [privateIterationState, cfrDFreshInformationChain]
  rcases (fullInformation M).terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
      _ cut E.initHistory history reached with stopped | depth
  · rw [(fullInformation M).runBehavioralFrom_of_terminal _ _ stopped,
      (fullInformation M).runBehavioralFrom_of_terminal _ _ stopped]
  · have atCut : history.trace.length = cut := by
      simpa only [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length,
        Nat.zero_add] using depth
    rw [cfrDConstructedSampledInformationOracle_replay]
    symm
    rw [cfrDDepthPlay_eq]
    exact cfrDDepthProfile_focal_atCut (fullInformation M) (fullObservationClock M)
      _ _ unknown who cut remaining history atCut

/-- Same-setting fresh recomputation has the parent's derived security bound,
with NO extra drift penalty. Positive child loss, finite T and numerical
prediction error remain visible. The final draw is coherent, not a claim that
arbitrary native-iteration sampling realizes a child off its own support. -/
theorem cfrDInformationReplay_security (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h who => payoff who h))
    (cut remaining : Nat) (bound error loss : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error)
    (hl : 0 < loss) (bounded : ∀ who h, |payoff who h| ≤ bound) (noise : CFRDPredictionNoise M)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (reference : Profile (fullInformation M).behavioralSignature)
    (equilibrium : IsNash ((fullInformation M).toBehavioralGameForm (cut + remaining))
      (euPreference (fun h who => payoff who h)) reference)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (t : Nat) [NeZero t] :
    let plays := fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut remaining
      (cfrDConstructedSampledInformationOracle M fallback payoff cut remaining bound loss noise)
      n.val
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
      (privateCarriedResolve (fullInformation M) (cfrIterationLaw t) plays
        (cfrDFreshChainResolver M fallback payoff cut remaining bound (fun _ => loss) plays 1)
        unknown who cut remaining).expect (payoff who) := by
  dsimp only
  rw [cfrDInformationReplay_resolve_law]
  exact cfrDConstructedSampledInformationOracle_carried_security M fallback payoff zeroSum
    cut remaining bound error loss hb he hl bounded noise noiseBound reference equilibrium
    unknown who t

end Native
end GameTheory.ReBeL
