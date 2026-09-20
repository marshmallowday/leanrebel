/-
# Counterfactual model envelopes for public re-solving

The comparator is the incumbent MODEL continuation, not its payoff against
one fixed weak opponent. Positive opponent-reference fibers cover off-model
prefixes. Their upper envelopes transfer to prefix-only deviations, the
quantities actually controlled by the outer CFR-D trunk regret theorem.
-/

import GameTheory.Analysis.ReBeL.CFRDChildResolve

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*}

/-- Resolved payoff minus incumbent MODEL payoff at one history. The payoff
will belong to the opponent; this is not fixed-opponent replacement loss. -/
def privateResolvedEnvelopeGap (plays : K → Profile M.behavioralSignature)
    (resolver : CarriedPublicResolver M K) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut remaining : Nat) (payoff : E.History → ℝ)
    (iteration : K) (history : E.History) : ℝ :=
  (carriedResolvedTail M resolver unknown who remaining
      (privateIterationState M plays cut iteration history)).expect payoff -
    (M.runBehavioralFrom (plays iteration) remaining history).expect payoff

/-- Stopped leaves contribute exactly zero, without a posterior or query. -/
theorem privateResolvedEnvelopeGap_stopped (plays : K → Profile M.behavioralSignature)
    (resolver : CarriedPublicResolver M K) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut remaining : Nat) (payoff : E.History → ℝ)
    (iteration : K) (history : E.History)
    (stopped : cfrDCutLive remaining history ≠ true) :
    privateResolvedEnvelopeGap M plays resolver unknown who cut remaining payoff
      iteration history = 0 := by
  unfold privateResolvedEnvelopeGap carriedResolvedTail
  simp only [privateIterationState, if_neg stopped,
    cfrD_run_stopped M _ remaining history stopped, sub_self]

/-- Conditioning on a stopped information fiber cannot create envelope loss. -/
theorem privateResolvedEnvelopeGap_conditional_stopped
    (plays : K → Profile M.behavioralSignature) (resolver : CarriedPublicResolver M K)
    (unknown : Profile M.behavioralSignature) (who opponent : Fin 2)
    (cut remaining : Nat) (payoff : E.History → ℝ) (iteration : K)
    (law : FinDist E.History) (info : M.InfoState opponent)
    (sampled : (info, false) ∈ (law.map fun h =>
      (M.infoOf opponent h.trace, cfrDCutLive remaining h)).support) :
    conditionalOracleValue law
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
      (privateResolvedEnvelopeGap M plays resolver unknown who cut remaining payoff iteration)
      (info, false) = 0 := by
  unfold conditionalOracleValue
  calc
    _ = (law.condOnFibre
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
        (info, false)).expect (fun _ => (0 : ℝ)) := by
      apply FinDist.expect_congr
      intro history reached
      have same := congrArg Prod.snd (conditionalOracle_support law
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
        (info, false) sampled history reached)
      apply privateResolvedEnvelopeGap_stopped
      rw [show cfrDCutLive remaining history = false from same]
      decide
    _ = 0 := FinDist.expect_const _ _

variable [∀ who info, Fintype (M.Choice who info)]

/-- Local upper envelope in the OPPONENT'S payoff, at every positive reference
fiber. This is a solver obligation, not a consequence of independent Nash
selection and not a certificate of the final game's security. -/
def CFRDResolverEnvelope (plays : K → Profile M.behavioralSignature)
    (resolver : CarriedPublicResolver M K) (fallback : Profile M.strategicSignature)
    (unknown : Profile M.behavioralSignature) (who opponent : Fin 2)
    (cut remaining : Nat) (payoff : E.History → ℝ) (loss : ℝ) : Prop :=
  ∀ iteration info,
    (info, true) ∈ ((unilateralReferenceLaw M (plays iteration) fallback opponent cut).map
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).support →
    conditionalOracleValue (unilateralReferenceLaw M (plays iteration) fallback opponent cut)
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
      (privateResolvedEnvelopeGap M plays resolver unknown who cut remaining payoff iteration)
      (info, true) ≤ loss

/-- Perfect recall derives the change of measure for the actual arbitrary
opponent's prefix. Zero factual reach is not divided away or excluded. -/
theorem privateResolvedEnvelopeGap_prefix_le (hrecall : M.PerfectRecall)
    (plays : K → Profile M.behavioralSignature) (resolver : CarriedPublicResolver M K)
    (fallback : Profile M.strategicSignature) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (different : opponent ≠ who) (cut remaining : Nat)
    (payoff : E.History → ℝ) (loss : ℝ) (nonneg : 0 ≤ loss)
    (envelope : CFRDResolverEnvelope M plays resolver fallback unknown who opponent
      cut remaining payoff loss) (iteration : K) :
    (M.runBehavioral (Profile.update unknown who (plays iteration who)) cut).expect
      (privateResolvedEnvelopeGap M plays resolver unknown who cut remaining payoff iteration) ≤
      loss := by
  rw [privateOpponent_profile M (plays iteration) unknown who opponent different]
  apply conditionalOracle_reweight_le
    (unilateralReferenceLaw M (plays iteration) fallback opponent cut)
    (M.runBehavioral (Profile.update (plays iteration) opponent (unknown opponent)) cut)
    (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
    (fun tag : M.InfoState opponent × Bool =>
      unilateralDensity M (plays iteration) fallback opponent (unknown opponent) tag.1)
    (unilateralReference_density M hrecall (plays iteration) fallback opponent
      (unknown opponent) cut)
    (privateResolvedEnvelopeGap M plays resolver unknown who cut remaining payoff iteration) loss
  rintro ⟨info, flag⟩ sampled
  cases flag
  · rw [privateResolvedEnvelopeGap_conditional_stopped M plays resolver unknown who opponent
      cut remaining payoff iteration _ info sampled]
    exact nonneg
  · exact envelope iteration info sampled

/-- A resolved opponent payoff is compared to the incumbent model after ONLY
the unknown opponent's prefix is installed. This is weaker than preserving
exploitation against that opponent and matches the computed trunk-regret sum. -/
theorem privateCarriedResolve_envelope_le_prefix (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (seed : FinDist K)
    (plays : K → Profile M.behavioralSignature) (resolver : CarriedPublicResolver M K)
    (fallback : Profile M.strategicSignature) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (different : opponent ≠ who) (cut remaining : Nat)
    (payoff : E.History → ℝ) (loss : ℝ) (nonneg : 0 ≤ loss)
    (envelope : CFRDResolverEnvelope M plays resolver fallback unknown who opponent
      cut remaining payoff loss) :
    (privateCarriedResolve M seed plays resolver unknown who cut remaining).expect payoff -
      seed.expect (fun n => (M.runBehavioral (Profile.update (plays n) opponent
        (cfrDPrefixPolicy M clock (plays n) opponent (unknown opponent) cut))
        (cut + remaining)).expect payoff) ≤ loss := by
  have virtual (n : K) :
      (M.runBehavioral (Profile.update (plays n) opponent
        (cfrDPrefixPolicy M clock (plays n) opponent (unknown opponent) cut))
        (cut + remaining)).expect payoff =
      (M.runBehavioral (Profile.update unknown who (plays n who)) cut).expect
        (fun h => (M.runBehavioralFrom (plays n) remaining h).expect payoff) := by
    rw [cfrDPrefix_run_bind, FinDist.expect_bind,
      ← privateOpponent_profile M (plays n) unknown who opponent different]
  simp only [privateCarriedResolve, privateCarriedPrefix, FinDist.expect_bind,
    FinDist.expect_map, virtual]
  rw [← FinDist.expect_sub]
  apply FinDist.expect_le_of_forall
  intro n _
  rw [← FinDist.expect_sub]
  exact privateResolvedEnvelopeGap_prefix_le M hrecall plays resolver fallback unknown who
    opponent different cut remaining payoff loss nonneg envelope n

/-- Retaining the virtual continuation specializes the envelope to the
already established opponent leaf-optimality contract. This is an actual
instantiation, but not a claim that arbitrary fresh child solves agree. -/
theorem cfrDResolverEnvelope_retained (plays : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (different : opponent ≠ who) (cut remaining : Nat)
    (payoff : E.History → ℝ) (loss : ℝ)
    (optimal : ∀ n, CFRDLeafOptimal M (plays n) fallback opponent payoff cut remaining loss) :
    CFRDResolverEnvelope M plays (fun n _ _ => FinDist.pure (plays n)) fallback
      unknown who opponent cut remaining payoff loss := by
  have gap (n : K) (history : E.History) :
      privateResolvedEnvelopeGap M plays (fun k _ _ => FinDist.pure (plays k))
        unknown who cut remaining payoff n history =
      cfrDLeafGain M (plays n) opponent (unknown opponent) payoff remaining history := by
    by_cases active : cfrDCutLive remaining history = true
    · simp only [privateResolvedEnvelopeGap, carriedResolvedTail, privateIterationState,
        if_pos active, FinDist.pure_bind, cfrDLeafGain,
        privateOpponent_profile M (plays n) unknown who opponent different]
    · rw [privateResolvedEnvelopeGap_stopped M plays _ unknown who cut remaining payoff
        n history active, cfrDLeafGain_stopped M _ _ _ _ _ _ active]
  intro n info sampled
  have gapFunction := funext (gap n)
  simpa only [conditionalOracleValue, gapFunction] using optimal n (unknown opponent) info sampled

/-- Numerical model-value accuracy and the resolved child's upper value bound
supply the envelope additively. The same reference fiber is used on both sides;
there is no premise equating the model PBS to the unknown opponent's law. -/
theorem cfrDResolverEnvelope_of_prediction
    (plays : K → Profile M.behavioralSignature) (resolver : CarriedPublicResolver M K)
    (fallback : Profile M.strategicSignature) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (cut remaining : Nat) (payoff : E.History → ℝ)
    (prediction : K → M.InfoState opponent → ℝ) (valueError childLoss : ℝ)
    (accurate : ∀ n info,
      (info, true) ∈ ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).support →
      |prediction n info -
        conditionalOracleValue (unilateralReferenceLaw M (plays n) fallback opponent cut)
          (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
          (fun h => (M.runBehavioralFrom (plays n) remaining h).expect payoff)
          (info, true)| ≤ valueError)
    (child : ∀ n info,
      (info, true) ∈ ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).support →
      conditionalOracleValue (unilateralReferenceLaw M (plays n) fallback opponent cut)
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
        (fun h => (carriedResolvedTail M resolver unknown who remaining
          (privateIterationState M plays cut n h)).expect payoff) (info, true) ≤
        prediction n info + childLoss) :
    CFRDResolverEnvelope M plays resolver fallback unknown who opponent cut remaining
      payoff (valueError + childLoss) := by
  intro n info sampled
  have valueBound := (abs_le.mp (accurate n info sampled)).2
  have childBound := child n info sampled
  unfold conditionalOracleValue privateResolvedEnvelopeGap
  rw [FinDist.expect_sub]
  unfold conditionalOracleValue at valueBound childBound
  linarith

end GameTheory.ReBeL
