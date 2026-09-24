/-
# Fresh-continuation comparisons under information-local reference changes

The OLD reference law is dominated by the NEW one through a density measurable
at the complete information/live tag. This preserves the queried conditionals
without requiring equality of the full laws. It is an explicit additional
premise, not a consequence of scalar Nash accuracy or arbitrary re-solving.
-/

import GameTheory.Analysis.ReBeL.CFRDFreshValueDrift
import GameTheory.ReBeL.OracleReweighting

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [∀ who info, Fintype (M.Choice who info)]

/-- Supported signed changes telescope under an information-local density.
The direction matters: every OLD queried fiber must remain supported by the
middle law. No equality of the observation marginals is required. -/
theorem cfrDFreshValueChange_add_of_informationReweight
    (base middle next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) (weight : M.InfoState who × Bool → ℝ)
    (density : ∀ history,
      (unilateralReferenceLaw M base fallback who cut).prob history =
        (unilateralReferenceLaw M middle fallback who cut).prob history *
          weight (M.infoOf who history.trace, cfrDCutLive remaining history))
    (info : M.InfoState who)
    (sampled : (info, true) ∈ ((unilateralReferenceLaw M base fallback who cut).map
      (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))).support) :
    cfrDFreshValueChange M base next fallback who payoff cut remaining info =
      cfrDFreshValueChange M base middle fallback who payoff cut remaining info +
        cfrDFreshValueChange M middle next fallback who payoff cut remaining info := by
  have same := informationReweight_conditional
    (unilateralReferenceLaw M middle fallback who cut)
    (unilateralReferenceLaw M base fallback who cut)
    (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))
    weight density (info, true) sampled
  unfold cfrDFreshValueChange conditionalOracleValue
  rw [← same, ← FinDist.expect_add]
  apply FinDist.expect_congr
  intro history _
  ring

variable [Fintype E.History]

/-- The OLD supported-query maximum remains subadditive. A fiber supported only
by the new law is harmless: it can enlarge the middle-to-next maximum. A fiber
supported only by the old law is excluded by the stated density, not discarded. -/
theorem cfrDFreshValueDrift_le_add_of_informationReweight
    (base middle next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) (weight : M.InfoState who × Bool → ℝ)
    (density : ∀ history,
      (unilateralReferenceLaw M base fallback who cut).prob history =
        (unilateralReferenceLaw M middle fallback who cut).prob history *
          weight (M.infoOf who history.trace, cfrDCutLive remaining history)) :
    cfrDFreshValueDrift M base next fallback who payoff cut remaining ≤
      cfrDFreshValueDrift M base middle fallback who payoff cut remaining +
        cfrDFreshValueDrift M middle next fallback who payoff cut remaining := by
  apply cfrDFreshValueDrift_le M base next fallback who payoff cut remaining
  · exact add_nonneg
      (cfrDFreshValueDrift_nonneg M base middle fallback who payoff cut remaining)
      (cfrDFreshValueDrift_nonneg M middle next fallback who payoff cut remaining)
  · intro info sampled
    have sampledMiddle : (info, true) ∈ ((unilateralReferenceLaw M middle fallback who cut).map
        (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))).support := by
      rw [FinDist.support_map] at sampled ⊢
      obtain ⟨history, reached, tag⟩ := sampled
      exact ⟨history, informationReweight_support
        (unilateralReferenceLaw M middle fallback who cut)
        (unilateralReferenceLaw M base fallback who cut)
        (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h)) weight density reached, tag⟩
    rw [cfrDFreshValueChange_add_of_informationReweight M base middle next fallback who
      payoff cut remaining weight density info sampled]
    exact add_le_add
      (cfrDFreshValueChange_le_drift M base middle fallback who payoff cut remaining info sampled)
      (cfrDFreshValueChange_le_drift M middle next fallback who payoff cut remaining info
        sampledMiddle)

variable {K : Type*} [Fintype K] [Nonempty K]

/-- Each actual finite parent member may have its own information-local density.
This statement does not identify the unknown opponent's posterior with a model. -/
theorem cfrDFreshUniformDrift_le_add_of_informationReweight
    (plays middle next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) (weight : K → M.InfoState who × Bool → ℝ)
    (density : ∀ n history,
      (unilateralReferenceLaw M (plays n) fallback who cut).prob history =
        (unilateralReferenceLaw M (middle n) fallback who cut).prob history *
          weight n (M.infoOf who history.trace, cfrDCutLive remaining history)) :
    cfrDFreshUniformDrift M plays next fallback who payoff cut remaining ≤
      cfrDFreshUniformDrift M plays middle fallback who payoff cut remaining +
        cfrDFreshUniformDrift M middle next fallback who payoff cut remaining := by
  apply cfrDFreshUniformDrift_le M plays next fallback who payoff cut remaining
  · exact add_nonneg
      (cfrDFreshUniformDrift_nonneg M plays middle fallback who payoff cut remaining)
      (cfrDFreshUniformDrift_nonneg M middle next fallback who payoff cut remaining)
  · intro n
    exact (cfrDFreshValueDrift_le_add_of_informationReweight M (plays n) (middle n) (next n)
      fallback who payoff cut remaining (weight n) (density n)).trans
      (add_le_add
        (cfrDFreshValueDrift_le_uniform M plays middle fallback who payoff cut remaining n)
        (cfrDFreshValueDrift_le_uniform M middle next fallback who payoff cut remaining n))

/-- The coherent resolver envelope needs equality only of the queried
conditionals, supplied here by an information-local reference density. The new
child's local quality remains a separate premise at this generic boundary.
No reference equality, unknown-opponent density, or final safety bound is assumed. -/
theorem cfrDFreshCoherentResolver_envelope_of_informationReweight (hrecall : M.PerfectRecall)
    (plays next : K → Profile M.behavioralSignature) (fallback : Profile M.strategicSignature)
    (unknown : Profile M.behavioralSignature) (who opponent : Fin 2)
    (different : opponent ≠ who) (cut remaining : Nat) (payoff : E.History → ℝ) (loss : ℝ)
    (weight : K → M.InfoState opponent × Bool → ℝ)
    (density : ∀ n history,
      (unilateralReferenceLaw M (plays n) fallback opponent cut).prob history =
        (unilateralReferenceLaw M (next n) fallback opponent cut).prob history *
          weight n (M.infoOf opponent history.trace, cfrDCutLive remaining history))
    (optimal : ∀ n, CFRDLeafOptimal M (next n) fallback opponent payoff cut remaining loss) :
    CFRDResolverEnvelope M plays (cfrDCoherentResolver M fallback next) fallback
      unknown who opponent cut remaining payoff
      (loss + cfrDFreshUniformDrift M plays next fallback opponent payoff cut remaining) := by
  have gap (n : K) (history : E.History) :
      privateResolvedEnvelopeGap M plays (cfrDCoherentResolver M fallback next)
          unknown who cut remaining payoff n history =
        cfrDLeafGain M (next n) opponent (unknown opponent) payoff remaining history +
          ((M.runBehavioralFrom (next n) remaining history).expect payoff -
            (M.runBehavioralFrom (plays n) remaining history).expect payoff) := by
    unfold privateResolvedEnvelopeGap
    rw [cfrDCoherentResolver_tail M hrecall]
    dsimp only [privateIterationState]
    rw [privateOpponent_profile M (next n) unknown who opponent different]
    unfold cfrDLeafGain
    ring
  intro n info sampled
  have same := informationReweight_conditional
    (unilateralReferenceLaw M (next n) fallback opponent cut)
    (unilateralReferenceLaw M (plays n) fallback opponent cut)
    (fun history => (M.infoOf opponent history.trace, cfrDCutLive remaining history))
    (weight n) (density n) (info, true) sampled
  have sampledNext : (info, true) ∈
      ((unilateralReferenceLaw M (next n) fallback opponent cut).map
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).support := by
    rw [FinDist.support_map] at sampled ⊢
    obtain ⟨history, reached, tag⟩ := sampled
    exact ⟨history, informationReweight_support
      (unilateralReferenceLaw M (next n) fallback opponent cut)
      (unilateralReferenceLaw M (plays n) fallback opponent cut)
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
      (weight n) (density n) reached, tag⟩
  have leaf := optimal n (unknown opponent) info sampledNext
  unfold conditionalOracleValue at leaf
  rw [← same] at leaf
  have drift := (cfrDFreshValueChange_le_drift M (plays n) (next n) fallback opponent payoff
    cut remaining info sampled).trans
      (cfrDFreshValueDrift_le_uniform M plays next fallback opponent payoff cut remaining n)
  unfold cfrDFreshValueChange conditionalOracleValue at drift
  unfold conditionalOracleValue
  rw [funext (gap n), FinDist.expect_add]
  exact add_le_add leaf drift

end GameTheory.ReBeL
