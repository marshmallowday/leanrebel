/-
# Fresh-continuation comparisons under information-local reference changes

The OLD reference law is dominated by the NEW one through a density measurable
at the complete information/live tag. This preserves the queried conditionals
without requiring equality of the full laws. It is an explicit additional
premise, not a consequence of scalar Nash accuracy or arbitrary re-solving.
-/

import GameTheory.Analysis.ReBeL.CFRDFreshValueDrift
import GameTheory.ReBeL.OracleReweighting
import GameTheory.Math.Probability.FinDistConditioning

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


/-- A finite, computed maximum of conditional-law transport and lost-query
costs. OLD-unsupported queries contribute zero. No unknown opponent is input. -/
def cfrDReferenceTransportDefect (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (cut remaining : Nat) : ℝ :=
  max 0 (Finset.univ.sup' Finset.univ_nonempty fun n : K =>
    (Finset.univ : Finset E.History).sup' ⟨E.initHistory, Finset.mem_univ _⟩ fun history =>
      FinDist.conditionalTransportDefect
        (unilateralReferenceLaw M (plays n) fallback who cut)
        (unilateralReferenceLaw M (next n) fallback who cut)
        (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h))
        (M.infoOf who history.trace, true))

/-- The transport allowance is always nonnegative. -/
theorem cfrDReferenceTransportDefect_nonneg (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (cut remaining : Nat) :
    0 ≤ cfrDReferenceTransportDefect M plays next fallback who cut remaining := le_max_left _ _

/-- There is a uniform finite bound without a minimum-reach assumption. -/
theorem cfrDReferenceTransportDefect_le_two (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (cut remaining : Nat) :
    cfrDReferenceTransportDefect M plays next fallback who cut remaining ≤ 2 := by
  unfold cfrDReferenceTransportDefect
  apply max_le (by norm_num)
  apply Finset.sup'_le
  intro n _
  apply Finset.sup'_le
  intro history _
  exact FinDist.conditionalTransportDefect_le_two _ _ _ _

/-- Every OLD supported live query occurs in the history-indexed maximum. -/
theorem conditionalTransportDefect_le_reference (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (cut remaining : Nat) (n : K)
    (info : M.InfoState who)
    (sampled : (info, true) ∈ ((unilateralReferenceLaw M (plays n) fallback who cut).map
      (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h))).support) :
    FinDist.conditionalTransportDefect
        (unilateralReferenceLaw M (plays n) fallback who cut)
        (unilateralReferenceLaw M (next n) fallback who cut)
        (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h)) (info, true) ≤
      cfrDReferenceTransportDefect M plays next fallback who cut remaining := by
  classical
  rw [FinDist.support_map] at sampled
  obtain ⟨history, _, tag⟩ := sampled
  have same : M.infoOf who history.trace = info := congrArg Prod.fst tag
  unfold cfrDReferenceTransportDefect
  apply le_trans _ (le_max_right _ _)
  apply le_trans _ (Finset.le_sup' _ (Finset.mem_univ n))
  have member := Finset.le_sup' (s := (Finset.univ : Finset E.History))
    (fun h => FinDist.conditionalTransportDefect
      (unilateralReferenceLaw M (plays n) fallback who cut)
      (unilateralReferenceLaw M (next n) fallback who cut)
      (fun leaf => (M.infoOf who leaf.trace, cfrDCutLive remaining leaf))
      (M.infoOf who h.trace, true)) (Finset.mem_univ history)
  simpa only [same] using member

/-- Information-local domination is exactly a zero-transport special case.
The continuation-value drift itself is not asserted to vanish. -/
theorem cfrDReferenceTransportDefect_eq_zero_of_informationReweight
    (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (cut remaining : Nat)
    (weight : K → M.InfoState who × Bool → ℝ)
    (density : ∀ n history,
      (unilateralReferenceLaw M (plays n) fallback who cut).prob history =
        (unilateralReferenceLaw M (next n) fallback who cut).prob history *
          weight n (M.infoOf who history.trace, cfrDCutLive remaining history)) :
    cfrDReferenceTransportDefect M plays next fallback who cut remaining = 0 := by
  apply le_antisymm
  · unfold cfrDReferenceTransportDefect
    apply max_le (le_refl _)
    apply Finset.sup'_le
    intro n _
    apply Finset.sup'_le
    intro history _
    apply le_of_eq
    apply FinDist.conditionalTransportDefect_eq_zero
    · intro sampled
      rw [FinDist.support_map] at sampled ⊢
      obtain ⟨h, reached, tag⟩ := sampled
      exact ⟨h, informationReweight_support
        (unilateralReferenceLaw M (next n) fallback who cut)
        (unilateralReferenceLaw M (plays n) fallback who cut)
        (fun leaf => (M.infoOf who leaf.trace, cfrDCutLive remaining leaf))
        (weight n) (density n) reached, tag⟩
    · intro sampled
      exact informationReweight_conditional
        (unilateralReferenceLaw M (next n) fallback who cut)
        (unilateralReferenceLaw M (plays n) fallback who cut)
        (fun leaf => (M.infoOf who leaf.trace, cfrDCutLive remaining leaf))
        (weight n) (density n) _ sampled
  · exact cfrDReferenceTransportDefect_nonneg M plays next fallback who cut remaining

/-- A fresh resolver has an explicit envelope even when reference conditionals
change or an OLD query disappears. Child response gain costs at most twice the
payoff bound; no density or support inclusion is assumed. The computed transport
and value-drift terms must still be controlled for a vanishing safety rate. -/
theorem cfrDFreshCoherentResolver_envelope_with_transport (hrecall : M.PerfectRecall)
    (plays next : K → Profile M.behavioralSignature) (fallback : Profile M.strategicSignature)
    (unknown : Profile M.behavioralSignature) (who opponent : Fin 2)
    (different : opponent ≠ who) (cut remaining : Nat) (payoff : E.History → ℝ)
    (bound loss : ℝ) (boundNonneg : 0 ≤ bound) (lossNonneg : 0 ≤ loss)
    (bounded : ∀ h, |payoff h| ≤ bound)
    (optimal : ∀ n, CFRDLeafOptimal M (next n) fallback opponent payoff cut remaining loss) :
    CFRDResolverEnvelope M plays (cfrDCoherentResolver M fallback next) fallback
      unknown who opponent cut remaining payoff
      (loss + cfrDFreshUniformDrift M plays next fallback opponent payoff cut remaining +
        2 * bound * cfrDReferenceTransportDefect M plays next fallback opponent cut remaining) := by
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
  have gainBound (n : K) (h : E.History) :
      |cfrDLeafGain M (next n) opponent (unknown opponent) payoff remaining h| ≤ 2 * bound := by
    unfold cfrDLeafGain
    have first := FinDist.abs_expect_le_of_abs_bound
      (M.runBehavioralFrom (Profile.update (next n) opponent (unknown opponent)) remaining h)
      payoff (fun history _ => bounded history)
    have second := FinDist.abs_expect_le_of_abs_bound
      (M.runBehavioralFrom (next n) remaining h) payoff (fun history _ => bounded history)
    have triangle := abs_sub
      ((M.runBehavioralFrom (Profile.update (next n) opponent (unknown opponent))
        remaining h).expect payoff)
      ((M.runBehavioralFrom (next n) remaining h).expect payoff)
    linarith
  intro n info sampled
  have transported := FinDist.condOnFibre_expect_le_add_transport
    (unilateralReferenceLaw M (plays n) fallback opponent cut)
    (unilateralReferenceLaw M (next n) fallback opponent cut)
    (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h)) (info, true) sampled
    (cfrDLeafGain M (next n) opponent (unknown opponent) payoff remaining)
    (2 * bound) loss lossNonneg (gainBound n) (optimal n (unknown opponent) info)
  have defect := mul_le_mul_of_nonneg_left
    (conditionalTransportDefect_le_reference M plays next fallback opponent cut remaining
      n info sampled) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) boundNonneg)
  have drift := (cfrDFreshValueChange_le_drift M (plays n) (next n) fallback opponent payoff
    cut remaining info sampled).trans
      (cfrDFreshValueDrift_le_uniform M plays next fallback opponent payoff cut remaining n)
  unfold cfrDFreshValueChange conditionalOracleValue at drift
  unfold conditionalOracleValue
  rw [funext (gap n), FinDist.expect_add]
  linarith

end GameTheory.ReBeL
