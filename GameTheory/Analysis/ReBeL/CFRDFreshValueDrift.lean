/-
# Computed counterfactual value drift under a fresh continuation

A fresh child can change the incumbent's information-value vector. The finite
maximum below measures the positive change on LIVE reference queries, including
zero factual reach. It is a real-valued specification, not a numeric runtime.
Local child optimality plus this computed drift yields the opponent envelope;
neither a fixed-opponent no-loss premise nor a final safety certificate is input.
-/

import GameTheory.Analysis.ReBeL.CFRDCoherentDraw
import Mathlib.Data.Finset.Lattice.Fold

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [∀ who info, Fintype (M.Choice who info)]

/-- The signed new-minus-old model value on the OLD reference information fiber. -/
def cfrDFreshValueChange (base next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) (info : M.InfoState who) : ℝ :=
  conditionalOracleValue (unilateralReferenceLaw M base fallback who cut)
    (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h))
    (fun h => (M.runBehavioralFrom next remaining h).expect payoff -
      (M.runBehavioralFrom base remaining h).expect payoff) (info, true)

/-- Keeping the same continuation changes no conditional model value. -/
theorem cfrDFreshValueChange_self (base : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) (info : M.InfoState who) :
    cfrDFreshValueChange M base base fallback who payoff cut remaining info = 0 := by
  unfold cfrDFreshValueChange conditionalOracleValue
  simp only [sub_self, FinDist.expect_const]

/-- Signed changes telescope on the SAME old reference law. Changing the
reference prefix is not covered by this identity. -/
theorem cfrDFreshValueChange_add_of_referenceLaw
    (base middle next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) (info : M.InfoState who)
    (referenceLaw : unilateralReferenceLaw M middle fallback who cut =
      unilateralReferenceLaw M base fallback who cut) :
    cfrDFreshValueChange M base next fallback who payoff cut remaining info =
      cfrDFreshValueChange M base middle fallback who payoff cut remaining info +
        cfrDFreshValueChange M middle next fallback who payoff cut remaining info := by
  unfold cfrDFreshValueChange conditionalOracleValue
  rw [referenceLaw, ← FinDist.expect_add]
  apply FinDist.expect_congr
  intro history _
  ring

variable [Fintype E.History]

/-- A finite maximum over supported live information queries, never over a
fabricated posterior. Repeated representatives of an information state do not
increase the maximum. The outer zero also covers an empty live query set. -/
def cfrDFreshValueDrift (base next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) : ℝ := by
  classical
  exact max 0 ((Finset.univ : Finset E.History).sup'
    ⟨E.initHistory, Finset.mem_univ _⟩ fun h =>
      if (M.infoOf who h.trace, true) ∈ ((unilateralReferenceLaw M base fallback who cut).map
          (fun leaf => (M.infoOf who leaf.trace, cfrDCutLive remaining leaf))).support then
        cfrDFreshValueChange M base next fallback who payoff cut remaining
          (M.infoOf who h.trace)
      else 0)

/-- The computed allowance is nonnegative, also when no live query is possible. -/
theorem cfrDFreshValueDrift_nonneg (base next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) : 0 ≤ cfrDFreshValueDrift M base next fallback who payoff cut remaining :=
  le_max_left _ _

/-- A positive reference query has a legal-history representative in the
finite maximum. Factual reach and a uniform positive probability floor are not required. -/
theorem cfrDFreshValueChange_le_drift (base next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) (info : M.InfoState who)
    (sampled : (info, true) ∈ ((unilateralReferenceLaw M base fallback who cut).map
      (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h))).support) :
    cfrDFreshValueChange M base next fallback who payoff cut remaining info ≤
      cfrDFreshValueDrift M base next fallback who payoff cut remaining := by
  classical
  have witness := sampled
  rw [FinDist.support_map] at witness
  obtain ⟨history, _, same⟩ := witness
  have observed : M.infoOf who history.trace = info := congrArg Prod.fst same
  unfold cfrDFreshValueDrift
  apply le_trans _ (le_max_right _ _)
  have member := Finset.le_sup'
    (s := (Finset.univ : Finset E.History))
    (fun h => if (M.infoOf who h.trace, true) ∈
        ((unilateralReferenceLaw M base fallback who cut).map
          (fun leaf => (M.infoOf who leaf.trace, cfrDCutLive remaining leaf))).support then
      cfrDFreshValueChange M base next fallback who payoff cut remaining (M.infoOf who h.trace)
      else 0) (Finset.mem_univ history)
  simpa only [observed, if_pos sampled] using member

/-- An independently justified numerical bound on every live value change
bounds the computed maximum. This is not inferred merely from child Nash. -/
theorem cfrDFreshValueDrift_le (base next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) (error : ℝ) (nonneg : 0 ≤ error)
    (bounded : ∀ info,
      (info, true) ∈ ((unilateralReferenceLaw M base fallback who cut).map
        (fun h => (M.infoOf who h.trace, cfrDCutLive remaining h))).support →
      cfrDFreshValueChange M base next fallback who payoff cut remaining info ≤ error) :
    cfrDFreshValueDrift M base next fallback who payoff cut remaining ≤ error := by
  classical
  unfold cfrDFreshValueDrift
  apply max_le nonneg
  apply Finset.sup'_le
  intro history _
  split_ifs with sampled
  · exact bounded _ sampled
  · exact nonneg

/-- Identical continuations incur exactly zero computed drift. -/
theorem cfrDFreshValueDrift_self (base : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) :
    cfrDFreshValueDrift M base base fallback who payoff cut remaining = 0 := by
  apply le_antisymm
  · apply cfrDFreshValueDrift_le M base base fallback who payoff cut remaining 0 (le_refl _)
    intro info _
    rw [cfrDFreshValueChange_self]
  · exact cfrDFreshValueDrift_nonneg M base base fallback who payoff cut remaining

/-- Zero remaining fuel excludes every live query instead of evaluating a
fallback conditional as though it had been queried. -/
theorem cfrDFreshValueDrift_zero_remaining (base next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut : Nat) : cfrDFreshValueDrift M base next fallback who payoff cut 0 = 0 := by
  apply le_antisymm
  · apply cfrDFreshValueDrift_le M base next fallback who payoff cut 0 0 (le_refl _)
    intro info sampled
    rw [FinDist.support_map] at sampled
    obtain ⟨history, _, same⟩ := sampled
    have impossible : (false : Bool) = true := by
      simpa only [cfrDCutLive_zero] using congrArg Prod.snd same
    cases impossible
  · exact cfrDFreshValueDrift_nonneg M base next fallback who payoff cut 0

/-- Successive fresh continuations have a subadditive positive drift when
both comparisons use the same supported reference queries. This does not assert
that either individual drift is small or follows from scalar Nash accuracy. -/
theorem cfrDFreshValueDrift_le_add_of_referenceLaw
    (base middle next : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat)
    (referenceLaw : unilateralReferenceLaw M middle fallback who cut =
      unilateralReferenceLaw M base fallback who cut) :
    cfrDFreshValueDrift M base next fallback who payoff cut remaining ≤
      cfrDFreshValueDrift M base middle fallback who payoff cut remaining +
        cfrDFreshValueDrift M middle next fallback who payoff cut remaining := by
  apply cfrDFreshValueDrift_le M base next fallback who payoff cut remaining
  · exact add_nonneg
      (cfrDFreshValueDrift_nonneg M base middle fallback who payoff cut remaining)
      (cfrDFreshValueDrift_nonneg M middle next fallback who payoff cut remaining)
  · intro info sampled
    have sampledMiddle := sampled
    rw [← referenceLaw] at sampledMiddle
    rw [cfrDFreshValueChange_add_of_referenceLaw M base middle next fallback who
      payoff cut remaining info referenceLaw]
    exact add_le_add
      (cfrDFreshValueChange_le_drift M base middle fallback who payoff cut remaining info sampled)
      (cfrDFreshValueChange_le_drift M middle next fallback who payoff cut remaining info
        sampledMiddle)

variable {K : Type*} [Fintype K] [Nonempty K]

/-- A uniform maximum over the actual finite parent family, not over a separate
learning trace. No arbitrary strategy or unknown opposing policy is an input. -/
def cfrDFreshUniformDrift (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) : ℝ :=
  max 0 (Finset.univ.sup' Finset.univ_nonempty fun n =>
    cfrDFreshValueDrift M (plays n) (next n) fallback who payoff cut remaining)

/-- The whole-family allowance remains nonnegative. -/
theorem cfrDFreshUniformDrift_nonneg (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) :
    0 ≤ cfrDFreshUniformDrift M plays next fallback who payoff cut remaining := le_max_left _ _

/-- Every actual parent round is represented in the uniform maximum. -/
theorem cfrDFreshValueDrift_le_uniform (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) (n : K) :
    cfrDFreshValueDrift M (plays n) (next n) fallback who payoff cut remaining ≤
      cfrDFreshUniformDrift M plays next fallback who payoff cut remaining := by
  unfold cfrDFreshUniformDrift
  apply le_trans _ (le_max_right _ _)
  exact Finset.le_sup'
    (fun k : K => cfrDFreshValueDrift M (plays k) (next k) fallback who payoff cut remaining)
    (Finset.mem_univ n)

/-- An entrywise numerical comparison may discharge the extra drift term.
The comparison is kept separate from the freshly solved child's regret bound. -/
theorem cfrDFreshUniformDrift_le (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) (error : ℝ) (nonneg : 0 ≤ error)
    (bounded : ∀ n, cfrDFreshValueDrift M (plays n) (next n) fallback who payoff
      cut remaining ≤ error) :
    cfrDFreshUniformDrift M plays next fallback who payoff cut remaining ≤ error := by
  unfold cfrDFreshUniformDrift
  exact max_le nonneg (Finset.sup'_le _ _ (fun n _ => bounded n))

/-- The actual finite parent family inherits drift subadditivity. Each
round must preserve its own reference law; no equality with the unknown
opponent's posterior, no shared seed, and no fresh-solve error rate is assumed. -/
theorem cfrDFreshUniformDrift_le_add_of_referenceLaw
    (plays middle next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat)
    (referenceLaw : ∀ n, unilateralReferenceLaw M (middle n) fallback who cut =
      unilateralReferenceLaw M (plays n) fallback who cut) :
    cfrDFreshUniformDrift M plays next fallback who payoff cut remaining ≤
      cfrDFreshUniformDrift M plays middle fallback who payoff cut remaining +
        cfrDFreshUniformDrift M middle next fallback who payoff cut remaining := by
  apply cfrDFreshUniformDrift_le M plays next fallback who payoff cut remaining
  · exact add_nonneg
      (cfrDFreshUniformDrift_nonneg M plays middle fallback who payoff cut remaining)
      (cfrDFreshUniformDrift_nonneg M middle next fallback who payoff cut remaining)
  · intro n
    exact (cfrDFreshValueDrift_le_add_of_referenceLaw M (plays n) (middle n) (next n)
      fallback who payoff cut remaining (referenceLaw n)).trans
      (add_le_add
        (cfrDFreshValueDrift_le_uniform M plays middle fallback who payoff cut remaining n)
        (cfrDFreshValueDrift_le_uniform M middle next fallback who payoff cut remaining n))

/-- A DIFFERENT continuation family yields a derived model envelope. Its local
optimality and unchanged reference prefix are the only strategic premises;
all cross-family model-value change is retained in the computed drift term.
Private plan draws realize the new family at every history, including off model. -/
theorem cfrDFreshCoherentResolver_envelope (hrecall : M.PerfectRecall)
    (plays next : K → Profile M.behavioralSignature) (fallback : Profile M.strategicSignature)
    (unknown : Profile M.behavioralSignature) (who opponent : Fin 2)
    (different : opponent ≠ who) (cut remaining : Nat) (payoff : E.History → ℝ) (loss : ℝ)
    (referenceLaw : ∀ n, unilateralReferenceLaw M (next n) fallback opponent cut =
      unilateralReferenceLaw M (plays n) fallback opponent cut)
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
  have sampledNext : (info, true) ∈ ((unilateralReferenceLaw M (next n)
      fallback opponent cut).map
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).support := by
    rw [referenceLaw n]
    exact sampled
  have leaf := optimal n (unknown opponent) info sampledNext
  unfold conditionalOracleValue at leaf
  rw [referenceLaw n] at leaf
  have drift := (cfrDFreshValueChange_le_drift M (plays n) (next n) fallback opponent payoff
    cut remaining info sampled).trans
      (cfrDFreshValueDrift_le_uniform M plays next fallback opponent payoff cut remaining n)
  unfold cfrDFreshValueChange conditionalOracleValue at drift
  unfold conditionalOracleValue
  rw [funext (gap n), FinDist.expect_add]
  exact add_le_add leaf drift

end GameTheory.ReBeL
