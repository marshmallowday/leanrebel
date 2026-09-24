/-
# Finite repeated fresh solves on a retained reference prefix

Every successor really runs the constructed information-set child solver on
its predecessor. Reference-law preservation is derived, not supplied in the
chain. The accumulated drift is explicit and need not vanish with child loss.
This is repeated solving at one fixed cut, not independent later carried-PBS
re-solving. Private finite-plan draws realize the final computed average.
-/

import GameTheory.Analysis.ReBeL.CFRDFreshResolve

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

section Drift

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who info, Fintype (M.Choice who info)]
variable {K : Type*} [Fintype K] [Nonempty K]

/-- No parent round changes when the entire family is retained. -/
theorem cfrDFreshUniformDrift_self (plays : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) :
    cfrDFreshUniformDrift M plays plays fallback who payoff cut remaining = 0 := by
  apply le_antisymm
  · apply cfrDFreshUniformDrift_le M plays plays fallback who payoff cut remaining 0 (le_refl _)
    intro n
    exact (cfrDFreshValueDrift_self M (plays n) fallback who payoff cut remaining).le
  · exact cfrDFreshUniformDrift_nonneg M plays plays fallback who payoff cut remaining

/-- A finite sequence of changes costs at most the sum of its measured drifts.
The reference law must be common to the comparisons, not just their observations. -/
theorem cfrDFreshUniformDrift_le_sum
    (plays : Nat → K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat)
    (referenceLaw : ∀ n k, unilateralReferenceLaw M (plays n k) fallback who cut =
      unilateralReferenceLaw M (plays 0 k) fallback who cut) (stages : Nat) :
    cfrDFreshUniformDrift M (plays 0) (plays stages) fallback who payoff cut remaining ≤
      ∑ n ∈ Finset.range stages,
        cfrDFreshUniformDrift M (plays n) (plays (n + 1)) fallback who payoff cut remaining := by
  induction stages with
  | zero => simp only [cfrDFreshUniformDrift_self, Finset.range_zero, Finset.sum_empty, le_refl]
  | succ stages ih =>
      calc
        _ ≤ cfrDFreshUniformDrift M (plays 0) (plays stages) fallback who payoff cut remaining +
            cfrDFreshUniformDrift M (plays stages) (plays (stages + 1)) fallback who payoff
              cut remaining :=
          cfrDFreshUniformDrift_le_add_of_referenceLaw M _ _ _ fallback who payoff cut remaining
            (referenceLaw stages)
        _ ≤ (∑ n ∈ Finset.range stages,
              cfrDFreshUniformDrift M (plays n) (plays (n + 1)) fallback who payoff cut remaining) +
            cfrDFreshUniformDrift M (plays stages) (plays (stages + 1)) fallback who payoff
              cut remaining := add_le_add_right ih _
        _ = _ := (Finset.sum_range_succ _ _).symm

end Drift

section Construction

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]

/-- Each successor recomputes the completed child from the preceding model.
The empty chain returns its input; no accuracy or equilibrium certificate is data. -/
def cfrDFreshInformationChain (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound : ℝ) (loss : Nat → ℝ)
    (base : Profile (fullInformation M).behavioralSignature) :
    Nat → Profile (fullInformation M).behavioralSignature
  | 0 => base
  | n + 1 => cfrDInformationContinuation M
      (cfrDFreshInformationChain M fallback payoff cut remaining bound loss base n)
      fallback cut remaining (fun h who => payoff who h) bound (loss n)

/-- An empty sequence neither solves a child nor changes the legal profile. -/
theorem cfrDFreshInformationChain_zero (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound : ℝ) (loss : Nat → ℝ)
    (base : Profile (fullInformation M).behavioralSignature) :
    cfrDFreshInformationChain M fallback payoff cut remaining bound loss base 0 = base := rfl

/-- Every actual fresh solve retains the original unilateral reference law.
No identification with the actual unknown opponent's posterior is used. -/
theorem cfrDFreshInformationChain_referenceLaw (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound : ℝ) (loss : Nat → ℝ)
    (base : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (stages : Nat) :
    unilateralReferenceLaw (fullInformation M)
        (cfrDFreshInformationChain M fallback payoff cut remaining bound loss base stages)
        (cfrDInformationFallback M fallback) who cut =
      unilateralReferenceLaw (fullInformation M) base
        (cfrDInformationFallback M fallback) who cut := by
  induction stages with
  | zero => rfl
  | succ stages ih =>
      exact (cfrDInformationContinuation_referenceLaw M
        (cfrDFreshInformationChain M fallback payoff cut remaining bound loss base stages)
        fallback cut remaining (fun h player => payoff player h) bound (loss stages) who).trans ih

/-- The last constructed solve supplies local quality on every live reference
query, including zero-own-reach types. Only its numerical tolerance must be positive. -/
theorem cfrDFreshInformationChain_leafOptimal (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h who => payoff who h))
    (cut remaining : Nat) (bound : ℝ) (loss : Nat → ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ who h, |payoff who h| ≤ bound)
    (base : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (stages : Nat)
    (positive : 0 < loss stages) :
    CFRDLeafOptimal (fullInformation M)
      (cfrDFreshInformationChain M fallback payoff cut remaining bound loss base (stages + 1))
      (cfrDInformationFallback M fallback) who (payoff who) cut remaining (loss stages) :=
  cfrDInformationContinuation_leafOptimal M
    (cfrDFreshInformationChain M fallback payoff cut remaining bound loss base stages)
    fallback cut remaining (fun h player => payoff player h) zeroSum bound (loss stages)
    nonneg positive (fun h player => bounded player h) who

variable {K : Type*}

/-- Draw the final recomputed average as a private legal plan. Intermediate
solves are computation, not draws shared with or observed by the opponent. -/
def cfrDFreshChainResolver (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound : ℝ) (loss : Nat → ℝ)
    (plays : K → Profile (fullInformation M).behavioralSignature) (stages : Nat) :
    CarriedPublicResolver (fullInformation M) K :=
  cfrDCoherentResolver (fullInformation M) (cfrDInformationFallback M fallback)
    (fun k => cfrDFreshInformationChain M fallback payoff cut remaining bound loss (plays k) stages)

/-- Private-plan realization preserves the full history law at every legal
carried state, not merely the expected scalar payoff at the modeled PBS. -/
theorem cfrDFreshChainResolver_tail (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound : ℝ) (loss : Nat → ℝ)
    (plays : K → Profile (fullInformation M).behavioralSignature) (stages : Nat)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (state : PrivateIterationState (fullInformation M) K) :
    carriedResolvedTail (fullInformation M)
        (cfrDFreshChainResolver M fallback payoff cut remaining bound loss plays stages)
        unknown who remaining state =
      (fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (cfrDFreshInformationChain M fallback payoff cut remaining bound loss
            (plays state.iteration) stages who)) remaining state.history :=
  cfrDCoherentResolver_tail (fullInformation M) (fullSignals_perfectRecall M.toInfoSignals)
    (cfrDInformationFallback M fallback) _ unknown who remaining state

variable [Fintype K] [Nonempty K]

/-- Accumulate the measured changes of the actual recomputed child sequence.
The common reference-law premise is discharged by the implementation. -/
theorem cfrDFreshInformationChain_drift_le_sum (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound : ℝ) (loss : Nat → ℝ)
    (plays : K → Profile (fullInformation M).behavioralSignature) (who : Fin 2) (stages : Nat) :
    cfrDFreshUniformDrift (fullInformation M) plays
        (fun k => cfrDFreshInformationChain M fallback payoff cut remaining bound loss
          (plays k) stages) (cfrDInformationFallback M fallback) who (payoff who) cut remaining ≤
      ∑ n ∈ Finset.range stages, cfrDFreshUniformDrift (fullInformation M)
        (fun k => cfrDFreshInformationChain M fallback payoff cut remaining bound loss (plays k) n)
        (fun k => cfrDFreshInformationChain M fallback payoff cut remaining bound loss
          (plays k) (n + 1)) (cfrDInformationFallback M fallback) who (payoff who) cut remaining :=
  cfrDFreshUniformDrift_le_sum (fullInformation M)
    (fun n k => cfrDFreshInformationChain M fallback payoff cut remaining bound loss (plays k) n)
    (cfrDInformationFallback M fallback) who (payoff who) cut remaining
    (fun n k => cfrDFreshInformationChain_referenceLaw M fallback payoff cut remaining
      bound loss (plays k) who n) stages

/-- Repeated fresh computation followed by a private final draw has a derived
opponent envelope. Last-child loss and every measured inter-solve drift stay
visible; no scalar-Nash-to-value-vector comparison is assumed. -/
theorem cfrDFreshChainResolver_envelope (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h who => payoff who h))
    (cut remaining : Nat) (bound : ℝ) (loss : Nat → ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ who h, |payoff who h| ≤ bound)
    (plays : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who opponent : Fin 2)
    (different : opponent ≠ who) (stages : Nat) (positive : 0 < loss stages) :
    CFRDResolverEnvelope (fullInformation M) plays
      (cfrDFreshChainResolver M fallback payoff cut remaining bound loss plays (stages + 1))
      (cfrDInformationFallback M fallback) unknown who opponent cut remaining (payoff opponent)
      (loss stages + ∑ n ∈ Finset.range (stages + 1), cfrDFreshUniformDrift (fullInformation M)
        (fun k => cfrDFreshInformationChain M fallback payoff cut remaining bound loss (plays k) n)
        (fun k => cfrDFreshInformationChain M fallback payoff cut remaining bound loss
          (plays k) (n + 1)) (cfrDInformationFallback M fallback) opponent (payoff opponent)
            cut remaining) := by
  have envelope := cfrDFreshCoherentResolver_envelope (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals) plays
    (fun k => cfrDFreshInformationChain M fallback payoff cut remaining bound loss
      (plays k) (stages + 1)) (cfrDInformationFallback M fallback) unknown who opponent different
    cut remaining (payoff opponent) (loss stages)
    (fun k => cfrDFreshInformationChain_referenceLaw M fallback payoff cut remaining bound loss
      (plays k) opponent (stages + 1))
    (fun k => cfrDFreshInformationChain_leafOptimal M fallback payoff zeroSum cut remaining
      bound loss nonneg bounded (plays k) opponent stages positive)
  have drift := cfrDFreshInformationChain_drift_le_sum M fallback payoff cut remaining bound loss
    plays opponent (stages + 1)
  intro k info sampled
  exact (envelope k info sampled).trans (add_le_add_left drift (loss stages))

end Construction
end GameTheory.ReBeL
