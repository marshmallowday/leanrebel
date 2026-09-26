/-
# Actual versus stored-model continuation transport

The stored PBS advances with the chosen MODEL profile. The actual continuation
replaces its opponent with an unknown legal policy. Their discrepancy is
computed from the incoming laws and one-step execution kernels along ACTUAL
visits, not assumed away by child Nash or by public posterior identification.
-/

import GameTheory.Math.Probability.FinDistKernelVariation
import GameTheory.Analysis.ReBeL.CFRDResolveBelief

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History]

/-- Accumulated one-step source discrepancies along ACTUAL prefix laws.
Terminal histories have identical absorbing kernels and incur zero cost. -/
def executionKernelCharge (first second : Profile M.behavioralSignature) :
    Nat → FinDist E.History → ℝ
  | 0, _ => 0
  | fuel + 1, actual =>
      actual.expect (fun h => FinDist.atomVariation
        (M.runBehavioralFrom first 1 h) (M.runBehavioralFrom second 1 h)) +
      executionKernelCharge first second fuel (actual.bind (M.runBehavioralFrom first 1))

/-- Identical execution profiles introduce no kernel charge, even off path. -/
theorem executionKernelCharge_self (profile : Profile M.behavioralSignature)
    (fuel : Nat) (actual : FinDist E.History) :
    executionKernelCharge M profile profile fuel actual = 0 := by
  induction fuel generalizing actual with
  | zero => rfl
  | succ fuel ih =>
      simp only [executionKernelCharge, FinDist.atomVariation_self, FinDist.expect_const, ih,
        add_zero]

/-- A finite-horizon source-law bound derived from canonical execution itself.
The initial law mismatch is retained, including when fuel is zero. -/
theorem runBehavioralFrom_atomVariation_le
    (first second : Profile M.behavioralSignature) (fuel : Nat)
    (actual model : FinDist E.History) :
    FinDist.atomVariation (actual.bind (M.runBehavioralFrom first fuel))
      (model.bind (M.runBehavioralFrom second fuel)) ≤
      FinDist.atomVariation actual model + executionKernelCharge M first second fuel actual := by
  induction fuel generalizing actual model with
  | zero =>
      simp only [runBehavioralFrom, runRandomizedFor_zero, FinDist.bind_pure,
        executionKernelCharge, add_zero, le_refl]
  | succ fuel ih =>
      have splitRun (law : FinDist E.History) (profile : Profile M.behavioralSignature) :
          law.bind (M.runBehavioralFrom profile (fuel + 1)) =
            (law.bind (M.runBehavioralFrom profile 1)).bind (M.runBehavioralFrom profile fuel) := by
        rw [FinDist.bind_bind]
        apply FinDist.bind_congr
        intro h _
        simpa only [Nat.add_comm 1 fuel] using M.runBehavioralFrom_add profile 1 fuel h
      rw [splitRun, splitRun]
      have step := FinDist.atomVariation_bind_le actual model
        (M.runBehavioralFrom first 1) (M.runBehavioralFrom second 1)
      exact (ih _ _).trans (by
        dsimp only [executionKernelCharge]
        linarith only [step])

/-- The computed charge for the precise profiles used by carriedResolvedStep
and carriedBeliefUpdate. The actual initial law need not be the stored PBS. -/
def carriedOpponentModelCharge {past : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals past) (actual : FinDist E.History)
    (chosen unknown : Profile M.behavioralSignature) (who : Fin 2) (fuel : Nat) : ℝ :=
  FinDist.atomVariation actual belief.law +
    executionKernelCharge M (Profile.update unknown who (chosen who)) chosen fuel actual

/-- With no continuation, only the incoming law discrepancy remains. -/
theorem carriedOpponentModelCharge_zero {past : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals past) (actual : FinDist E.History)
    (chosen unknown : Profile M.behavioralSignature) (who : Fin 2) :
    carriedOpponentModelCharge M belief actual chosen unknown who 0 =
      FinDist.atomVariation actual belief.law := by
  simp only [carriedOpponentModelCharge, executionKernelCharge, add_zero]

/-- Matching the stored joint law AND model profile makes the charge zero. -/
theorem carriedOpponentModelCharge_self {past : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals past) (chosen : Profile M.behavioralSignature)
    (who : Fin 2) (fuel : Nat) :
    carriedOpponentModelCharge M belief belief.law chosen chosen who fuel = 0 := by
  simp only [carriedOpponentModelCharge, Profile.update_eq_self, FinDist.atomVariation_self,
    executionKernelCharge_self, add_zero]

/-- The actual and model continuation laws have the computed discrepancy.
The unknown opponent is never used to update the stored model belief. -/
theorem carriedOpponentModelCharge_controls_law {past : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals past) (actual : FinDist E.History)
    (chosen unknown : Profile M.behavioralSignature) (who : Fin 2) (fuel : Nat) :
    FinDist.atomVariation
      (actual.bind (M.runBehavioralFrom (Profile.update unknown who (chosen who)) fuel))
      (PublicBelief.continuationLaw M chosen fuel belief) ≤
      carriedOpponentModelCharge M belief actual chosen unknown who fuel :=
  runBehavioralFrom_atomVariation_le M _ chosen fuel actual belief.law

/-- A model-supported resulting history has a genuine carried posterior that
contains that history. No fallback is being called a posterior. -/
theorem carriedBeliefUpdate_contains_of_supported {past : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals past) (chosen : Profile M.behavioralSignature)
    (fuel : Nat) (history : E.History)
    (reached : history ∈ (PublicBelief.continuationLaw M chosen fuel belief).support) :
    ∃ next, carriedBeliefUpdate M (some belief) chosen fuel
        (publicTrace M.toInfoSignals history.trace) = some next ∧ history ∈ next.law.support := by
  classical
  let law := PublicBelief.continuationLaw M chosen fuel belief
  have possible : PublicBelief.Possible (S := M.toInfoSignals) law
      (publicTrace M.toInfoSignals history.trace) := ⟨history, rfl, reached⟩
  refine ⟨PublicBelief.condition law _ possible, ?_, ?_⟩
  · simp only [carriedBeliefUpdate, Option.bind_some, PublicBelief.condition?, dif_pos possible]
  · exact FinDist.mem_support_condOn law _ _ rfl reached

/-- Under actual continuation, failure to obtain a model posterior containing
the actual history is bounded by the executed source charge. This covers both
impossible public observations and hidden histories missing from a valid PBS. -/
theorem carriedBeliefUpdate_failure_probability_le {past : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals past) (actual : FinDist E.History)
    (chosen unknown : Profile M.behavioralSignature) (who : Fin 2) (fuel : Nat) :
    (actual.bind (M.runBehavioralFrom (Profile.update unknown who (chosen who)) fuel)).probOf
      {history | ¬ ∃ next, carriedBeliefUpdate M (some belief) chosen fuel
        (publicTrace M.toInfoSignals history.trace) = some next ∧ history ∈ next.law.support} ≤
      carriedOpponentModelCharge M belief actual chosen unknown who fuel := by
  apply (FinDist.probOf_le_atomVariation_of_model_impossible _
    (PublicBelief.continuationLaw M chosen fuel belief) _ ?_).trans
      (carriedOpponentModelCharge_controls_law M belief actual chosen unknown who fuel)
  intro history failed reached
  exact failed (carriedBeliefUpdate_contains_of_supported M belief chosen fuel history reached)

/-- Mean public conditional transport is charged under the ACTUAL public law.
An absent model query has the existing explicit support-defect cost; its total
conditional fallback is not interpreted as a certified posterior. -/
theorem carriedOpponentModelCharge_controls_public_transport {past : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals past) (actual : FinDist E.History)
    (chosen unknown : Profile M.behavioralSignature) (who : Fin 2) (fuel : Nat) :
    let realLaw := actual.bind
      (M.runBehavioralFrom (Profile.update unknown who (chosen who)) fuel)
    let modelLaw := PublicBelief.continuationLaw M chosen fuel belief
    (PublicBelief.publicLaw (S := M.toInfoSignals) realLaw).expect
      (FinDist.conditionalTransportDefect realLaw modelLaw
        (fun h => publicTrace M.toInfoSignals h.trace)) ≤
      2 * carriedOpponentModelCharge M belief actual chosen unknown who fuel := by
  dsimp only
  exact (FinDist.expect_transport_le_atomVariation _ _ _).trans
    (mul_le_mul_of_nonneg_left
      (carriedOpponentModelCharge_controls_law M belief actual chosen unknown who fuel)
      (by norm_num))

end GameTheory.ReBeL
