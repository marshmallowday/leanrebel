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
      have zeroKernel (profile : Profile M.behavioralSignature) :
          M.runBehavioralFrom profile 0 = FinDist.pure := rfl
      simp only [zeroKernel, FinDist.bind_pure, executionKernelCharge, add_zero, le_refl]
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

omit [Fintype E.History] in
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
  · exact dif_pos possible
  · exact FinDist.mem_support_condOn law _ possible rfl reached

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


/-- Accumulated support leakage of one-step kernels under ACTUAL visits.
This records missing model outcomes, not a difference of positive atom weights. -/
def executionSupportCharge (first second : Profile M.behavioralSignature) :
    Nat → FinDist E.History → ℝ
  | 0, _ => 0
  | fuel + 1, actual =>
      actual.expect (fun h => (M.runBehavioralFrom first 1 h).probOf
        {next | next ∉ (M.runBehavioralFrom second 1 h).support}) +
      executionSupportCharge first second fuel (actual.bind (M.runBehavioralFrom first 1))

omit [Fintype E.History] in
/-- One-step support inclusion makes the complete support-leakage charge zero.
Kernel probabilities and the two legal profiles need not be equal. -/
theorem executionSupportCharge_eq_zero_of_step_support_subset
    (first second : Profile M.behavioralSignature)
    (included : ∀ h, (M.runBehavioralFrom first 1 h).support ⊆
      (M.runBehavioralFrom second 1 h).support)
    (fuel : Nat) (actual : FinDist E.History) :
    executionSupportCharge M first second fuel actual = 0 := by
  have stepZero (h : E.History) :
      (M.runBehavioralFrom first 1 h).probOf
        {next | next ∉ (M.runBehavioralFrom second 1 h).support} = 0 :=
    FinDist.probOf_unsupported_eq_zero_of_support_subset _ _ (included h)
  induction fuel generalizing actual with
  | zero => rfl
  | succ fuel ih =>
      simp only [executionSupportCharge, stepZero, FinDist.expect_const, ih, add_zero]

omit [Fintype E.History] in
/-- Finite-horizon lost support depends on incoming unsupported mass and actual
one-step leakage. No equality or density bound on the input laws is assumed. -/
theorem runBehavioralFrom_unsupported_le
    (first second : Profile M.behavioralSignature) (fuel : Nat)
    (actual model : FinDist E.History) :
    (actual.bind (M.runBehavioralFrom first fuel)).probOf
        {h | h ∉ (model.bind (M.runBehavioralFrom second fuel)).support} ≤
      actual.probOf {h | h ∉ model.support} +
        executionSupportCharge M first second fuel actual := by
  induction fuel generalizing actual model with
  | zero =>
      have zeroKernel (profile : Profile M.behavioralSignature) :
          M.runBehavioralFrom profile 0 = FinDist.pure := rfl
      simp only [zeroKernel, FinDist.bind_pure, executionSupportCharge, add_zero, le_refl]
  | succ fuel ih =>
      have splitRun (law : FinDist E.History) (profile : Profile M.behavioralSignature) :
          law.bind (M.runBehavioralFrom profile (fuel + 1)) =
            (law.bind (M.runBehavioralFrom profile 1)).bind (M.runBehavioralFrom profile fuel) := by
        rw [FinDist.bind_bind]
        apply FinDist.bind_congr
        intro h _
        simpa only [Nat.add_comm 1 fuel] using M.runBehavioralFrom_add profile 1 fuel h
      rw [splitRun, splitRun]
      have step := FinDist.probOf_bind_unsupported_le actual model
        (M.runBehavioralFrom first 1) (M.runBehavioralFrom second 1)
      exact (ih _ _).trans (by
        dsimp only [executionSupportCharge]
        linarith only [step])

/-- Support leakage is no larger than the existing full kernel-variation charge. -/
theorem executionSupportCharge_le_kernelCharge
    (first second : Profile M.behavioralSignature) (fuel : Nat)
    (actual : FinDist E.History) :
    executionSupportCharge M first second fuel actual ≤
      executionKernelCharge M first second fuel actual := by
  induction fuel generalizing actual with
  | zero => exact le_refl _
  | succ fuel ih =>
      apply add_le_add _ (ih _)
      apply FinDist.expect_mono
      intro h _
      exact FinDist.probOf_le_atomVariation_of_model_impossible _ _ _ (fun _ absent => absent)

/-- The incoming defect counts only histories outside the stored joint support.
The unknown opponent affects actual execution, never the stored model update. -/
def carriedOpponentSupportCharge {past : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals past) (actual : FinDist E.History)
    (chosen unknown : Profile M.behavioralSignature) (who : Fin 2) (fuel : Nat) : ℝ :=
  actual.probOf {h | h ∉ belief.law.support} +
    executionSupportCharge M (Profile.update unknown who (chosen who)) chosen fuel actual

/-- The support-specific allowance never exceeds the earlier source-law charge. -/
theorem carriedOpponentSupportCharge_le_modelCharge {past : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals past) (actual : FinDist E.History)
    (chosen unknown : Profile M.behavioralSignature) (who : Fin 2) (fuel : Nat) :
    carriedOpponentSupportCharge M belief actual chosen unknown who fuel ≤
      carriedOpponentModelCharge M belief actual chosen unknown who fuel :=
  add_le_add
    (FinDist.probOf_le_atomVariation_of_model_impossible _ _ _ (fun _ absent => absent))
    (executionSupportCharge_le_kernelCharge M _ chosen fuel actual)

omit [Fintype E.History] in
/-- The actual carried posterior failure has the support-specific rate, even
when the incoming actual weights differ from all positive model weights. -/
theorem carriedBeliefUpdate_failure_probability_le_supportCharge {past : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals past) (actual : FinDist E.History)
    (chosen unknown : Profile M.behavioralSignature) (who : Fin 2) (fuel : Nat) :
    (actual.bind (M.runBehavioralFrom (Profile.update unknown who (chosen who)) fuel)).probOf
      {history | ¬ ∃ next, carriedBeliefUpdate M (some belief) chosen fuel
        (publicTrace M.toInfoSignals history.trace) = some next ∧ history ∈ next.law.support} ≤
      carriedOpponentSupportCharge M belief actual chosen unknown who fuel := by
  apply (FinDist.probOf_le_probOf_unsupported _
    (PublicBelief.continuationLaw M chosen fuel belief) _ ?_).trans
      (runBehavioralFrom_unsupported_le M _ chosen fuel actual belief.law)
  intro history failed reached
  exact failed (carriedBeliefUpdate_contains_of_supported M belief chosen fuel history reached)

omit [Fintype E.History] in
/-- Supported incoming laws and support-dominated one-step execution incur no
support charge. Neither equality of laws nor equality of opponents is required. -/
theorem carriedOpponentSupportCharge_eq_zero_of_support {past : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals past) (actual : FinDist E.History)
    (chosen unknown : Profile M.behavioralSignature) (who : Fin 2) (fuel : Nat)
    (incoming : actual.support ⊆ belief.law.support)
    (steps : ∀ h, (M.runBehavioralFrom (Profile.update unknown who (chosen who)) 1 h).support ⊆
      (M.runBehavioralFrom chosen 1 h).support) :
    carriedOpponentSupportCharge M belief actual chosen unknown who fuel = 0 := by
  rw [carriedOpponentSupportCharge,
    FinDist.probOf_unsupported_eq_zero_of_support_subset actual belief.law incoming,
    executionSupportCharge_eq_zero_of_step_support_subset M _ chosen steps, add_zero]

end GameTheory.ReBeL
