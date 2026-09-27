/-
# Actual versus stored-model continuation transport

The stored PBS advances with the chosen MODEL profile. The actual continuation
replaces its opponent with an unknown legal policy. Their discrepancy is
computed from the incoming laws and one-step execution kernels along ACTUAL
visits, not assumed away by child Nash or by public posterior identification.
-/

import GameTheory.Math.Probability.FinDistKernelVariation
import GameTheory.Analysis.ReBeL.CFRDRecursivePlay

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

variable {K : Type*}

/-- The retained model posterior exists and contains the actual hidden history.
Unlike the sampling exception, this property also detects a missing belief. -/
def carriedStateSupported (state : PrivateIterationState M K) : Prop :=
  ∃ belief, state.belief = some belief ∧ state.history ∈ belief.law.support

/-- Support failure allowance for the actual randomized public resolver. Each
chosen profile stays paired with its own model update; model laws are not pooled.
Stopped stages retain their incoming defect, and a missing live belief costs one. -/
def carriedResolvedSupportCharge (resolver : CarriedPublicResolver M K)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (fuel : Nat)
    (state : PrivateIterationState M K) : ℝ := by
  classical
  exact if cfrDCutLive fuel state.history = true then
    match state.belief with
    | none => 1
    | some belief =>
        (resolver state.iteration (publicTrace M.toInfoSignals state.history.trace)
          (some belief)).expect (fun chosen =>
            carriedOpponentSupportCharge M belief (FinDist.pure state.history)
              chosen unknown who fuel)
  else if carriedStateSupported M state then 0 else 1

omit [Fintype E.History] in
/-- The full next private state, not merely its history marginal, satisfies the
computed support bound. No support inclusion, child Nash, or posterior identity
is supplied. The unknown legal opponent is arbitrary and unchanged by the draw. -/
theorem carriedResolvedStep_unsupported_le (plays : K → Profile M.behavioralSignature)
    (resolver : CarriedPublicResolver M K) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (fuel : Nat) (state : PrivateIterationState M K) :
    (carriedResolvedStep M plays resolver unknown who fuel state).probOf
        {next | ¬ carriedStateSupported M next} ≤
      carriedResolvedSupportCharge M resolver unknown who fuel state := by
  classical
  by_cases live : cfrDCutLive fuel state.history = true
  · cases stored : state.belief with
    | none =>
        rw [carriedResolvedSupportCharge, if_pos live, stored]
        rw [← FinDist.expect_indicator_eq_probOf]
        apply FinDist.expect_le_of_forall
        intro next _
        split_ifs <;> norm_num
    | some belief =>
        rw [carriedResolvedStep, if_pos live, carriedResolvedSupportCharge, if_pos live, stored]
        rw [← FinDist.expect_indicator_eq_probOf, FinDist.expect_bind]
        apply FinDist.expect_mono
        intro chosen _
        rw [FinDist.expect_map]
        have estimate := carriedBeliefUpdate_failure_probability_le_supportCharge M
          belief (FinDist.pure state.history) chosen unknown who fuel
        rw [FinDist.pure_bind, ← FinDist.expect_indicator_eq_probOf] at estimate
        simpa only [carriedStateSupported, resolvedNextState, stored, Set.mem_ofPred_eq]
          using estimate
  · rw [carriedResolvedStep, if_neg live, carriedResolvedSupportCharge, if_neg live]
    rw [← FinDist.expect_indicator_eq_probOf, FinDist.expect_pure]
    have stoppedBound :
        (if ¬ carriedStateSupported M state then (1 : ℝ) else 0) ≤
          if carriedStateSupported M state then 0 else 1 := by
      by_cases supported : carriedStateSupported M state <;> simp [supported]
    exact stoppedBound

omit [Fintype E.History] in
/-- At a live supported input, only the kernel leakage remains, averaged under
the native private resolver draw. Point-mass versus model weight differences
are not added back as a source-variation cost. -/
theorem carriedResolvedSupportCharge_of_supported
    (resolver : CarriedPublicResolver M K) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (fuel : Nat) (state : PrivateIterationState M K)
    (belief : PublicBelief M.toInfoSignals (publicTrace M.toInfoSignals state.history.trace))
    (live : cfrDCutLive fuel state.history = true) (stored : state.belief = some belief)
    (supported : state.history ∈ belief.law.support) :
    carriedResolvedSupportCharge M resolver unknown who fuel state =
      (resolver state.iteration (publicTrace M.toInfoSignals state.history.trace)
        (some belief)).expect (fun chosen =>
          executionSupportCharge M (Profile.update unknown who (chosen who)) chosen fuel
            (FinDist.pure state.history)) := by
  have incoming : (FinDist.pure state.history).support ⊆ belief.law.support := by
    intro history reached
    have same : history = state.history := FinDist.mem_support_pure.mp reached
    simpa only [same] using supported
  have vanished := FinDist.probOf_unsupported_eq_zero_of_support_subset
    (FinDist.pure state.history) belief.law incoming
  simp only [carriedResolvedSupportCharge, if_pos live, stored, carriedOpponentSupportCharge,
    vanished, zero_add]

omit [Fintype E.History] in
/-- Primitive support dominance is required only for profiles actually sampled
by this public resolver. It is not asserted for every unknown opponent or inferred
from finite-iteration equilibrium quality. Stopped supported states also cost zero. -/
theorem carriedResolvedSupportCharge_eq_zero_of_support
    (resolver : CarriedPublicResolver M K) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (fuel : Nat) (state : PrivateIterationState M K)
    (belief : PublicBelief M.toInfoSignals (publicTrace M.toInfoSignals state.history.trace))
    (stored : state.belief = some belief) (supported : state.history ∈ belief.law.support)
    (steps : ∀ chosen ∈ (resolver state.iteration
      (publicTrace M.toInfoSignals state.history.trace) (some belief)).support,
      ∀ h, (M.runBehavioralFrom (Profile.update unknown who (chosen who)) 1 h).support ⊆
        (M.runBehavioralFrom chosen 1 h).support) :
    carriedResolvedSupportCharge M resolver unknown who fuel state = 0 := by
  classical
  by_cases live : cfrDCutLive fuel state.history = true
  · rw [carriedResolvedSupportCharge_of_supported M resolver unknown who fuel state
      belief live stored supported]
    calc
      _ = (resolver state.iteration (publicTrace M.toInfoSignals state.history.trace)
          (some belief)).expect (fun _ => (0 : ℝ)) := by
        apply FinDist.expect_congr
        intro chosen sampled
        exact executionSupportCharge_eq_zero_of_step_support_subset M _ chosen
          (steps chosen sampled) fuel (FinDist.pure state.history)
      _ = 0 := FinDist.expect_const _ _
  · have valid : carriedStateSupported M state := ⟨belief, stored, supported⟩
    simp only [carriedResolvedSupportCharge, if_neg live, if_pos valid]

omit [Fintype E.History] in
/-- Flattening the newly chosen profile into retained memory preserves the same
support event. No posterior or private seed is resampled by this bookkeeping. -/
theorem carriedMemoryStep_unsupported_le (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K)
    (state : PrivateIterationState M (CarriedResolveMemory M K)) :
    (carriedMemoryStep M initial unknown who stage state).probOf
        {next | ¬ carriedStateSupported M next} ≤
      carriedResolvedSupportCharge M stage.resolver unknown who stage.fuel state := by
  rw [carriedMemoryStep, FinDist.probOf_map]
  exact carriedResolvedStep_unsupported_le M (carriedMemoryProfile M initial)
    stage.resolver unknown who stage.fuel state

omit [Fintype E.History] in
/-- An arbitrary incoming full-state law is averaged under its ACTUAL weights.
In particular, private memory may be correlated with both the hidden history
and its model PBS; no independent product of these marginals is introduced. -/
theorem carriedMemoryStep_law_unsupported_le (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : CarriedResolveStage M K)
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K))) :
    (states.bind (carriedMemoryStep M initial unknown who stage)).probOf
        {next | ¬ carriedStateSupported M next} ≤
      states.expect (carriedResolvedSupportCharge M stage.resolver unknown who stage.fuel) := by
  classical
  rw [← FinDist.expect_indicator_eq_probOf, FinDist.expect_bind]
  apply FinDist.expect_mono
  intro state _
  rw [FinDist.expect_indicator_eq_probOf]
  exact carriedMemoryStep_unsupported_le M initial unknown who stage state

/-- The primitive execution discrepancy and every actual-prefix contribution
are nonnegative, without any small-error hypothesis. -/
theorem executionKernelCharge_nonneg
    (first second : Profile M.behavioralSignature) (fuel : Nat)
    (actual : FinDist E.History) :
    0 ≤ executionKernelCharge M first second fuel actual := by
  induction fuel generalizing actual with
  | zero => exact le_refl _
  | succ fuel ih =>
      apply add_nonneg _ (ih _)
      calc
        0 = actual.expect (fun _ => (0 : ℝ)) := (FinDist.expect_const actual 0).symm
        _ ≤ _ := by
          apply FinDist.expect_mono
          intro history _
          exact FinDist.atomVariation_nonneg _ _

/-- Splitting a horizon preserves the actual checkpoint law in the remaining
execution charge. The model law is not substituted at the checkpoint. -/
theorem executionKernelCharge_add
    (first second : Profile M.behavioralSignature) (before after : Nat)
    (actual : FinDist E.History) :
    executionKernelCharge M first second (before + after) actual =
      executionKernelCharge M first second before actual +
        executionKernelCharge M first second after
          (actual.bind (M.runBehavioralFrom first before)) := by
  induction before generalizing actual with
  | zero =>
      have zeroKernel : M.runBehavioralFrom first 0 = FinDist.pure := rfl
      simp only [executionKernelCharge, zeroKernel, FinDist.bind_pure, zero_add]
  | succ before ih =>
      have checkpoint :
          actual.bind (M.runBehavioralFrom first (before + 1)) =
            (actual.bind (M.runBehavioralFrom first 1)).bind
              (M.runBehavioralFrom first before) := by
        rw [FinDist.bind_bind]
        apply FinDist.bind_congr
        intro history _
        simpa only [Nat.add_comm 1 before] using
          M.runBehavioralFrom_add first 1 before history
      rw [Nat.succ_add]
      simp only [executionKernelCharge]
      rw [ih, checkpoint]
      exact (add_assoc _ _ _).symm

/-- A primitive bound on each one-step canonical kernel supplies a linear
fuel allowance. Smallness must be established for these kernels themselves. -/
theorem executionKernelCharge_le_mul
    (first second : Profile M.behavioralSignature) (rate : ℝ)
    (steps : ∀ history, FinDist.atomVariation
      (M.runBehavioralFrom first 1 history) (M.runBehavioralFrom second 1 history) ≤ rate)
    (fuel : Nat) (actual : FinDist E.History) :
    executionKernelCharge M first second fuel actual ≤ (fuel : ℝ) * rate := by
  induction fuel generalizing actual with
  | zero => simp only [executionKernelCharge, Nat.cast_zero, zero_mul, le_refl]
  | succ fuel ih =>
      calc
        _ ≤ rate + (fuel : ℝ) * rate := by
          apply add_le_add _ (ih _)
          apply FinDist.expect_le_of_forall
          intro history _
          exact steps history
        _ = ((fuel + 1 : Nat) : ℝ) * rate := by push_cast; ring

/-- Incoming source variation and primitive opponent/model kernel rates remain
separate. A supported but differently weighted incoming law is not set to zero. -/
theorem carriedOpponentModelCharge_le_rate {past : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals past) (actual : FinDist E.History)
    (chosen unknown : Profile M.behavioralSignature) (who : Fin 2)
    (incoming rate : ℝ)
    (initial : FinDist.atomVariation actual belief.law ≤ incoming)
    (steps : ∀ history, FinDist.atomVariation
      (M.runBehavioralFrom (Profile.update unknown who (chosen who)) 1 history)
      (M.runBehavioralFrom chosen 1 history) ≤ rate)
    (fuel : Nat) :
    carriedOpponentModelCharge M belief actual chosen unknown who fuel ≤
      incoming + (fuel : ℝ) * rate :=
  add_le_add initial (executionKernelCharge_le_mul M _ chosen rate steps fuel actual)

omit [Fintype E.History] in
/-- The carried update is the certified MODEL posterior of the chosen
continuation at every model-supported public observation. -/
theorem carriedBeliefUpdate_eq_atObservation {past : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals past) (chosen : Profile M.behavioralSignature)
    (fuel : Nat) (observed : List M.PublicSignal)
    (positive : observed ∈ (PublicBelief.publicLaw (S := M.toInfoSignals)
      (PublicBelief.continuationLaw M chosen fuel belief)).support) :
    carriedBeliefUpdate M (some belief) chosen fuel observed =
      some (PublicBelief.atObservation
        (PublicBelief.continuationLaw M chosen fuel belief) observed positive) := by
  classical
  exact dif_pos ((PublicBelief.possible_iff_mem_publicLaw _ _).mpr positive)

omit [Fintype E.History] in
/-- The actual recursive step stores this certified model posterior. The
factual history determines only its public observation; it never resets the PBS. -/
theorem resolvedNextState_belief_eq_atObservation
    (state : PrivateIterationState M K)
    (belief : PublicBelief M.toInfoSignals (publicTrace M.toInfoSignals state.history.trace))
    (stored : state.belief = some belief)
    (chosen : Profile M.behavioralSignature) (fuel : Nat) (history : E.History)
    (positive : publicTrace M.toInfoSignals history.trace ∈
      (PublicBelief.publicLaw (S := M.toInfoSignals)
        (PublicBelief.continuationLaw M chosen fuel belief)).support) :
    (resolvedNextState M state chosen fuel history).belief =
      some (PublicBelief.atObservation
        (PublicBelief.continuationLaw M chosen fuel belief)
        (publicTrace M.toInfoSignals history.trace) positive) := by
  simpa only [resolvedNextState, stored] using
    carriedBeliefUpdate_eq_atObservation M belief chosen fuel
      (publicTrace M.toInfoSignals history.trace) positive

/-- Primitive source and canonical execution rates control the mean
conditional defect under the actual public law, including absent model queries.
No lower bound on public reach and no posterior equality are assumed. -/
theorem carriedOpponentModel_public_transport_le_rate {past : List M.PublicSignal}
    (belief : PublicBelief M.toInfoSignals past) (actual : FinDist E.History)
    (chosen unknown : Profile M.behavioralSignature) (who : Fin 2)
    (incoming rate : ℝ)
    (initial : FinDist.atomVariation actual belief.law ≤ incoming)
    (steps : ∀ history, FinDist.atomVariation
      (M.runBehavioralFrom (Profile.update unknown who (chosen who)) 1 history)
      (M.runBehavioralFrom chosen 1 history) ≤ rate)
    (fuel : Nat) :
    let realLaw := actual.bind
      (M.runBehavioralFrom (Profile.update unknown who (chosen who)) fuel)
    let modelLaw := PublicBelief.continuationLaw M chosen fuel belief
    (PublicBelief.publicLaw (S := M.toInfoSignals) realLaw).expect
      (FinDist.conditionalTransportDefect realLaw modelLaw
        (fun history => publicTrace M.toInfoSignals history.trace)) ≤
      2 * (incoming + (fuel : ℝ) * rate) := by
  exact (carriedOpponentModelCharge_controls_public_transport M belief actual chosen
    unknown who fuel).trans (mul_le_mul_of_nonneg_left
      (carriedOpponentModelCharge_le_rate M belief actual chosen unknown who
        incoming rate initial steps fuel) (by norm_num))

end GameTheory.ReBeL
