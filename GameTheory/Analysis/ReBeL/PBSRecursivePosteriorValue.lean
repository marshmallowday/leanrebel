/-
# Recomputed recursive policies at saved and live posteriors

Filtering stopped mass and rerunning a solver are different operations.
The signed policy term below uses the two actual recursive computations,
including their separate budgets. No continuity of the solver is assumed.
-/

import GameTheory.Analysis.ReBeL.CFRDStoredChildDefect
import GameTheory.Analysis.ReBeL.PBSRecursiveCarriedReplay

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)

/-- The signed change in continuation value under one fixed incoming law.
Both profiles are explicit; closeness of their Nash gaps is not an input. -/
def recursivePolicyValueChange
    (first second unknown : Profile (fullInformation M).behavioralSignature)
    (who : Fin 2) (fuel : Nat) (law : FinDist E.History) (value : E.History → ℝ) : ℝ :=
  law.expect (fun history =>
    ((fullInformation M).runBehavioralFrom
      (Profile.update unknown who (first who)) fuel history).expect value -
    ((fullInformation M).runBehavioralFrom
      (Profile.update unknown who (second who)) fuel history).expect value)

variable [Fintype E.History]

/-- An independently measured execution discrepancy bounds the signed term.
The prefix inside this charge follows the FIRST compared policy. -/
theorem recursivePolicyValueChange_abs_le
    (first second unknown : Profile (fullInformation M).behavioralSignature)
    (who : Fin 2) (fuel : Nat) (law : FinDist E.History) (value : E.History → ℝ)
    (limit : ℝ) (nonneg : 0 ≤ limit) (bounded : ∀ h, |value h| ≤ limit) :
    |recursivePolicyValueChange M first second unknown who fuel law value| ≤
      limit * executionKernelCharge (fullInformation M)
        (Profile.update unknown who (first who))
        (Profile.update unknown who (second who)) fuel law := by
  have distance := runBehavioralFrom_atomVariation_le (fullInformation M)
    (Profile.update unknown who (first who)) (Profile.update unknown who (second who))
    fuel law law
  rw [FinDist.atomVariation_self, zero_add] at distance
  have estimate := (FinDist.abs_expect_sub_le_atomVariation
    (law.bind ((fullInformation M).runBehavioralFrom
      (Profile.update unknown who (first who)) fuel))
    (law.bind ((fullInformation M).runBehavioralFrom
      (Profile.update unknown who (second who)) fuel))
    value limit bounded).trans (mul_le_mul_of_nonneg_left distance nonneg)
  simpa only [recursivePolicyValueChange, FinDist.expect_sub, FinDist.expect_bind] using estimate

omit [Fintype E.History] in
/-- With changed policies the posterior-only estimate controls the residual
AFTER retaining the signed policy term. It cannot discard that term. -/
theorem cfrDFactualChild_changedPolicy_residual
    (trunk first second unknown : Profile (fullInformation M).behavioralSignature)
    (cut remaining : Nat) (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs)
    (who : Fin 2) (fuel : Nat) (value : E.History → ℝ)
    (limit : ℝ) (bounded : ∀ h, |value h| ≤ limit) :
    let saved := PublicBelief.condition (S := (fullInformation M).toInfoSignals)
      ((fullInformation M).runBehavioral trunk cut) obs
      (cfrDFactualChildPossible_public M trunk cut remaining obs possible)
    let child := cfrDFactualChildBelief M trunk cut remaining obs possible
    |((saved.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (first who)) fuel)).expect value -
      (child.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (second who)) fuel)).expect value) -
      recursivePolicyValueChange M first second unknown who fuel child.law value| ≤
      2 * limit * (((fullInformation M).runBehavioral trunk cut).probOf
        {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs ∧
          cfrDCutLive remaining h ≠ true} /
        ((fullInformation M).runBehavioral trunk cut).probOf
          {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs}) := by
  intro saved child
  have estimate := cfrDFactualChild_public_continuation_error M trunk cut remaining obs
    possible ((fullInformation M).runBehavioralFrom
      (Profile.update unknown who (first who)) fuel) value limit bounded
  have identity :
      ((saved.law.bind ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who (first who)) fuel)).expect value -
        (child.law.bind ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who (second who)) fuel)).expect value) -
        recursivePolicyValueChange M first second unknown who fuel child.law value =
      (saved.law.bind ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who (first who)) fuel)).expect value -
        (child.law.bind ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who (first who)) fuel)).expect value := by
    simp only [recursivePolicyValueChange, FinDist.expect_sub, FinDist.expect_bind]
    ring
  rw [identity]
  exact estimate

variable [∀ who, Fintype (E.Action who)]

/-- Both sides now use the actual recursive private draws on their respective
PBSs. The same draw is used through all fuel, including late continuation.
The saved tolerance and factual mass-scaled tolerance are kept distinct. -/
theorem pbsRecursiveDepthDraw_public_child_residual
    (noise : PBSRecursiveDepthNoise.{u}) (cuts : List Nat)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (bound publicTolerance loss : ℝ)
    (trunk unknown : Profile (fullInformation M).behavioralSignature)
    (cut remaining : Nat) (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs)
    (who : Fin 2) (fuel : Nat) (value : E.History → ℝ)
    (limit : ℝ) (bounded : ∀ h, |value h| ≤ limit) :
    let saved := PublicBelief.condition (S := (fullInformation M).toInfoSignals)
      ((fullInformation M).runBehavioral trunk cut) obs
      (cfrDFactualChildPossible_public M trunk cut remaining obs possible)
    let child := cfrDFactualChildBelief M trunk cut remaining obs possible
    let childTolerance := child.law.positiveMassFloor * loss
    |((pbsRecursiveDepthDraw noise cuts M fallback payoff bound saved publicTolerance).expect
        (fun chosen => (saved.law.bind ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who (chosen who)) fuel)).expect value) -
      (pbsRecursiveDepthDraw noise cuts M fallback payoff bound child childTolerance).expect
        (fun chosen => (child.law.bind ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who (chosen who)) fuel)).expect value)) -
      recursivePolicyValueChange M
        (pbsRecursiveDepth noise cuts E M fallback payoff bound saved publicTolerance)
        (pbsRecursiveDepth noise cuts E M fallback payoff bound child childTolerance)
        unknown who fuel child.law value| ≤
      2 * limit * (((fullInformation M).runBehavioral trunk cut).probOf
        {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs ∧
          cfrDCutLive remaining h ≠ true} /
        ((fullInformation M).runBehavioral trunk cut).probOf
          {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs}) := by
  intro saved child childTolerance
  rw [pbsRecursiveDepthDraw_value, pbsRecursiveDepthDraw_value]
  exact cfrDFactualChild_changedPolicy_residual M trunk
    (pbsRecursiveDepth noise cuts E M fallback payoff bound saved publicTolerance)
    (pbsRecursiveDepth noise cuts E M fallback payoff bound child childTolerance)
    unknown cut remaining obs possible who fuel value limit bounded

end GameTheory.ReBeL
