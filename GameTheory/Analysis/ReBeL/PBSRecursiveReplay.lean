/-
# Replay of the actual recursive child

The same deterministic child computation has an equivalent private-iterate
draw at each supported root, against every unknown opponent. Parent table
replay keeps the factual joint PBS and its mass-scaled tolerance exactly.
This does not identify a later carried model PBS with that factual child.
-/

import GameTheory.Analysis.ReBeL.PBSRecursiveDepth
import GameTheory.Analysis.ReBeL.PBSSupportedSampling
import GameTheory.Math.Probability.FinDistEventError

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable (noise : PBSRecursiveDepthNoise.{u}) (cuts : List Nat)
variable (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
variable (bound : ℝ) {obs : List M.PublicSignal}

/-- Delay the single private draw until after sampling the incoming root. -/
theorem pbsRecursiveDepthDraw_delayed
    (belief : PublicBelief (fullInformation M).toInfoSignals obs) (tolerance : ℝ)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat) :
    belief.law.bind (fun history =>
      (pbsRecursiveDepthDraw noise cuts M fallback payoff bound belief tolerance).bind
        (fun chosen => (fullInformation M).runBehavioralFrom
          (Profile.update unknown who (chosen who)) steps history)) =
      belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance who))
        steps) := by
  rw [FinDist.bind_comm]
  exact pbsRecursiveDepthDraw_law noise cuts M fallback payoff bound belief tolerance
    unknown who steps

/-- Root prefixes separate the actual model mixture into pointwise laws.
Neither Nash accuracy nor equality of actual and model probabilities is needed. -/
theorem pbsRecursiveDepthDraw_from_support
    (belief : PublicBelief (fullInformation M).toInfoSignals obs) (tolerance : ℝ)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (history : E.History) (supported : history ∈ belief.law.support) :
    (pbsRecursiveDepthDraw noise cuts M fallback payoff bound belief tolerance).bind
      (fun chosen => (fullInformation M).runBehavioralFrom
        (Profile.update unknown who (chosen who)) steps history) =
      (fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance who))
        steps history :=
  pbsPublicBelief_sampling_from_support M belief
    (pbsRecursiveDepthDraw noise cuts M fallback payoff bound belief tolerance)
    (fun chosen => Profile.update unknown who (chosen who))
    (Profile.update unknown who
      (pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance who)) steps
    (pbsRecursiveDepthDraw_delayed M noise cuts fallback payoff bound belief tolerance
      unknown who steps) history supported

/-- Actual root weights may be arbitrarily reweighted inside model support. -/
theorem pbsRecursiveDepthDraw_reweighted
    (belief : PublicBelief (fullInformation M).toInfoSignals obs) (tolerance : ℝ)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (actual : FinDist E.History)
    (dominated : ∀ history ∈ actual.support, history ∈ belief.law.support) :
    actual.bind (fun history =>
      (pbsRecursiveDepthDraw noise cuts M fallback payoff bound belief tolerance).bind
        (fun chosen => (fullInformation M).runBehavioralFrom
          (Profile.update unknown who (chosen who)) steps history)) =
      actual.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance who))
        steps) := by
  apply FinDist.bind_congr
  intro history sampled
  exact pbsRecursiveDepthDraw_from_support M noise cuts fallback payoff bound belief tolerance
    unknown who steps history (dominated history sampled)

/-- Off-support roots are charged under the actual law, without asserting
that the probability is small or that the unknown opponent follows the model. -/
theorem pbsRecursiveDepthDraw_actual_error
    (belief : PublicBelief (fullInformation M).toInfoSignals obs) (tolerance : ℝ)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (actual : FinDist E.History) (value : E.History → ℝ) (limit : ℝ)
    (bounded : ∀ history, |value history| ≤ limit) :
    |(actual.bind (fun history =>
        (pbsRecursiveDepthDraw noise cuts M fallback payoff bound belief tolerance).bind
          (fun chosen => (fullInformation M).runBehavioralFrom
            (Profile.update unknown who (chosen who)) steps history))).expect value -
      (actual.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance who))
        steps)).expect value| ≤
      2 * limit * actual.probOf {history | history ∉ belief.law.support} := by
  apply FinDist.abs_expect_bind_sub_le_of_eq_off_event
  · exact bounded
  · intro history _ outside
    exact pbsRecursiveDepthDraw_from_support M noise cuts fallback payoff bound belief tolerance
      unknown who steps history (not_not.mp outside)

omit [Fintype E.History] [∀ who, Fintype (E.Action who)] in
/-- The focal player's actual public splice retains the chosen child on every
legal descendant. The other player remains the same unknown policy. -/
theorem cfrDComposedChildProfile_unilateral_from
    (trunk : Profile (fullInformation M).behavioralSignature)
    (cut remaining : Nat) (loss : ℝ) (solve : PBSChildSolve M)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (first : E.History) (atCut : first.trace.length = cut) (fuel : Nat) :
    (fullInformation M).runBehavioralFrom
      (Profile.update unknown who
        (cfrDComposedChildProfile M trunk fallback cut remaining loss solve who)) fuel first =
      (fullInformation M).runBehavioralFrom
        (Profile.update unknown who (cfrDComposedChildTable M trunk fallback cut remaining
          loss solve (publicTrace M.toInfoSignals first.trace) who)) fuel first := by
  apply (fullInformation M).runBehavioralFrom_congr
  intro later reaches _ player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    exact cfrDComposedChildProfile_of_reaches M trunk fallback cut remaining loss solve
      who first later atCut reaches
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]

/-- Replay the EXACT recursive computation used in a possible parent-table
entry. Its tolerance includes the factual joint-law mass floor; replacing it
by the unscaled parent loss would describe a different computation. -/
theorem pbsRecursiveDepthDraw_composed_child
    (trunk : Profile (fullInformation M).behavioralSignature)
    (cut remaining : Nat) (loss : ℝ)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (first : E.History)
    (supported : first ∈ (cfrDFactualChildBelief M trunk cut remaining obs possible).law.support)
    (fuel : Nat) :
    (pbsRecursiveDepthDraw noise cuts M fallback payoff bound
      (cfrDFactualChildBelief M trunk cut remaining obs possible)
      ((cfrDFactualChildBelief M trunk cut remaining obs possible).law.positiveMassFloor *
        loss)).bind (fun chosen => (fullInformation M).runBehavioralFrom
          (Profile.update unknown who (chosen who)) fuel first) =
      (fullInformation M).runBehavioralFrom
        (Profile.update unknown who (cfrDComposedChildProfile M trunk fallback cut remaining
          loss (pbsRecursiveDepth noise cuts E M fallback payoff bound) who)) fuel first := by
  let belief := cfrDFactualChildBelief M trunk cut remaining obs possible
  have rootPublic := belief.supported first supported
  rw [publicRoot_trace_eq] at rootPublic
  rw [cfrDComposedChildProfile_unilateral_from M fallback trunk cut remaining loss
    (pbsRecursiveDepth noise cuts E M fallback payoff bound) unknown who first
    (cfrDFactualChildBelief_atCut M trunk cut remaining obs possible first supported) fuel]
  rw [rootPublic]
  have table :
      cfrDComposedChildTable M trunk fallback cut remaining loss
        (pbsRecursiveDepth noise cuts E M fallback payoff bound) obs =
      pbsRecursiveDepth noise cuts E M fallback payoff bound belief
        (belief.law.positiveMassFloor * loss) := by
    simp only [cfrDComposedChildTable, dif_pos possible, belief]
  rw [table]
  exact pbsRecursiveDepthDraw_from_support M noise cuts fallback payoff bound belief
    (belief.law.positiveMassFloor * loss) unknown who fuel first supported

/-- The replay identity survives arbitrary actual probabilities on the factual
child support, including a private-type conditioning. The full late fuel is free. -/
theorem pbsRecursiveDepthDraw_composed_reweighted
    (trunk : Profile (fullInformation M).behavioralSignature)
    (cut remaining : Nat) (loss : ℝ)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (actual : FinDist E.History)
    (dominated : ∀ history ∈ actual.support,
      history ∈ (cfrDFactualChildBelief M trunk cut remaining obs possible).law.support)
    (fuel : Nat) :
    actual.bind (fun history =>
      (pbsRecursiveDepthDraw noise cuts M fallback payoff bound
        (cfrDFactualChildBelief M trunk cut remaining obs possible)
        ((cfrDFactualChildBelief M trunk cut remaining obs possible).law.positiveMassFloor *
          loss)).bind (fun chosen => (fullInformation M).runBehavioralFrom
            (Profile.update unknown who (chosen who)) fuel history)) =
      actual.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (cfrDComposedChildProfile M trunk fallback cut remaining
          loss (pbsRecursiveDepth noise cuts E M fallback payoff bound) who)) fuel) := by
  apply FinDist.bind_congr
  intro history sampled
  exact pbsRecursiveDepthDraw_composed_child M noise cuts fallback payoff bound trunk
    cut remaining loss possible unknown who history (dominated history sampled) fuel

variable [∀ who info, Fintype ((fullInformation M).Choice who info)]

/-- The actual parent's off-path completion preserves the focal player's
entire law against every unknown opponent from the original initial history.
This is a reach-factorization result, not a support assumption on the opponent. -/
theorem cfrDComposedChildContinuation_unilateral_run
    (trunk : Profile (fullInformation M).behavioralSignature)
    (cut remaining : Nat) (loss : ℝ) (solve : PBSChildSolve M)
    (utility : E.History → Fin 2 → ℝ)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (horizon : Nat) :
    (fullInformation M).runBehavioral
      (Profile.update unknown who
        (cfrDComposedChildContinuation M trunk fallback cut remaining loss solve utility who))
      horizon =
    (fullInformation M).runBehavioral
      (Profile.update unknown who
        (cfrDComposedChildProfile M trunk fallback cut remaining loss solve who)) horizon := by
  unfold cfrDComposedChildContinuation
  exact cfrDCompleteZeroReach_unilateral_run (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals) _ _ unknown who horizon

end GameTheory.ReBeL
