/-
# Consuming the actual parent's stored child posterior

The same protocol's played composed round propagates its model posterior.
Publicly visible termination identifies that posterior with its factual live
child, so the existing recursive resolver consumes the exact child input.
Matching the rooted and original protocols across successive solves is separate.
-/

import GameTheory.Analysis.ReBeL.CFRDStoredChild
import GameTheory.Analysis.ReBeL.PBSRecursiveReplay

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]
variable [∀ who, DecidableEq ((fullInformation M).InfoState who)]
variable (recursiveNoise : PBSRecursiveDepthNoise.{u}) (cuts : List Nat)
variable (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
variable (bound : ℝ) {K : Type*}

/-- A stored MODEL posterior from the actual noisy parent is the exact input
to a matched recursive replay. The target remains the parent's mass-scaled
request; an independently fixed tolerance would be another computation. -/
theorem pbsRecursiveResolver_composed_input
    (observable : PubliclyObservableTermination M)
    (cut remaining : Nat) (loss : ℝ) (noise : CFRDPredictionNoise M) (round : Nat)
    (state : PrivateIterationState (fullInformation M) K)
    (prior : PublicBelief (fullInformation M).toInfoSignals
      (publicTrace (fullInformation M).toInfoSignals state.history.trace))
    (stored : state.belief = some prior) (initial : prior.law = FinDist.pure E.initHistory)
    (history : E.History)
    (possible : CFRDFactualChildPossible M
      (cfrDComposedTrunk M fallback payoff cut remaining loss
        (pbsRecursiveDepth recursiveNoise cuts E M fallback payoff bound) noise round)
      cut remaining (publicTrace M.toInfoSignals history.trace))
    (plays : (K × Profile (fullInformation M).behavioralSignature) →
      Profile (fullInformation M).behavioralSignature) :
    let solve := pbsRecursiveDepth recursiveNoise cuts E M fallback payoff bound
    let trunk := cfrDComposedTrunk M fallback payoff cut remaining loss solve noise round
    let child := cfrDFactualChildBelief M trunk cut remaining
      (publicTrace M.toInfoSignals history.trace) possible
    let next := cfrDComposedNextState M fallback payoff cut remaining loss solve noise round
      state history
    next.belief = some child ∧
      pbsRecursiveDepthResolver recursiveNoise cuts M fallback payoff bound
        (child.law.positiveMassFloor * loss) plays next.iteration
        (publicTrace M.toInfoSignals history.trace) next.belief =
      pbsRecursiveDepthDraw recursiveNoise cuts M fallback payoff bound child
        (child.law.positiveMassFloor * loss) := by
  intro solve trunk child next
  have same : next.belief = some child :=
    cfrDComposedRound_storedChild M observable fallback payoff cut remaining loss solve
      noise round state prior stored initial history possible
  refine ⟨same, ?_⟩
  rw [same]
  rfl

/-- The concrete matched resolver, using the actual stored posterior, replays
the parent's factual child against an arbitrary fixed unknown opponent.
History support is explicit; positivity of the public observation alone does
not ensure an actual hidden history lies in the modeled joint support. -/
theorem pbsRecursiveResolver_composed_law
    (observable : PubliclyObservableTermination M)
    (cut remaining : Nat) (loss : ℝ) (noise : CFRDPredictionNoise M) (round : Nat)
    (state : PrivateIterationState (fullInformation M) K)
    (prior : PublicBelief (fullInformation M).toInfoSignals
      (publicTrace (fullInformation M).toInfoSignals state.history.trace))
    (stored : state.belief = some prior) (initial : prior.law = FinDist.pure E.initHistory)
    (history : E.History)
    (possible : CFRDFactualChildPossible M
      (cfrDComposedTrunk M fallback payoff cut remaining loss
        (pbsRecursiveDepth recursiveNoise cuts E M fallback payoff bound) noise round)
      cut remaining (publicTrace M.toInfoSignals history.trace))
    (supported : history ∈ (cfrDFactualChildBelief M
      (cfrDComposedTrunk M fallback payoff cut remaining loss
        (pbsRecursiveDepth recursiveNoise cuts E M fallback payoff bound) noise round)
      cut remaining (publicTrace M.toInfoSignals history.trace) possible).law.support)
    (plays : (K × Profile (fullInformation M).behavioralSignature) →
      Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (fuel : Nat) :
    let solve := pbsRecursiveDepth recursiveNoise cuts E M fallback payoff bound
    let trunk := cfrDComposedTrunk M fallback payoff cut remaining loss solve noise round
    let child := cfrDFactualChildBelief M trunk cut remaining
      (publicTrace M.toInfoSignals history.trace) possible
    let next := cfrDComposedNextState M fallback payoff cut remaining loss solve noise round
      state history
    (pbsRecursiveDepthResolver recursiveNoise cuts M fallback payoff bound
      (child.law.positiveMassFloor * loss) plays next.iteration
      (publicTrace M.toInfoSignals history.trace) next.belief).bind (fun chosen =>
        (fullInformation M).runBehavioralFrom
          (Profile.update unknown who (chosen who)) fuel history) =
      (fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (cfrDComposedChildProfile M trunk fallback cut remaining loss solve who))
        fuel history := by
  intro solve trunk child next
  have input := (pbsRecursiveResolver_composed_input M recursiveNoise cuts fallback payoff bound
    observable cut remaining loss noise round state prior stored initial history possible plays).2
  rw [input]
  exact pbsRecursiveDepthDraw_composed_child M recursiveNoise cuts fallback payoff bound
    trunk cut remaining loss possible unknown who history supported fuel

/-- Every bounded or unbounded real observable inherits the exact supported
law equality. The fuel may include stage plus late continuation under one draw. -/
theorem pbsRecursiveResolver_composed_value
    (observable : PubliclyObservableTermination M)
    (cut remaining : Nat) (loss : ℝ) (noise : CFRDPredictionNoise M) (round : Nat)
    (state : PrivateIterationState (fullInformation M) K)
    (prior : PublicBelief (fullInformation M).toInfoSignals
      (publicTrace (fullInformation M).toInfoSignals state.history.trace))
    (stored : state.belief = some prior) (initial : prior.law = FinDist.pure E.initHistory)
    (history : E.History)
    (possible : CFRDFactualChildPossible M
      (cfrDComposedTrunk M fallback payoff cut remaining loss
        (pbsRecursiveDepth recursiveNoise cuts E M fallback payoff bound) noise round)
      cut remaining (publicTrace M.toInfoSignals history.trace))
    (supported : history ∈ (cfrDFactualChildBelief M
      (cfrDComposedTrunk M fallback payoff cut remaining loss
        (pbsRecursiveDepth recursiveNoise cuts E M fallback payoff bound) noise round)
      cut remaining (publicTrace M.toInfoSignals history.trace) possible).law.support)
    (plays : (K × Profile (fullInformation M).behavioralSignature) →
      Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (fuel : Nat)
    (value : E.History → ℝ) :
    let solve := pbsRecursiveDepth recursiveNoise cuts E M fallback payoff bound
    let trunk := cfrDComposedTrunk M fallback payoff cut remaining loss solve noise round
    let child := cfrDFactualChildBelief M trunk cut remaining
      (publicTrace M.toInfoSignals history.trace) possible
    let next := cfrDComposedNextState M fallback payoff cut remaining loss solve noise round
      state history
    (pbsRecursiveDepthResolver recursiveNoise cuts M fallback payoff bound
      (child.law.positiveMassFloor * loss) plays next.iteration
      (publicTrace M.toInfoSignals history.trace) next.belief).expect (fun chosen =>
        ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who (chosen who)) fuel history).expect value) =
      ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (cfrDComposedChildProfile M trunk fallback cut remaining loss solve who))
        fuel history).expect value := by
  have equal := congrArg (fun law : FinDist E.History => law.expect value)
    (pbsRecursiveResolver_composed_law M recursiveNoise cuts fallback payoff bound observable
      cut remaining loss noise round state prior stored initial history possible supported
      plays unknown who fuel)
  simpa only [FinDist.expect_bind] using equal

end GameTheory.ReBeL
