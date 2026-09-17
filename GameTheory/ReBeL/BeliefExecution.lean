/-
# Executing from a public belief

A referee first samples information-local legal actions and the canonical
transition, then samples the new public observation and keeps its joint
posterior. Iterating this operation has exactly the original history law.
No equilibrium or outcome equivalence is assumed as an input field.
-/

import GameTheory.ReBeL.Belief
import GameTheory.ReBeL.Payoff

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

namespace PublicBelief

variable [Fintype ι] (M : InformationModel E)

/-- The belief-game state retains its public-history index and joint law. -/
abbrev State := Σ p, PublicBelief M.toInfoSignals p

/-- The reference continuation samples a root history, then runs the original protocol. -/
def continuationLaw (profile : Profile M.behavioralSignature) (fuel : Nat)
    {p : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals p) : FinDist E.History :=
  belief.law.bind (M.runBehavioralFrom profile fuel)

@[simp]
theorem continuationLaw_zero (profile : Profile M.behavioralSignature)
    {p : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals p) :
    continuationLaw M profile 0 belief = belief.law :=
  FinDist.bind_pure belief.law

/-- The actual Bayes/referee step, including legal action and chance sampling.
Terminal branches remain absorbing through the canonical runner. -/
def update (profile : Profile M.behavioralSignature) (belief : State M) : FinDist (State M) :=
  split (continuationLaw M profile 1 belief.2)

/-- Iterate public transitions. The zero-fuel result is a cut, not necessarily terminal. -/
def run (profile : Profile M.behavioralSignature) : Nat → State M → FinDist (State M)
  | 0, belief => FinDist.pure belief
  | fuel + 1, belief => (update M profile belief).bind (run profile fuel)

/-- One Bayesian update commutes with the actual one-step history execution. -/
theorem update_law (profile : Profile M.behavioralSignature) (belief : State M) :
    (update M profile belief).bind (fun next => next.2.law) =
      continuationLaw M profile 1 belief.2 :=
  split_bind_law _

/-- Full outcome-law preservation is derived by induction and disintegration. -/
theorem run_law (profile : Profile M.behavioralSignature) (fuel : Nat) (belief : State M) :
    (run M profile fuel belief).bind (fun next => next.2.law) =
      continuationLaw M profile fuel belief.2 := by
  induction fuel generalizing belief with
  | zero => simp only [run, FinDist.pure_bind, continuationLaw_zero]
  | succ fuel ih =>
      rw [run, FinDist.bind_bind]
      calc
        (update M profile belief).bind
            (fun next => (run M profile fuel next).bind (fun last => last.2.law)) =
            (update M profile belief).bind
              (fun next => continuationLaw M profile fuel next.2) :=
          FinDist.bind_congr fun next _ => ih next
        _ = (continuationLaw M profile 1 belief.2).bind
              (M.runBehavioralFrom profile fuel) :=
          split_bind_continuation _ _
        _ = continuationLaw M profile (fuel + 1) belief.2 := by
          rw [continuationLaw, FinDist.bind_bind]
          apply FinDist.bind_congr
          intro root _
          simpa only [Nat.add_comm] using (M.runBehavioralFrom_add profile 1 fuel root).symm

/-- Every real outcome observable is preserved, not only the game's chosen utility. -/
theorem run_expect (profile : Profile M.behavioralSignature) (fuel : Nat)
    (belief : State M) (observable : E.History → ℝ) :
    (run M profile fuel belief).expect (fun next => next.2.law.expect observable) =
      (continuationLaw M profile fuel belief.2).expect observable := by
  rw [← FinDist.expect_bind, run_law]

/-- Future expected reward is the PBS average of canonical history continuation values. -/
def futureValue (reward : StageReward E) (profile : Profile M.behavioralSignature)
    (fuel : Nat) {p : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals p)
    (i : ι) : ℝ :=
  belief.law.expect (fun root => continuationValue M reward fuel profile root i)

/-- Removing expected past reward gives exactly the canonical future-reward convention. -/
theorem futureValue_eq_difference (reward : StageReward E)
    (profile : Profile M.behavioralSignature) (fuel : Nat)
    {p : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals p) (i : ι) :
    futureValue M reward profile fuel belief i =
      (continuationLaw M profile fuel belief).expect (fun h => cumulativeUtility reward h i) -
        belief.law.expect (fun h => cumulativeUtility reward h i) := by
  unfold futureValue continuationValue expectedUtility futureUtility continuationLaw
  simp only [FinDist.expect_sub, FinDist.expect_const, FinDist.expect_bind]

/-- Referee execution preserves the expected future reward, after the outcome law proof. -/
theorem run_futureValue (reward : StageReward E)
    (profile : Profile M.behavioralSignature) (fuel : Nat) (belief : State M) (i : ι) :
    (run M profile fuel belief).expect
        (fun next => next.2.law.expect (fun h => cumulativeUtility reward h i)) -
        belief.2.law.expect (fun h => cumulativeUtility reward h i) =
      futureValue M reward profile fuel belief.2 i := by
  rw [run_expect, futureValue_eq_difference]

/-- A supported terminal root requires no prescribed action, even at positive fuel. -/
theorem continuationLaw_of_terminal (profile : Profile M.behavioralSignature) (fuel : Nat)
    {p : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals p)
    (terminal : ∀ h ∈ belief.law.support, E.terminal h.state) :
    continuationLaw M profile fuel belief = belief.law := by
  exact (FinDist.bind_congr fun h hh => M.runBehavioralFrom_of_terminal profile fuel
    (terminal h hh)).trans (FinDist.bind_pure _)

/-- A proved horizon, rather than fuel exhaustion alone, certifies terminal outcomes. -/
theorem continuationLaw_terminal_of_bound (profile : Profile M.behavioralSignature)
    {bound : Nat} (bounded : E.BoundedHorizon bound)
    {p : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals p)
    (h : E.History) (positive : h ∈ (continuationLaw M profile bound belief).support) :
    E.terminal h.state := by
  rw [continuationLaw, FinDist.support_bind] at positive
  obtain ⟨root, _, hh⟩ := Set.mem_iUnion₂.mp positive
  exact M.runBehavioralFrom_terminal_of_bound profile bounded root h hh

/-- Extra fuel after the proved horizon changes neither the history law nor any payoff. -/
theorem continuationLaw_bound_add (profile : Profile M.behavioralSignature)
    {bound : Nat} (bounded : E.BoundedHorizon bound) (extra : Nat)
    {p : List M.PublicSignal} (belief : PublicBelief M.toInfoSignals p) :
    continuationLaw M profile (bound + extra) belief =
      continuationLaw M profile bound belief := by
  exact FinDist.bind_congr fun root _ =>
    M.runBehavioralFrom_bound_add profile bounded extra root

end PublicBelief

end GameTheory.ReBeL
