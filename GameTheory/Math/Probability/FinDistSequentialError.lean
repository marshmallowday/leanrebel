/-
# Sequential finite-kernel errors on actual forward laws

The hybrid argument changes one kernel at a time. Every event is charged
under the first execution's prefix law, never an unrelated model or the
second execution's prefix. Kernels and final observables may read all state.
-/

import GameTheory.Math.Probability.FinDistEventError

noncomputable section

namespace GameTheory.Math.Probability.FinDist

universe u v w
variable {A : Type u} {I : Type v} {B : Type w}

/-- Compose a finite list of kernels using the existing finite-law bind.
A stage label may encode a state-dependent kernel and need not have finite type. -/
def bindSequence (step : I → A → FinDist A) : List I → A → FinDist A
  | [], state => FinDist.pure state
  | stage :: stages, state =>
      (step stage state).bind (bindSequence step stages)

/-- Sum of exceptional-event probabilities along the actual forward execution.
This is an expected number of visits, not a union probability; it may exceed one. -/
def sequenceEventMass (step : I → A → FinDist A) (event : I → Set A) :
    List I → FinDist A → ℝ
  | [], _ => 0
  | stage :: stages, law =>
      law.probOf (event stage) + sequenceEventMass step event stages (law.bind (step stage))

/-- Splitting a schedule keeps the complete intermediate state distribution. -/
theorem bindSequence_append (step : I → A → FinDist A)
    (prefix suffix : List I) (state : A) :
    bindSequence step (prefix ++ suffix) state =
      (bindSequence step prefix state).bind (bindSequence step suffix) := by
  induction prefix generalizing state with
  | nil => simp only [List.nil_append, bindSequence, FinDist.pure_bind]
  | cons stage stages ih =>
      simp only [List.cons_append, bindSequence, ih, FinDist.bind_bind]

/-- The sequence error uses only equality of the kernels off the stated events.
No per-stage payoff-loss or final safety premise is assumed. The final kernel
may inspect the entire retained state, and the events may differ by stage. -/
theorem abs_expect_bindSequence_sub_le_of_eq_off_event
    (first second : I → A → FinDist A) (event : I → Set A)
    (equal : ∀ stage state, state ∉ event stage → first stage state = second stage state)
    (future : A → FinDist B) (payoff : B → ℝ) (bound : ℝ)
    (bounded : ∀ outcome, |payoff outcome| ≤ bound)
    (stages : List I) (law : FinDist A) :
    |((law.bind (bindSequence first stages)).bind future).expect payoff -
        ((law.bind (bindSequence second stages)).bind future).expect payoff| ≤
      2 * bound * sequenceEventMass first event stages law := by
  induction stages generalizing law with
  | nil =>
      simp only [bindSequence, sequenceEventMass, sub_self, abs_zero, mul_zero, le_refl]
  | cons stage stages ih =>
      let finish : A → FinDist B := fun state =>
        (bindSequence second stages state).bind future
      have headBound := abs_expect_bind_sub_le_of_eq_off_event law (event stage)
        (fun state => (first stage state).bind finish)
        (fun state => (second stage state).bind finish) payoff bound bounded
        (fun state _ outside => congrArg (fun distribution => distribution.bind finish)
          (equal stage state outside))
      have tailBound := ih (law.bind (first stage))
      simp only [bindSequence, sequenceEventMass, FinDist.expect_bind, finish] at
        headBound tailBound ⊢
      calc
        _ ≤ |law.expect (fun state => (first stage state).expect (fun next =>
                (bindSequence first stages next).expect (fun last =>
                  (future last).expect payoff))) -
              law.expect (fun state => (first stage state).expect (fun next =>
                (bindSequence second stages next).expect (fun last =>
                  (future last).expect payoff)))| +
            |law.expect (fun state => (first stage state).expect (fun next =>
                (bindSequence second stages next).expect (fun last =>
                  (future last).expect payoff))) -
              law.expect (fun state => (second stage state).expect (fun next =>
                (bindSequence second stages next).expect (fun last =>
                  (future last).expect payoff)))| := abs_sub_le _ _ _
        _ ≤ 2 * bound * sequenceEventMass first event stages (law.bind (first stage)) +
            2 * bound * law.probOf (event stage) := add_le_add tailBound headBound
        _ = _ := by ring

/-- The same theorem for a final observable on the complete retained state. -/
theorem abs_expect_sequence_sub_le_of_eq_off_event
    (first second : I → A → FinDist A) (event : I → Set A)
    (equal : ∀ stage state, state ∉ event stage → first stage state = second stage state)
    (payoff : A → ℝ) (bound : ℝ) (bounded : ∀ state, |payoff state| ≤ bound)
    (stages : List I) (law : FinDist A) :
    |(law.bind (bindSequence first stages)).expect payoff -
        (law.bind (bindSequence second stages)).expect payoff| ≤
      2 * bound * sequenceEventMass first event stages law := by
  have result := abs_expect_bindSequence_sub_le_of_eq_off_event first second event equal
    FinDist.pure payoff bound bounded stages law
  simpa only [FinDist.expect_bind, FinDist.expect_pure] using result

end GameTheory.Math.Probability.FinDist
