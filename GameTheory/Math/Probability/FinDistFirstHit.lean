/-
# First-hit bounds for sequential finite kernels

The first execution determines the probability of ever entering an exceptional
state. Unlike the expected number of exceptional visits, this probability is
at most one. The Boolean stopping law is built only from canonical FinDist
operations; it does not replace the actual execution or its retained state.
The refined stopping law also retains the first exceptional state and the
unexecuted suffix, allowing a source-dependent continuation-error decomposition.
-/

import GameTheory.Math.Probability.FinDistSequentialError

noncomputable section

namespace GameTheory.Math.Probability.FinDist

universe u v w
variable {A : Type u} {I : Type v} {B : Type w}

/-- Record whether an exception is encountered before the finite schedule ends.
Only this analysis law stops at the first hit; the original execution need not. -/
def sequenceFirstHit (step : I → A → FinDist A) (event : I → Set A) :
    List I → A → FinDist Bool
  | [], _ => FinDist.pure false
  | stage :: stages, state => by
      classical
      exact if state ∈ event stage then FinDist.pure true
        else (step stage state).bind (sequenceFirstHit step event stages)

/-- Probability of at least one exceptional visit under the native execution.
There is no assumption that the initial state law is a model posterior. -/
def sequenceFirstHitProbability (step : I → A → FinDist A) (event : I → Set A)
    (stages : List I) (law : FinDist A) : ℝ :=
  (law.bind (sequenceFirstHit step event stages)).prob true

/-- The stopped Boolean law gives a genuine probability, not a visit count. -/
theorem sequenceFirstHitProbability_nonneg (step : I → A → FinDist A)
    (event : I → Set A) (stages : List I) (law : FinDist A) :
    0 ≤ sequenceFirstHitProbability step event stages law :=
  FinDist.prob_nonneg _ _

/-- Repeated exceptional visits can never make the first-hit probability exceed one. -/
theorem sequenceFirstHitProbability_le_one (step : I → A → FinDist A)
    (event : I → Set A) (stages : List I) (law : FinDist A) :
    sequenceFirstHitProbability step event stages law ≤ 1 :=
  FinDist.prob_le_one _ _

/-- Integrate signed pointwise error bounds without assuming constant allowances. -/
private theorem firstHit_average (law : FinDist A) (first second allowance : A → ℝ)
    (bounded : ∀ state ∈ law.support, |first state - second state| ≤ allowance state) :
    |law.expect first - law.expect second| ≤ law.expect allowance := by
  have upper : law.expect first - law.expect second ≤ law.expect allowance := by
    rw [← FinDist.expect_sub]
    exact FinDist.expect_mono fun state reached => (abs_le.mp (bounded state reached)).2
  have lower : law.expect second - law.expect first ≤ law.expect allowance := by
    rw [← FinDist.expect_sub]
    apply FinDist.expect_mono
    intro state reached
    have h := (abs_le.mp (bounded state reached)).1
    linarith
  exact abs_le.mpr ⟨by linarith, upper⟩

/-- Complete-kernel discrepancy is charged only at the first exception. Before
that hit the two kernels agree on the entire state, including private memory.
After the hit any bounded future can differ by at most twice its absolute bound. -/
theorem abs_expect_bindSequence_sub_le_firstHit
    (first second : I → A → FinDist A) (event : I → Set A)
    (equal : ∀ stage state, state ∉ event stage → first stage state = second stage state)
    (future : A → FinDist B) (payoff : B → ℝ) (bound : ℝ)
    (bounded : ∀ outcome, |payoff outcome| ≤ bound)
    (stages : List I) (law : FinDist A) :
    |((law.bind (bindSequence first stages)).bind future).expect payoff -
        ((law.bind (bindSequence second stages)).bind future).expect payoff| ≤
      2 * bound * sequenceFirstHitProbability first event stages law := by
  classical
  induction stages generalizing law with
  | nil =>
      norm_num [bindSequence, sequenceFirstHitProbability, sequenceFirstHit,
        FinDist.prob_bind, FinDist.prob_pure_eq_ite]
  | cons stage stages ih =>
      have localBound (state : A) :
          |((bindSequence first (stage :: stages) state).bind future).expect payoff -
              ((bindSequence second (stage :: stages) state).bind future).expect payoff| ≤
            2 * bound * (sequenceFirstHit first event (stage :: stages) state).prob true := by
        by_cases hit : state ∈ event stage
        · rw [sequenceFirstHit, if_pos hit, FinDist.prob_pure_self, mul_one]
          obtain ⟨firstLower, firstUpper⟩ := abs_le.mp
            (FinDist.abs_expect_le_of_abs_bound
              ((bindSequence first (stage :: stages) state).bind future) payoff
              (fun outcome _ => bounded outcome))
          obtain ⟨secondLower, secondUpper⟩ := abs_le.mp
            (FinDist.abs_expect_le_of_abs_bound
              ((bindSequence second (stage :: stages) state).bind future) payoff
              (fun outcome _ => bounded outcome))
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        · have shared : second stage state = first stage state :=
            (equal stage state hit).symm
          simpa only [bindSequence, sequenceFirstHit, if_neg hit, shared,
            sequenceFirstHitProbability, FinDist.bind_bind] using ih (first stage state)
      have averaged := firstHit_average law
        (fun state => ((bindSequence first (stage :: stages) state).bind future).expect payoff)
        (fun state => ((bindSequence second (stage :: stages) state).bind future).expect payoff)
        (fun state =>
          2 * bound * (sequenceFirstHit first event (stage :: stages) state).prob true)
        (fun state _ => localBound state)
      simpa only [FinDist.expect_bind, FinDist.expect_smul, sequenceFirstHitProbability,
        FinDist.prob_bind] using averaged

/-- A first hit is no more likely than the expected number of native visits.
The right-hand side is the existing forward-event sum, not a model-law estimate. -/
theorem sequenceFirstHitProbability_le_eventMass (step : I → A → FinDist A)
    (event : I → Set A) (stages : List I) (law : FinDist A) :
    sequenceFirstHitProbability step event stages law ≤
      sequenceEventMass step event stages law := by
  classical
  induction stages generalizing law with
  | nil =>
      norm_num [sequenceFirstHitProbability, sequenceFirstHit, sequenceEventMass,
        FinDist.prob_bind, FinDist.prob_pure_eq_ite]
  | cons stage stages ih =>
      have pointwise (state : A) :
          (sequenceFirstHit step event (stage :: stages) state).prob true ≤
            (if state ∈ event stage then (1 : ℝ) else 0) +
              sequenceFirstHitProbability step event stages (step stage state) := by
        by_cases hit : state ∈ event stage
        · rw [sequenceFirstHit, if_pos hit, FinDist.prob_pure_self, if_pos hit]
          have nonnegative :=
            sequenceFirstHitProbability_nonneg step event stages (step stage state)
          linarith
        · simp only [sequenceFirstHit, if_neg hit, zero_add, sequenceFirstHitProbability,
            le_refl]
      calc
        _ = law.expect (fun state =>
            (sequenceFirstHit step event (stage :: stages) state).prob true) :=
          FinDist.prob_bind _ _ _
        _ ≤ law.expect (fun state => (if state ∈ event stage then (1 : ℝ) else 0) +
            sequenceFirstHitProbability step event stages (step stage state)) :=
          FinDist.expect_mono fun state _ => pointwise state
        _ = law.probOf (event stage) +
            sequenceFirstHitProbability step event stages (law.bind (step stage)) := by
          rw [FinDist.expect_add, FinDist.expect_indicator_eq_probOf]
          simp only [sequenceFirstHitProbability, FinDist.prob_bind, FinDist.expect_bind]
        _ ≤ law.probOf (event stage) +
            sequenceEventMass step event stages (law.bind (step stage)) := by
          linarith [ih (law.bind (step stage))]
        _ = _ := rfl

/-- The sharper allowance is bounded by both one and the previous forward sum. -/
theorem sequenceFirstHitProbability_le_min (step : I → A → FinDist A)
    (event : I → Set A) (stages : List I) (law : FinDist A) :
    sequenceFirstHitProbability step event stages law ≤
      min 1 (sequenceEventMass step event stages law) :=
  le_min (sequenceFirstHitProbability_le_one step event stages law)
    (sequenceFirstHitProbability_le_eventMass step event stages law)

/-- Retain the first exceptional state and the suffix beginning at its unexecuted
stage. None means that no exception occurred. The native run itself never stops. -/
def sequenceFirstExit (step : I → A → FinDist A) (event : I → Set A) :
    List I → A → FinDist (Option (List I × A))
  | [], _ => FinDist.pure none
  | stage :: stages, state => by
      classical
      exact if state ∈ event stage then FinDist.pure (some (stage :: stages, state))
        else (step stage state).bind (sequenceFirstExit step event stages)

/-- Forgetting the retained witness recovers the existing Boolean stopping law. -/
theorem sequenceFirstExit_hit (step : I → A → FinDist A) (event : I → Set A)
    (stages : List I) (state : A) :
    (sequenceFirstExit step event stages state).map Option.isSome =
      sequenceFirstHit step event stages state := by
  classical
  induction stages generalizing state with
  | nil => simp [sequenceFirstExit, sequenceFirstHit, FinDist.map_eq_bind]
  | cons stage stages ih =>
      by_cases hit : state ∈ event stage
      · simp [sequenceFirstExit, sequenceFirstHit, hit, FinDist.map_eq_bind]
      · simp only [sequenceFirstExit, sequenceFirstHit, if_neg hit, FinDist.map_bind]
        exact FinDist.bind_congr fun next _ => ih next

/-- Witness refinement does not change the first-hit probability at any root law. -/
theorem sequenceFirstExit_hitProbability (step : I → A → FinDist A) (event : I → Set A)
    (stages : List I) (law : FinDist A) :
    ((law.bind (sequenceFirstExit step event stages)).map Option.isSome).prob true =
      sequenceFirstHitProbability step event stages law := by
  simp only [FinDist.map_bind, sequenceFirstExit_hit, sequenceFirstHitProbability]

/-- The complete first-exit witness law is invariant under changes AFTER the
first exceptional visit. Both kernels retain the same state before that visit. -/
theorem sequenceFirstExit_eq_of_eq_off_event
    (first second : I → A → FinDist A) (event : I → Set A)
    (equal : ∀ stage state, state ∉ event stage → first stage state = second stage state)
    (stages : List I) (state : A) :
    sequenceFirstExit first event stages state = sequenceFirstExit second event stages state := by
  classical
  induction stages generalizing state with
  | nil => rfl
  | cons stage stages ih =>
      by_cases hit : state ∈ event stage
      · simp only [sequenceFirstExit, if_pos hit]
      · simp only [sequenceFirstExit, if_neg hit, equal stage state hit]
        exact FinDist.bind_congr fun next _ => ih next

/-- The signed continuation discrepancy at the retained first-exit witness.
The suffix INCLUDES the exceptional stage. No bound or safety certificate is input. -/
def sequenceFirstExitValue (first second : I → A → FinDist A)
    (future : A → FinDist B) (payoff : B → ℝ) : Option (List I × A) → ℝ
  | none => 0
  | some (stages, state) =>
      ((bindSequence first stages state).bind future).expect payoff -
        ((bindSequence second stages state).bind future).expect payoff

/-- Exact signed decomposition, not merely a worst-case bound: all discrepancy
comes from native first-exit states, each evaluated on its own remaining suffix.
The result holds for arbitrary finite laws and arbitrary future observables. -/
theorem expect_bindSequence_sub_eq_firstExit
    (first second : I → A → FinDist A) (event : I → Set A)
    (equal : ∀ stage state, state ∉ event stage → first stage state = second stage state)
    (future : A → FinDist B) (payoff : B → ℝ) (stages : List I) (law : FinDist A) :
    ((law.bind (bindSequence first stages)).bind future).expect payoff -
        ((law.bind (bindSequence second stages)).bind future).expect payoff =
      (law.bind (sequenceFirstExit first event stages)).expect
        (sequenceFirstExitValue first second future payoff) := by
  classical
  induction stages generalizing law with
  | nil => simp [bindSequence, sequenceFirstExit, sequenceFirstExitValue]
  | cons stage stages ih =>
      have localIdentity (state : A) :
          ((bindSequence first (stage :: stages) state).bind future).expect payoff -
              ((bindSequence second (stage :: stages) state).bind future).expect payoff =
            (sequenceFirstExit first event (stage :: stages) state).expect
              (sequenceFirstExitValue first second future payoff) := by
        by_cases hit : state ∈ event stage
        · rw [sequenceFirstExit, if_pos hit, FinDist.expect_pure]
          rfl
        · have shared : second stage state = first stage state :=
            (equal stage state hit).symm
          simpa only [bindSequence, sequenceFirstExit, if_neg hit, shared,
            FinDist.bind_bind, FinDist.expect_bind] using ih (first stage state)
      simp only [FinDist.expect_bind]
      rw [← FinDist.expect_sub]
      exact FinDist.expect_congr fun state _ => by
        simpa only [FinDist.expect_bind] using localIdentity state

/-- A computed state-dependent allowance replaces the uniform worst-case charge.
The expectation retains all dependence between the stopping time and private state. -/
theorem abs_expect_bindSequence_sub_le_firstExit
    (first second : I → A → FinDist A) (event : I → Set A)
    (equal : ∀ stage state, state ∉ event stage → first stage state = second stage state)
    (future : A → FinDist B) (payoff : B → ℝ) (stages : List I) (law : FinDist A) :
    |((law.bind (bindSequence first stages)).bind future).expect payoff -
        ((law.bind (bindSequence second stages)).bind future).expect payoff| ≤
      (law.bind (sequenceFirstExit first event stages)).expect
        (fun witness => |sequenceFirstExitValue first second future payoff witness|) := by
  rw [expect_bindSequence_sub_eq_firstExit first second event equal future payoff stages law]
  have averaged := firstHit_average (law.bind (sequenceFirstExit first event stages))
    (sequenceFirstExitValue first second future payoff) (fun _ => 0)
    (fun witness => |sequenceFirstExitValue first second future payoff witness|)
    (fun witness _ => by simp only [sub_zero, le_refl])
  simpa only [FinDist.expect_const, sub_zero] using averaged

/-- The computed allowance is no larger than twice the observable bound times
the old hit probability. A positive hit probability need not cause any payoff error. -/
theorem firstExitValue_expect_abs_le_firstHit
    (first second : I → A → FinDist A) (event : I → Set A)
    (future : A → FinDist B) (payoff : B → ℝ) (bound : ℝ)
    (bounded : ∀ outcome, |payoff outcome| ≤ bound) (stages : List I) (law : FinDist A) :
    (law.bind (sequenceFirstExit first event stages)).expect
        (fun witness => |sequenceFirstExitValue first second future payoff witness|) ≤
      2 * bound * sequenceFirstHitProbability first event stages law := by
  have localBound (witness : Option (List I × A)) :
      |sequenceFirstExitValue first second future payoff witness| ≤
        2 * bound * (FinDist.pure witness.isSome).prob true := by
    cases witness with
    | none => norm_num [sequenceFirstExitValue, FinDist.prob_pure_eq_ite]
    | some pair =>
        obtain ⟨suffix, state⟩ := pair
        obtain ⟨firstLower, firstUpper⟩ := abs_le.mp
          (FinDist.abs_expect_le_of_abs_bound
            ((bindSequence first suffix state).bind future) payoff
            (fun outcome _ => bounded outcome))
        obtain ⟨secondLower, secondUpper⟩ := abs_le.mp
          (FinDist.abs_expect_le_of_abs_bound
            ((bindSequence second suffix state).bind future) payoff
            (fun outcome _ => bounded outcome))
        simp only [sequenceFirstExitValue, Option.isSome, FinDist.prob_pure_self, mul_one]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    _ ≤ (law.bind (sequenceFirstExit first event stages)).expect
        (fun witness => 2 * bound * (FinDist.pure witness.isSome).prob true) :=
      FinDist.expect_mono fun witness _ => localBound witness
    _ = 2 * bound *
        ((law.bind (sequenceFirstExit first event stages)).map Option.isSome).prob true := by
      rw [FinDist.expect_smul, FinDist.map_eq_bind, FinDist.prob_bind]
    _ = _ := by rw [sequenceFirstExit_hitProbability]

end GameTheory.Math.Probability.FinDist
