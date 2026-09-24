/-
# First-hit bounds for sequential finite kernels

The first execution determines the probability of ever entering an exceptional
state. Unlike the expected number of exceptional visits, this probability is
at most one. The Boolean stopping law is built only from canonical FinDist
operations; it does not replace the actual execution or its retained state.
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

end GameTheory.Math.Probability.FinDist
