/-
# Native finite-schedule support charges

One-step support transport is composed under actual complete-state prefix laws.
The resulting forward sum bounds visits and hence first-hit probability, but
is not itself a probability or an assertion that primitive leakage is small.
The existing first-hit law observes inputs to scheduled stages, not the final
post-schedule state. The sum conservatively also charges the last transition.
-/

import GameTheory.Analysis.ReBeL.PBSOpponentModelTransport
import GameTheory.Analysis.ReBeL.PBSCarriedDepthFirstHit

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K I : Type*}

/-- Forward sum of native resolver support charges. Every new prefix is the
actual full-state law, including the correlated private memory and model PBS.
Stage labels may carry arbitrary finite search parameters. -/
def carriedMemorySupportCharge (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : I → CarriedResolveStage M K) :
    List I → FinDist (PrivateIterationState M (CarriedResolveMemory M K)) → ℝ
  | [], _ => 0
  | label :: labels, states =>
      states.expect (carriedResolvedSupportCharge M (stage label).resolver unknown who
        (stage label).fuel) +
      carriedMemorySupportCharge initial unknown who stage labels
        (states.bind (carriedMemoryStep M initial unknown who (stage label)))

/-- A stage-local sampling exception may be narrower than missing or unsupported
beliefs. Its native visit count is bounded by the initial support defect and
computed one-step charges, with no supplied security or posterior-equality premise. -/
theorem carriedMemorySequence_eventMass_le_supportCharge
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : I → CarriedResolveStage M K)
    (event : I → Set (PrivateIterationState M (CarriedResolveMemory M K)))
    (contained : ∀ label, event label ⊆ {state | ¬ carriedStateSupported M state})
    (schedule : List I)
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K))) :
    FinDist.sequenceEventMass (fun label => carriedMemoryStep M initial unknown who (stage label))
        event schedule states ≤
      states.probOf {state | ¬ carriedStateSupported M state} +
        carriedMemorySupportCharge M initial unknown who stage schedule states := by
  classical
  induction schedule generalizing states with
  | nil =>
      simp only [FinDist.sequenceEventMass, carriedMemorySupportCharge, add_zero]
      rw [← FinDist.expect_indicator_eq_probOf]
      calc
        0 = states.expect (fun _ => (0 : ℝ)) := (FinDist.expect_const states 0).symm
        _ ≤ _ := by
          apply FinDist.expect_mono
          intro state _
          split_ifs <;> norm_num
  | cons label labels ih =>
      have headBound : states.probOf (event label) ≤
          states.probOf {state | ¬ carriedStateSupported M state} := by
        rw [← FinDist.expect_indicator_eq_probOf, ← FinDist.expect_indicator_eq_probOf]
        apply FinDist.expect_mono
        intro state _
        by_cases hit : state ∈ event label
        · simp only [if_pos hit, if_pos (contained label hit), le_refl]
        · simp only [if_neg hit]
          split_ifs <;> norm_num
      have nextBound := carriedMemoryStep_law_unsupported_le M initial unknown who
        (stage label) states
      calc
        _ = states.probOf (event label) +
            FinDist.sequenceEventMass
              (fun index => carriedMemoryStep M initial unknown who (stage index))
              event labels (states.bind (carriedMemoryStep M initial unknown who (stage label)))
              := rfl
        _ ≤ states.probOf {state | ¬ carriedStateSupported M state} +
            ((states.bind (carriedMemoryStep M initial unknown who (stage label))).probOf
                {state | ¬ carriedStateSupported M state} +
              carriedMemorySupportCharge M initial unknown who stage labels
                (states.bind (carriedMemoryStep M initial unknown who (stage label)))) :=
          add_le_add headBound (ih _)
        _ ≤ states.probOf {state | ¬ carriedStateSupported M state} +
            (states.expect (carriedResolvedSupportCharge M (stage label).resolver unknown who
                (stage label).fuel) +
              carriedMemorySupportCharge M initial unknown who stage labels
                (states.bind (carriedMemoryStep M initial unknown who (stage label)))) :=
          add_le_add le_rfl (add_le_add nextBound le_rfl)
        _ = _ := rfl

/-- The actual first-hit probability is at most one and at most the composed
support charge. The sum may overcount repeated defects and is not a new law. -/
theorem carriedMemorySequence_firstHit_le_supportCharge
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : I → CarriedResolveStage M K)
    (event : I → Set (PrivateIterationState M (CarriedResolveMemory M K)))
    (contained : ∀ label, event label ⊆ {state | ¬ carriedStateSupported M state})
    (schedule : List I)
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K))) :
    FinDist.sequenceFirstHitProbability
        (fun label => carriedMemoryStep M initial unknown who (stage label))
        event schedule states ≤
      min 1 (states.probOf {state | ¬ carriedStateSupported M state} +
        carriedMemorySupportCharge M initial unknown who stage schedule states) := by
  apply le_min (FinDist.sequenceFirstHitProbability_le_one _ _ _ _)
  exact (FinDist.sequenceFirstHitProbability_le_eventMass _ _ _ _).trans
    (carriedMemorySequence_eventMass_le_supportCharge M initial unknown who stage event
      contained schedule states)

/-- A uniform primitive one-step support-leakage bound gives a linear fuel
allowance under actual visits. This is not a claim that the supplied rate is small. -/
theorem executionSupportCharge_le_mul
    (first second : Profile M.behavioralSignature) (rate : ℝ)
    (leakage : ∀ h, (M.runBehavioralFrom first 1 h).probOf
      {next | next ∉ (M.runBehavioralFrom second 1 h).support} ≤ rate)
    (fuel : Nat) (actual : FinDist E.History) :
    executionSupportCharge M first second fuel actual ≤ (fuel : ℝ) * rate := by
  induction fuel generalizing actual with
  | zero => simp only [executionSupportCharge, Nat.cast_zero, zero_mul, le_refl]
  | succ fuel ih =>
      calc
        _ ≤ rate + (fuel : ℝ) * rate := by
          apply add_le_add _ (ih _)
          apply FinDist.expect_le_of_forall
          intro history _
          exact leakage history
        _ = ((fuel + 1 : Nat) : ℝ) * rate := by push_cast; ring

/-- From a supported input, the native selected-model charge is controlled by
primitive leakage of the actually sampled profiles. Terminal and zero-fuel
inputs cost zero. No condition is imposed on unsupported incoming states. -/
theorem carriedResolvedSupportCharge_le_of_step_leakage
    (resolver : CarriedPublicResolver M K) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (fuel : Nat) (state : PrivateIterationState M K)
    (supported : carriedStateSupported M state) (rate : ℝ) (nonnegative : 0 ≤ rate)
    (leakage : ∀ chosen ∈ (resolver state.iteration
      (publicTrace M.toInfoSignals state.history.trace) state.belief).support,
      ∀ h, (M.runBehavioralFrom (Profile.update unknown who (chosen who)) 1 h).probOf
        {next | next ∉ (M.runBehavioralFrom chosen 1 h).support} ≤ rate) :
    carriedResolvedSupportCharge M resolver unknown who fuel state ≤ (fuel : ℝ) * rate := by
  classical
  obtain ⟨belief, stored, member⟩ := supported
  by_cases live : cfrDCutLive fuel state.history = true
  · rw [carriedResolvedSupportCharge_of_supported M resolver unknown who fuel state
      belief live stored member]
    apply FinDist.expect_le_of_forall
    intro chosen sampled
    apply executionSupportCharge_le_mul
    intro history
    exact leakage chosen (by simpa only [stored] using sampled) history
  · have valid : carriedStateSupported M state := ⟨belief, stored, member⟩
    rw [carriedResolvedSupportCharge, if_neg live, if_pos valid]
    exact mul_nonneg (Nat.cast_nonneg _) nonnegative

/-- Primitive support leakage is accumulated only until the first defective
input. Persistent failures do not cause quadratic repeated charges, and the
last transition is excluded because its output is not an observed stage input. -/
theorem carriedMemorySequence_firstHit_le_primitiveRate
    (initial : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2)
    (stage : I → CarriedResolveStage M K)
    (event : I → Set (PrivateIterationState M (CarriedResolveMemory M K)))
    (contained : ∀ label, event label ⊆ {state | ¬ carriedStateSupported M state})
    (rate : I → ℝ) (nonnegative : ∀ label, 0 ≤ rate label)
    (leakage : ∀ label state, carriedStateSupported M state →
      ∀ chosen ∈ ((stage label).resolver state.iteration
        (publicTrace M.toInfoSignals state.history.trace) state.belief).support,
        ∀ h, (M.runBehavioralFrom (Profile.update unknown who (chosen who)) 1 h).probOf
          {next | next ∉ (M.runBehavioralFrom chosen 1 h).support} ≤ rate label)
    (schedule : List I)
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K))) :
    FinDist.sequenceFirstHitProbability
        (fun label => carriedMemoryStep M initial unknown who (stage label))
        event schedule states ≤
      min 1 (states.probOf {state | ¬ carriedStateSupported M state} +
        FinDist.firstHitRateBudget (fun label => ((stage label).fuel : ℝ) * rate label)
          schedule) := by
  classical
  apply le_min (FinDist.sequenceFirstHitProbability_le_one _ _ _ _)
  apply FinDist.sequenceFirstHitProbability_le_rateBudget _ _ event contained
  · intro label
    exact mul_nonneg (Nat.cast_nonneg _) (nonnegative label)
  · intro label state outside
    have supported : carriedStateSupported M state := by
      by_contra invalid
      exact outside invalid
    exact (carriedMemoryStep_unsupported_le M initial unknown who (stage label) state).trans
      (carriedResolvedSupportCharge_le_of_step_leakage M (stage label).resolver unknown who
        (stage label).fuel state supported (rate label) (nonnegative label)
        (leakage label state supported))

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- The existing noisy depth-limited CFR resolver, with its native private
iteration/PBS pairing at every stage, satisfies the composed support bound.
Missing beliefs are charged conservatively although they are not sampling exceptions. -/
theorem pbsCarriedDepthFirstHitProbability_le_supportCharge
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (schedule : List (PBSCarriedDepthParameters M))
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))) :
    pbsCarriedDepthFirstHitProbability M fallback payoff initial unknown who schedule states ≤
      min 1 (states.probOf {state | ¬ carriedStateSupported (fullInformation M) state} +
        carriedMemorySupportCharge (fullInformation M) initial unknown who
          (pbsCarriedDepthConfiguredStage M fallback payoff initial) schedule states) := by
  apply carriedMemorySequence_firstHit_le_supportCharge
  intro parameters state hit supported
  obtain ⟨belief, stored, member⟩ := supported
  have outside : state.history ∉ belief.law.support := by
    simpa only [stored] using hit.2
  exact outside member

/-- Composed support charges control the already proved history-first sampling
comparison, not unilateral security. The unchanged unknown opponent and all
finite-iteration and noise parameters remain in the actual native execution. -/
theorem pbsCarriedDepth_support_future_error {Outcome : Type*}
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (schedule : List (PBSCarriedDepthParameters M))
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)))
    (future : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K) → FinDist Outcome)
    (value : Outcome → ℝ) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ outcome, |value outcome| ≤ bound) :
    |((pbsCarriedDepthNativeStates M fallback payoff initial unknown who schedule states).bind
        future).expect value -
      ((pbsCarriedDepthHistoryFirstStates M fallback payoff initial unknown who
        schedule states).bind future).expect value| ≤
      2 * bound * min 1
        (states.probOf {state | ¬ carriedStateSupported (fullInformation M) state} +
          carriedMemorySupportCharge (fullInformation M) initial unknown who
            (pbsCarriedDepthConfiguredStage M fallback payoff initial) schedule states) := by
  exact (pbsCarriedDepthFirstHit_future_error M fallback payoff initial unknown who schedule
    states future value bound bounded).trans
      (mul_le_mul_of_nonneg_left
        (pbsCarriedDepthFirstHitProbability_le_supportCharge M fallback payoff initial unknown
          who schedule states) (mul_nonneg (by norm_num) nonnegative))

/-- The actual noisy depth-CFR schedule consumes primitive selected-model rates.
The same unknown opponent is used at every stage; rates are not obtained from
child Nash or equality of actual and stored posteriors. -/
theorem pbsCarriedDepthFirstHitProbability_le_primitiveRate
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (rate : PBSCarriedDepthParameters M → ℝ)
    (nonnegative : ∀ parameters, 0 ≤ rate parameters)
    (leakage : ∀ parameters state, carriedStateSupported (fullInformation M) state →
      ∀ chosen ∈ ((pbsCarriedDepthConfiguredStage M fallback payoff initial parameters).resolver
        state.iteration (publicTrace (fullInformation M).toInfoSignals state.history.trace)
        state.belief).support,
        ∀ h, ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who (chosen who)) 1 h).probOf
            {next | next ∉ ((fullInformation M).runBehavioralFrom chosen 1 h).support} ≤
          rate parameters)
    (schedule : List (PBSCarriedDepthParameters M))
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))) :
    pbsCarriedDepthFirstHitProbability M fallback payoff initial unknown who schedule states ≤
      min 1 (states.probOf {state | ¬ carriedStateSupported (fullInformation M) state} +
        FinDist.firstHitRateBudget (fun parameters => (parameters.fuel : ℝ) * rate parameters)
          schedule) := by
  apply carriedMemorySequence_firstHit_le_primitiveRate
    (fullInformation M) initial unknown who
    (pbsCarriedDepthConfiguredStage M fallback payoff initial) _ _ rate nonnegative leakage
  intro parameters state hit supported
  obtain ⟨belief, stored, member⟩ := supported
  have outside : state.history ∉ belief.law.support := by
    simpa only [stored] using hit.2
  exact outside member

end GameTheory.ReBeL

namespace GameTheory.ReBeL.Examples.CarriedSupport

open GameTheory.Math.Probability

/-- A genuinely random transition leaks a quarter of its mass to the bad state. -/
def quarterLeak (_ : Unit) (_ : Fin 2) : FinDist (Fin 2) :=
  FinDist.mix (1 / 4) (by norm_num) (by norm_num) (FinDist.pure 0) (FinDist.pure 1)

/-- An empty schedule observes no state. This must not be identified with the
initial support defect, which is one for the displayed bad initial state. -/
theorem empty_schedule :
    FinDist.sequenceFirstHitProbability quarterLeak (fun _ => {0}) [] (FinDist.pure 0) = 0 := by
  simp [FinDist.sequenceFirstHitProbability, FinDist.sequenceFirstHit,
    FinDist.prob_pure_eq_ite]

/-- Two stage inputs see quarter-mass failure. Checking only the initial state
would miss it, while incorrectly treating the last output as another input adds a hit. -/
theorem two_stage_hit :
    FinDist.sequenceFirstHitProbability quarterLeak (fun _ => {0}) [(), ()]
        (FinDist.pure 1) = 1 / 4 := by
  norm_num [FinDist.sequenceFirstHitProbability, FinDist.sequenceFirstHit,
    quarterLeak, FinDist.prob_bind, FinDist.expect_mix, FinDist.expect_pure,
    FinDist.prob_pure_eq_ite]

/-- Three stage inputs have union probability seven sixteenths, not the
one-half expected visit count. Independent native draws are not pooled into a seed. -/
theorem three_stage_hit_not_visits :
    FinDist.sequenceFirstHitProbability quarterLeak (fun _ => {0}) [(), (), ()]
        (FinDist.pure 1) = 7 / 16 ∧
      FinDist.sequenceEventMass quarterLeak (fun _ => {0}) [(), (), ()]
        (FinDist.pure 1) = 1 / 2 := by
  classical
  constructor
  · norm_num [FinDist.sequenceFirstHitProbability, FinDist.sequenceFirstHit,
      quarterLeak, FinDist.prob_bind, FinDist.expect_mix, FinDist.expect_pure,
      FinDist.prob_pure_eq_ite]
  · norm_num [FinDist.sequenceEventMass, quarterLeak,
      ← FinDist.expect_indicator_eq_probOf, FinDist.expect_bind,
      FinDist.expect_mix, FinDist.expect_pure, FinDist.expect_const]

end GameTheory.ReBeL.Examples.CarriedSupport

namespace GameTheory.ReBeL.Examples.PrimitiveSupport

open GameTheory.Math.Probability

/-- Bad states stay bad, whereas good states leak a quarter of their mass. -/
def stickyQuarterLeak (_ : Unit) (state : Fin 2) : FinDist (Fin 2) :=
  if state = 0 then FinDist.pure 0 else CarriedSupport.quarterLeak () state

/-- Primitive leakage is small at every good state, including before a first hit. -/
theorem sticky_rate_on_good (state : Fin 2) (good : state ∉ ({0} : Set (Fin 2))) :
    (stickyQuarterLeak () state).probOf {0} ≤ 1 / 4 := by
  classical
  have different : state ≠ 0 := good
  norm_num [stickyQuarterLeak, different, CarriedSupport.quarterLeak,
    ← FinDist.expect_indicator_eq_probOf, FinDist.expect_mix, FinDist.expect_pure]

/-- Requiring the quarter bound also at bad states would incorrectly reject
this process. The next-state bad probability there is one, not one quarter. -/
theorem sticky_bad_has_unit_rate :
    (stickyQuarterLeak () 0).probOf {0} = 1 := by
  classical
  norm_num [stickyQuarterLeak, ← FinDist.expect_indicator_eq_probOf, FinDist.expect_pure]

/-- The good-state hypothesis alone yields the two-transition allowance 1/2
for three stage inputs, even with absorbing failure and no independence premise. -/
theorem three_stage_primitive_bound :
    FinDist.sequenceFirstHitProbability stickyQuarterLeak (fun _ => {0})
      [(), (), ()] (FinDist.pure 1) ≤ 1 / 2 := by
  classical
  have estimate := FinDist.sequenceFirstHitProbability_le_rateBudget stickyQuarterLeak {0}
    (fun _ => {0}) (fun _ _ member => member) (fun _ => (1 / 4 : ℝ))
    (fun _ => by norm_num) (fun _ state good => sticky_rate_on_good state good)
    [(), (), ()] (FinDist.pure 1)
  norm_num [FinDist.firstHitRateBudget, ← FinDist.expect_indicator_eq_probOf,
    FinDist.expect_pure] at estimate
  exact estimate

/-- The displayed rate bound is nonvacuous: the exact hit probability is 7/16. -/
theorem sticky_three_stage_hit :
    FinDist.sequenceFirstHitProbability stickyQuarterLeak (fun _ => {0})
      [(), (), ()] (FinDist.pure 1) = 7 / 16 := by
  norm_num [FinDist.sequenceFirstHitProbability, FinDist.sequenceFirstHit,
    stickyQuarterLeak, CarriedSupport.quarterLeak, FinDist.prob_bind,
    FinDist.expect_mix, FinDist.expect_pure, FinDist.prob_pure_eq_ite]

/-- One input observes no later transition, regardless of that transition's rate. -/
theorem singleton_budget :
    FinDist.firstHitRateBudget (fun _ : Unit => (7 : ℝ)) [()] = 0 := rfl

end GameTheory.ReBeL.Examples.PrimitiveSupport
