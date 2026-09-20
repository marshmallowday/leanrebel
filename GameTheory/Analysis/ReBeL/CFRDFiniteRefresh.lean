/-
# Fresh finite solves of the actual carried public belief

Each live scheduled query computes a finite-budget normal-form solution from
the stored joint PBS, then privately refreshes the retained profile with the
specified probability. Missing model support retains the old selection. Local
loss bounds are derived at every actual carried state and compose recursively.
The explicit refresh penalty is not a lossless arbitrary-equilibrium claim.
-/

import GameTheory.Analysis.ReBeL.CFRDRefreshMix
import GameTheory.Analysis.ReBeL.PBSFinitePlanSolver

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {K : Type*}

/-- Re-solve the carried PBS, not a replay from the original root. A missing
model posterior never fabricates a belief from the actual hidden history. -/
def finiteRefreshCandidate (initial : K → Profile M.behavioralSignature)
    (clock : ObservationClock M) (fallback : Profile M.strategicSignature)
    (fuel : Nat) (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) :
    CarriedPublicResolver M (CarriedResolveMemory M K) := fun memory _ belief =>
  FinDist.pure (match belief with
    | some prior => pbsConditionalBudgetProfile M clock fallback prior fuel utility bound loss
    | none => carriedMemoryProfile M initial memory)

/-- No model posterior means exact retention rather than an unrelated solve. -/
theorem finiteRefreshCandidate_none (initial : K → Profile M.behavioralSignature)
    (clock : ObservationClock M) (fallback : Profile M.strategicSignature)
    (fuel : Nat) (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ)
    (memory : CarriedResolveMemory M K) (obs : List M.PublicSignal) :
    finiteRefreshCandidate M initial clock fallback fuel utility bound loss memory obs none =
      FinDist.pure (carriedMemoryProfile M initial memory) := rfl

/-- A present PBS is sent to the finite recurrence with its own mass budget. -/
theorem finiteRefreshCandidate_some (initial : K → Profile M.behavioralSignature)
    (clock : ObservationClock M) (fallback : Profile M.strategicSignature)
    (fuel : Nat) (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ)
    (memory : CarriedResolveMemory M K) (obs : List M.PublicSignal)
    (belief : PublicBelief M.toInfoSignals obs) :
    finiteRefreshCandidate M initial clock fallback fuel utility bound loss memory obs
        (some belief) =
      FinDist.pure (pbsConditionalBudgetProfile M clock fallback belief fuel utility bound loss) :=
  rfl

/-- Every candidate drawn from a present PBS is the actual finite solver's
approximate Nash profile. This does not assert Nash for the retain-old mixture. -/
theorem finiteRefreshCandidate_isNash (hrecall : M.PerfectRecall)
    (initial : K → Profile M.behavioralSignature) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ history who, |utility history who| ≤ bound)
    (memory : CarriedResolveMemory M K) (obs : List M.PublicSignal)
    (belief : PublicBelief M.toInfoSignals obs) (chosen : Profile M.behavioralSignature)
    (sampled : chosen ∈ (finiteRefreshCandidate M initial clock fallback fuel utility bound loss
      memory obs (some belief)).support) :
    IsNash (behavioralBeliefForm M belief fuel)
      (euPreferenceWithin (belief.law.positiveMassFloor * loss) utility) chosen := by
  rw [finiteRefreshCandidate_some, FinDist.mem_support_pure] at sampled
  subst chosen
  exact pbsFiniteBudgetProfile_isNash M hrecall clock fallback belief fuel utility zeroSum
    bound nonneg bounded (belief.law.positiveMassFloor * loss)
    (mul_pos (FinDist.positiveMassFloor_pos belief.law) positive)

/-- Each query solves the entire remaining horizon, then executes only this
stage's fuel before the next public query. The finite list gives termination. -/
def finiteRefreshStages (initial : K → Profile M.behavioralSignature)
    (clock : ObservationClock M) (fallback : Profile M.strategicSignature)
    (utility : E.History → Fin 2 → ℝ) (bound loss rate : ℝ)
    (nonneg : 0 ≤ rate) (atMostOne : rate ≤ 1) (finalFuel : Nat) :
    List Nat → List (CarriedResolveStage M K)
  | [] => []
  | fuel :: fuels =>
      mixedCarriedStage M initial
        (finiteRefreshCandidate M initial clock fallback (fuel + (fuels.sum + finalFuel))
          utility bound loss) fuel rate nonneg atMostOne ::
        finiteRefreshStages initial clock fallback utility bound loss rate
          nonneg atMostOne finalFuel fuels

/-- The schedule consumes exactly its declared fuel, including the final tail. -/
theorem finiteRefreshStages_fuel (initial : K → Profile M.behavioralSignature)
    (clock : ObservationClock M) (fallback : Profile M.strategicSignature)
    (utility : E.History → Fin 2 → ℝ) (bound loss rate : ℝ)
    (nonneg : 0 ≤ rate) (atMostOne : rate ≤ 1) (finalFuel : Nat) (fuels : List Nat) :
    carriedResolveFuel M finalFuel
        (finiteRefreshStages M initial clock fallback utility bound loss rate
          nonneg atMostOne finalFuel fuels) = fuels.sum + finalFuel := by
  induction fuels with
  | nil => simp only [finiteRefreshStages, carriedResolveFuel, List.sum_nil, Nat.zero_add]
  | cons fuel fuels ih =>
      simp only [finiteRefreshStages, carriedResolveFuel, mixedCarriedStage,
        ih, List.sum_cons, Nat.add_assoc]

/-- A constant derived allowance is charged once per scheduled stage. -/
theorem finiteRefreshStages_allowance (initial : K → Profile M.behavioralSignature)
    (clock : ObservationClock M) (fallback : Profile M.strategicSignature)
    (utility : E.History → Fin 2 → ℝ) (bound loss rate : ℝ)
    (nonneg : 0 ≤ rate) (atMostOne : rate ≤ 1) (finalFuel : Nat) (fuels : List Nat)
    (allowance : ℝ) :
    ((finiteRefreshStages M initial clock fallback utility bound loss rate
      nonneg atMostOne finalFuel fuels).map (fun _ => allowance)).sum =
        (fuels.length : ℝ) * allowance := by
  induction fuels with
  | nil => simp only [finiteRefreshStages, List.map_nil, List.sum_nil, List.length_nil,
      Nat.cast_zero, zero_mul]
  | cons fuel fuels ih =>
      simp only [finiteRefreshStages, List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one, ih]
      ring

/-- No stage-local comparison is supplied: the bounded mixture derives all
of them for the actual forward state laws, including missing/off-model PBSs. -/
theorem finiteRefreshStages_stepBounds (initial : K → Profile M.behavioralSignature)
    (clock : ObservationClock M) (fallback : Profile M.strategicSignature)
    (utility : E.History → Fin 2 → ℝ) (bound loss rate : ℝ)
    (nonneg : 0 ≤ rate) (atMostOne : rate ≤ 1) (finalFuel : Nat) (fuels : List Nat)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (boundNonneg : 0 ≤ bound)
    (bounded : ∀ history, |utility history who| ≤ bound)
    (states : FinDist (PrivateIterationState M (CarriedResolveMemory M K))) :
    CarriedResolveStepBounds M initial unknown who finalFuel (fun h => utility h who)
      (fun _ => 2 * bound * rate)
      (finiteRefreshStages M initial clock fallback utility bound loss rate
        nonneg atMostOne finalFuel fuels) states := by
  induction fuels generalizing states with
  | nil => trivial
  | cons fuel fuels ih =>
      constructor
      · intro state _
        simpa only [carriedResolveFuel, finiteRefreshStages_fuel, mixedCarriedStage] using
          mixedCarriedStage_loss_le M initial
            (finiteRefreshCandidate M initial clock fallback (fuel + (fuels.sum + finalFuel))
              utility bound loss) unknown who fuel (fuels.sum + finalFuel) rate nonneg atMostOne
            (fun h => utility h who) bound boundNonneg bounded state
      · exact ih _

/-- Fresh finite solves, sampled and remembered during actual execution,
inherit the original lower bound with an explicit accumulated refresh cost. -/
theorem finiteRefresh_inherits_bound (seed : FinDist K)
    (initial : K → Profile M.behavioralSignature) (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (utility : E.History → Fin 2 → ℝ)
    (bound loss rate : ℝ) (nonneg : 0 ≤ rate) (atMostOne : rate ≤ 1)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (cut finalFuel : Nat)
    (fuels : List Nat) (boundNonneg : 0 ≤ bound)
    (bounded : ∀ history, |utility history who| ≤ bound) (lower : ℝ)
    (prior : lower ≤ (privateCarriedContinue M seed initial unknown who cut
      (fuels.sum + finalFuel)).expect (fun h => utility h who)) :
    lower - (fuels.length : ℝ) * (2 * bound * rate) ≤
      (privateRecursiveResolve M seed initial unknown who cut finalFuel
        (finiteRefreshStages M initial clock fallback utility bound loss rate
          nonneg atMostOne finalFuel fuels)).expect (fun h => utility h who) := by
  have result := privateRecursiveResolve_inherits_bound M seed initial unknown who cut finalFuel
    (finiteRefreshStages M initial clock fallback utility bound loss rate
      nonneg atMostOne finalFuel fuels) (fun h => utility h who) (fun _ => 2 * bound * rate) lower
    (by simpa only [finiteRefreshStages_fuel] using prior)
    (finiteRefreshStages_stepBounds M initial clock fallback utility bound loss rate
      nonneg atMostOne finalFuel fuels unknown who boundNonneg bounded _)
  simpa only [finiteRefreshStages_allowance] using result

end GameTheory.ReBeL
