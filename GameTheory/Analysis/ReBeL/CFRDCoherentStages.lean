/-
# Repeated coherent private draws with actual carried memory

Every active stage independently realizes the same retained parent family.
The canonical state machine retains all draws and updates its model belief.
With all continuation fuel covered by the finite schedule, the entire law
is unchanged. This is not fresh independent solving of a new PBS game.
-/

import GameTheory.Analysis.ReBeL.CFRDFiniteCoherent
import GameTheory.Analysis.ReBeL.CFRDRecursivePlay

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] {K : Type*}

/-- The original private parent index selects the family at every stage.
Current hidden history and the unknown opposing policy are never query inputs. -/
def cfrDCoherentStage (fallback : Profile M.strategicSignature)
    (plays : K → Profile M.behavioralSignature) (fuel : Nat) : CarriedResolveStage M K where
  fuel := fuel
  resolver := fun memory _ _ => cfrDPolicyDraw M fallback (plays memory.1)

/-- One real step followed by the same parent's behavioral continuation has
that parent's joint history law. The stored pure draw need not equal the parent. -/
theorem cfrDCoherentStage_then (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (plays : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (fuel remaining : Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K)) :
    (carriedMemoryStep M plays unknown who (cfrDCoherentStage M fallback plays fuel) state).bind
        (fun next => M.runBehavioralFrom
          (Profile.update unknown who (plays next.iteration.1 who)) remaining next.history) =
      M.runBehavioralFrom (Profile.update unknown who (plays state.iteration.1 who))
        (fuel + remaining) state.history := by
  change ((carriedResolvedStep M (carriedMemoryProfile M plays)
    (fun memory _ _ => cfrDPolicyDraw M fallback (plays memory.1))
    unknown who fuel state).map (storeCarriedDraw M)).bind
      (fun next => M.runBehavioralFrom
        (Profile.update unknown who (plays next.iteration.1 who)) remaining next.history) = _
  by_cases live : cfrDCutLive fuel state.history = true
  · simp only [carriedResolvedStep, if_pos live,
      FinDist.bind_map, FinDist.bind_bind, storeCarriedDraw, resolvedNextState]
    rw [← FinDist.bind_bind, cfrDPolicyDraw_run M hrecall]
    exact (M.runBehavioralFrom_add _ fuel remaining state.history).symm
  · simp only [carriedResolvedStep, if_neg live,
      FinDist.bind_map, FinDist.pure_bind, storeCarriedDraw]
    rw [M.runBehavioralFrom_add,
      cfrD_run_stopped M _ fuel state.history live, FinDist.pure_bind]

/-- A finite list covers all execution fuel; zero-fuel entries still use the
canonical no-query branch and contribute zero to the overall horizon. -/
theorem cfrDCoherentStages_fuel (fallback : Profile M.strategicSignature)
    (plays : K → Profile M.behavioralSignature) (schedule : List Nat) :
    carriedResolveFuel M 0 (schedule.map (cfrDCoherentStage M fallback plays)) = schedule.sum := by
  induction schedule with
  | nil => rfl
  | cons fuel schedule ih =>
      simpa only [List.map_cons, carriedResolveFuel, cfrDCoherentStage, List.sum_cons] using
        congrArg (fun remaining => fuel + remaining) ih

/-- Fresh independent plan draws at every active stage preserve the entire
law from an arbitrary memory/history/model-belief state. No expected-value
comparison, reference-support assumption or per-draw safety is supplied. -/
theorem cfrDCoherentStages_run (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (plays : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (schedule : List Nat)
    (state : PrivateIterationState M (CarriedResolveMemory M K)) :
    executeCarriedResolves M plays unknown who 0
        (schedule.map (cfrDCoherentStage M fallback plays)) state =
      M.runBehavioralFrom (Profile.update unknown who (plays state.iteration.1 who))
        schedule.sum state.history := by
  induction schedule generalizing state with
  | nil => rfl
  | cons fuel schedule ih =>
      simp only [List.map_cons, List.sum_cons, executeCarriedResolves]
      calc
        _ = (carriedMemoryStep M plays unknown who
              (cfrDCoherentStage M fallback plays fuel) state).bind
            (fun next => M.runBehavioralFrom
              (Profile.update unknown who (plays next.iteration.1 who))
              schedule.sum next.history) := by
          apply FinDist.bind_congr
          intro next _
          exact ih next
        _ = _ := cfrDCoherentStage_then M hrecall fallback plays unknown who fuel schedule.sum state

/-- The real unknown-opponent prefix and every carried posterior are retained
by the state machine. Coherent repeated draws recover the parent's whole law
without an accumulated replacement penalty. -/
theorem cfrDCoherentStages_recursive_eq (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (seed : FinDist K)
    (plays : K → Profile M.behavioralSignature) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut : Nat) (schedule : List Nat) :
    privateRecursiveResolve M seed plays unknown who cut 0
        (schedule.map (cfrDCoherentStage M fallback plays)) =
      privateCarriedContinue M seed plays unknown who cut schedule.sum := by
  unfold privateRecursiveResolve privateCarriedContinue
  rw [FinDist.bind_map]
  apply FinDist.bind_congr
  intro state _
  exact cfrDCoherentStages_run M hrecall fallback plays unknown who schedule
    (enterCarriedMemory M state)

variable [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]
variable [∀ who, DecidableEq ((fullInformation M).InfoState who)]

/-- The actual finite-child outer recurrence supports any finite coherent
schedule with no stage-count penalty. Numerical, child and outer errors remain;
the theorem is not permission to substitute a different child policy family. -/
theorem cfrDFiniteCoherentStages_security
    (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut : Nat) (schedule : List Nat)
    (bound error loss : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ who h, |payoff who h| ≤ bound) (noise : CFRDPredictionNoise M)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (reference : Profile (fullInformation M).behavioralSignature)
    (equilibrium : IsNash ((fullInformation M).toBehavioralGameForm (cut + schedule.sum))
      (euPreference (fun h who => payoff who h)) reference)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (t : Nat) [NeZero t] :
    let plays := fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
      fallback payoff cut schedule.sum
      (cfrDConstructedFiniteOracle M fallback payoff cut schedule.sum bound loss noise) n.val
    ((fullInformation M).runBehavioral reference (cut + schedule.sum)).expect (payoff who) -
      ((cfrDDepthErrorConstant (fullInformation M) (fullObservationClock M)
            fallback cut schedule.sum 0 +
          cfrDDepthErrorConstant (fullInformation M) (fullObservationClock M)
            fallback cut schedule.sum 1) * error +
        (cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
            fallback cut schedule.sum bound 0 +
          cfrDDepthFiniteConstant (fullInformation M) (fullObservationClock M)
            fallback cut schedule.sum bound 1) / Real.sqrt t + 2 * loss) ≤
      (privateRecursiveResolve (fullInformation M) (cfrIterationLaw t) plays
        unknown who cut 0
        (schedule.map (cfrDCoherentStage (fullInformation M) fallback plays))).expect
        (payoff who) := by
  dsimp only
  rw [cfrDCoherentStages_recursive_eq (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals)]
  exact cfrDConstructedFiniteOracle_carried_security M fallback payoff zeroSum cut schedule.sum
    bound error loss hb he hl bounded noise noiseBound reference equilibrium unknown who t

end GameTheory.ReBeL
