/-
# Recursive carried information-set solving and missing-PBS loss

The deployed chain uses fresh child iterations at each available stored PBS.
On a missing-model branch every later stage retains the most recent policy,
so the entire canonical continuation law and every payoff are unchanged.
The remaining replacement loss is localized to states with an available PBS.
This is not a bound for those supported branches or a per-iterate guarantee.
-/

import GameTheory.Analysis.ReBeL.CFRDInformationResolve
import GameTheory.Analysis.ReBeL.CFRDInformationSampledDriver

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {K : Type*}

/-- The complete recursive chain at a missing model PBS is exactly the
incumbent continuation. The incumbent is the newest stored draw, not the
initial policy. No reach domination or opponent-model premise is supplied. -/
theorem cfrDInformationResolveStages_run_none
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (bound loss : ℝ) (finalFuel : Nat) (schedule : List Nat)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) (missing : state.belief = none) :
    executeCarriedResolves (fullInformation M) initial unknown who finalFuel
        (cfrDInformationResolveStages M initial fallback payoff bound loss finalFuel schedule)
        state =
      (fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (carriedMemoryProfile (fullInformation M) initial state.iteration who))
        (schedule.sum + finalFuel) state.history := by
  induction schedule generalizing state with
  | nil =>
      simp only [cfrDInformationResolveStages, executeCarriedResolves, carriedSelectedTail,
        List.sum_nil, Nat.zero_add]
  | cons fuel schedule ih =>
      simp only [cfrDInformationResolveStages, executeCarriedResolves, List.sum_cons]
      rw [cfrDInformationResolveStage_none M initial fallback payoff
        (fuel + schedule.sum + finalFuel) fuel bound loss unknown who state missing,
        FinDist.bind_map]
      calc
        _ = ((fullInformation M).runBehavioralFrom
              (Profile.update unknown who
                (carriedMemoryProfile (fullInformation M) initial state.iteration who))
              fuel state.history).bind
            ((fullInformation M).runBehavioralFrom
              (Profile.update unknown who
                (carriedMemoryProfile (fullInformation M) initial state.iteration who))
              (schedule.sum + finalFuel)) := by
          apply FinDist.bind_congr
          intro history _
          exact ih (cfrDInformationMissingNext M initial state history) rfl
        _ = _ := by
          rw [← (fullInformation M).runBehavioralFrom_add, Nat.add_assoc]

/-- Full-schedule replacement loss relative to the newest retained policy.
This observable makes no claim that an individual stored draw is optimal. -/
def cfrDInformationResolveLoss
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (bound loss : ℝ) (finalFuel : Nat) (schedule : List Nat)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (value : E.History → ℝ)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) : ℝ :=
  ((fullInformation M).runBehavioralFrom
    (Profile.update unknown who
      (carriedMemoryProfile (fullInformation M) initial state.iteration who))
    (schedule.sum + finalFuel) state.history).expect value -
  (executeCarriedResolves (fullInformation M) initial unknown who finalFuel
    (cfrDInformationResolveStages M initial fallback payoff bound loss finalFuel schedule)
    state).expect value

/-- Missing model support contributes zero ADDITIONAL replacement loss even
with positive fuel, nonempty private memory and an arbitrary fixed opponent. -/
theorem cfrDInformationResolveLoss_none
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (bound loss : ℝ) (finalFuel : Nat) (schedule : List Nat)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (value : E.History → ℝ)
    (state : PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K)) (missing : state.belief = none) :
    cfrDInformationResolveLoss M initial fallback payoff bound loss finalFuel schedule
      unknown who value state = 0 := by
  unfold cfrDInformationResolveLoss
  rw [cfrDInformationResolveStages_run_none M initial fallback payoff bound loss finalFuel
    schedule unknown who state missing, sub_self]

/-- The actual expected replacement loss is supported only where a model PBS
is available. This exact decomposition does not bound the remaining term or
replace an actual state law by a model law. -/
theorem cfrDInformationResolveLoss_supported_part
    (initial : K → Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (bound loss : ℝ) (finalFuel : Nat) (schedule : List Nat)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (value : E.History → ℝ)
    (states : FinDist (PrivateIterationState (fullInformation M)
      (CarriedResolveMemory (fullInformation M) K))) :
    states.expect (cfrDInformationResolveLoss M initial fallback payoff bound loss finalFuel
      schedule unknown who value) =
      states.expect (fun state => state.belief.elim 0 (fun _ =>
        cfrDInformationResolveLoss M initial fallback payoff bound loss finalFuel schedule
          unknown who value state)) := by
  apply FinDist.expect_congr
  intro state _
  cases present : state.belief with
  | none => exact cfrDInformationResolveLoss_none M initial fallback payoff
      bound loss finalFuel schedule unknown who value state present
  | some belief => rfl

/-- The new draw has a derived positive-loss deviation bound on its own joint
PBS. No Nash witness is given to the solver and no individual-iterate bound
is inferred. Transferring this to a changed carried law remains separate. -/
theorem cfrDInformationResolveDraw_gain_le {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel : Nat) (bound loss : ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h))
    (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ h who, |payoff who h| ≤ bound)
    (who : Fin 2) (target : (fullInformation M).BehavioralPolicy who) :
    let average := pbsInformationConditionalProfile M belief fallback fuel
      (fun h player => payoff player h) bound loss
    (belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update average who target) fuel)).expect (payoff who) -
      ((cfrDInformationResolveDraw M belief fallback payoff fuel bound loss).bind
        (fun chosen => belief.law.bind ((fullInformation M).runBehavioralFrom
          (Profile.update average who (chosen who)) fuel))).expect (payoff who) ≤
        belief.law.positiveMassFloor * loss := by
  dsimp only
  rw [cfrDInformationResolveDraw_law, Profile.update_eq_self]
  have equilibrium := pbsInformationConditionalProfile_isNash M belief fallback fuel
    (fun h player => payoff player h) zeroSum bound loss nonneg positive bounded
  rw [isNash_iff] at equilibrium
  exact sub_le_iff_le_add.mpr (equilibrium who target)

variable [∀ who info, Fintype ((fullInformation M).Choice who info)]
variable [∀ who, DecidableEq ((fullInformation M).InfoState who)]

/-- Deploy the ACTUAL noisy sampled-value parent, then re-solve each available
carried PBS with a fresh information-set draw. The opponent is fixed outside
all private draws. This defines the remaining recursive safety target. -/
def cfrDInformationRecursivePlay (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut finalFuel : Nat) (schedule : List Nat)
    (bound loss : ℝ) (noise : CFRDPredictionNoise M) (t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) :
    FinDist E.History :=
  let remaining := schedule.sum + finalFuel
  let plays := fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
    (cfrDInformationFallback M fallback) payoff cut remaining
    (cfrDConstructedSampledInformationOracle M fallback payoff cut remaining bound loss noise)
    n.val
  privateRecursiveResolve (fullInformation M) (cfrIterationLaw t) plays unknown who cut finalFuel
    (cfrDInformationResolveStages M plays fallback payoff bound loss finalFuel schedule)

/-- An empty re-solving schedule recovers the previously proved retained
sampled-value parent, with exactly the same perturbation and outer iterations. -/
theorem cfrDInformationRecursivePlay_nil (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut finalFuel : Nat)
    (bound loss : ℝ) (noise : CFRDPredictionNoise M) (t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) :
    cfrDInformationRecursivePlay M fallback payoff cut finalFuel [] bound loss noise t
      unknown who =
      privateCarriedContinue (fullInformation M) (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay (fullInformation M) (fullObservationClock M)
          (cfrDInformationFallback M fallback) payoff cut finalFuel
          (cfrDConstructedSampledInformationOracle M fallback payoff cut finalFuel
            bound loss noise) n.val) unknown who cut finalFuel := by
  simp only [cfrDInformationRecursivePlay, List.sum_nil, Nat.zero_add,
    cfrDInformationResolveStages, privateRecursiveResolve_nil]

end GameTheory.ReBeL
