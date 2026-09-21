/-
# Sampling the actual information-set child iterations

The private index is uniform over the very CFR iterates used by the child's
own-reach average. Decode each iterate through the original local AOH. The
resulting complete history law equals the computed averaged policy against
any fixed behavioral opponent. The root law remains the supplied joint PBS;
this is not an identification with an unknown opponent's actual posterior.
-/

import GameTheory.Analysis.ReBeL.PBSInformationCFR

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)

/-- An arbitrary rooted policy, playing against fixed original opponents,
decodes with no change to the complete original continuation law. -/
theorem pbsRootDecodeOwn_law (roots : FinDist E.History) (cut : Nat)
    (rootDepth : ∀ history ∈ roots.support, history.trace.length = cut)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (policy : (pbsRootFullInformation M roots).BehavioralPolicy who) (steps : Nat) :
    ((pbsRootFullInformation M roots).runBehavioral
      (Profile.update (pbsRootBehavioralFullProfile M roots unknown) who policy)
      (steps + 1)).map History.state =
        (roots.bind ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who (pbsRootDecodePolicy M roots cut who policy))
          steps)).map some := by
  simpa only [pbsRootDecodeProfile_update, pbsRootDecodeProfile_lift] using
    pbsRootDecodeProfile_law M roots cut rootDepth
      (Profile.update (pbsRootBehavioralFullProfile M roots unknown) who policy) steps

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

section Native

variable (roots : FinDist E.History)

local instance samplingHistoryFintype : Fintype (pbsRootProtocol roots).History :=
  pbsRootHistoryFintype roots

local instance samplingInfoDecidableEq (who : Fin 2) :
    DecidableEq ((pbsRootFullInformation M roots).InfoState who) := Classical.decEq _

local instance samplingChoiceFintype (who : Fin 2)
    (info : (pbsRootFullInformation M roots).InfoState who) :
    Fintype ((pbsRootFullInformation M roots).Choice who info) := by
  classical
  infer_instance

/-- One genuine information-set regret-matching iterate. No fresh equilibrium
or deterministic complete-plan learner is substituted for the recurrence. -/
def pbsRootCFRIterate (fallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ) (fuel round : Nat) :
    Profile (pbsRootFullInformation M roots).behavioralSignature :=
  cfrPlay (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (pbsRootFallback M roots fallback) (pbsRootPayoff roots payoff) (fuel + 1) round

/-- A private uniform draw realizes the child's actual own-reach average.
The execution fuel need not equal the horizon used to train the recurrence. -/
theorem pbsRootCFR_uniform_law (fallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ) (fuel t : Nat) [NeZero t]
    (unknown : Profile (pbsRootFullInformation M roots).behavioralSignature)
    (who : Fin 2) (steps : Nat) :
    (pbsRootFullInformation M roots).runBehavioral
      (Profile.update unknown who (pbsRootCFR M roots fallback payoff fuel t who))
      (steps + 1) =
        (cfrIterationLaw t).bind (fun n => (pbsRootFullInformation M roots).runBehavioral
          (Profile.update unknown who (pbsRootCFRIterate M roots fallback payoff fuel n.val who))
          (steps + 1)) := by
  exact run_unilateral_average (pbsRootFullInformation M roots)
    (fullSignals_perfectRecall (pbsRootInformation (fullInformation M) roots).toInfoSignals)
    (fun _ => cfrIterationLaw t)
    (fun n : Fin t => pbsRootCFRIterate M roots fallback payoff fuel n.val)
    (pbsRootFallback M roots fallback) unknown who (steps + 1)

end Native

variable {observations : List M.PublicSignal}

/-- Decode the same child iterate into an original information-local policy. -/
def pbsInformationCFRIterate
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (fuel round : Nat) : Profile (fullInformation M).behavioralSignature :=
  pbsRootDecodeProfile M belief.law (observations.length - 1)
    (pbsRootCFRIterate M belief.law fallback payoff fuel round)

/-- Uniformly selecting the actual decoded child iterate preserves the whole
law, not just expected payoff. The unknown opponents stay outside the draw. -/
theorem pbsInformationCFR_sampling_law
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) :
    (cfrIterationLaw t).bind (fun n => belief.law.bind
      ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFRIterate M belief fallback payoff
          fuel n.val who)) steps)) =
      belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFR M belief fallback payoff fuel t who))
        steps) := by
  have equal := congrArg
    (fun law : FinDist (pbsRootProtocol belief.law).History => law.map History.state)
    (pbsRootCFR_uniform_law M belief.law fallback payoff fuel t
      (pbsRootBehavioralFullProfile M belief.law unknown) who steps)
  rw [FinDist.map_bind] at equal
  simp_rw [pbsRootDecodeOwn_law M belief.law (observations.length - 1)
    (pbsRoot_publicBelief_depth M belief)] at equal
  rw [← FinDist.map_bind] at equal
  apply FinDist.map_injective Option.some_injective
  exact equal.symm

/-- The child iteration index can be drawn after the independent joint-root
chance draw, with the same law. It is retained throughout the continuation. -/
theorem pbsInformationCFR_delayed_sampling
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) :
    belief.law.bind (fun history => (cfrIterationLaw t).bind (fun n =>
      (fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFRIterate M belief fallback payoff
          fuel n.val who)) steps history)) =
      belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFR M belief fallback payoff fuel t who))
        steps) := by
  rw [FinDist.bind_comm]
  exact pbsInformationCFR_sampling_law M belief fallback payoff fuel t unknown who steps

/-- The actual child values are the mean of the same decoded iteration family.
This identity alone makes no individual-iterate optimality claim. -/
theorem pbsInformationCFR_sampling_value
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) (value : E.History → ℝ) :
    (cfrIterationLaw t).expect (fun n => (belief.law.bind
      ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFRIterate M belief fallback payoff
          fuel n.val who)) steps)).expect value) =
      (belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFR M belief fallback payoff fuel t who))
        steps)).expect value := by
  have equal := congrArg (fun law : FinDist E.History => law.expect value)
    (pbsInformationCFR_sampling_law M belief fallback payoff fuel t unknown who steps)
  simpa only [FinDist.expect_bind] using equal

end GameTheory.ReBeL
