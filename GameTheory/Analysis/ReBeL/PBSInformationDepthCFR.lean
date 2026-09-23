/-
# Depth-limited sampled-value solving of an original public belief

Decode the constructed noisy rooted CFR-D recurrence through each player's
own AOH. Both all-deviation Nash and actual-iteration sampling transfer back
to the original continuation game, with the same finite-time error budget.
This does not identify a model PBS with an unknown opponent's actual posterior.
-/

import GameTheory.Analysis.ReBeL.PBSRootDepthCFR

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {observations : List M.PublicSignal}

/-- The original local strategy computed by the noisy depth-limited root.
Only the supplied joint belief determines the new game's initial chance law. -/
def pbsInformationDepthCFR
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : PBSRootDepthNoise M belief.law)
    (t : Nat) [NeZero t] : Profile (fullInformation M).behavioralSignature :=
  pbsRootDecodeProfile M belief.law (observations.length - 1)
    (pbsRootDepthAverage M belief.law fallback payoff cut remaining bound loss noise t)

/-- An actual decoded parent iterate, with that round's completed child
continuation, not a newly substituted equilibrium or an averaged private seed. -/
def pbsInformationDepthCFRIterate
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : PBSRootDepthNoise M belief.law)
    (round : Nat) : Profile (fullInformation M).behavioralSignature :=
  pbsRootDecodeProfile M belief.law (observations.length - 1)
    (pbsRootDepthIterate M belief.law fallback payoff cut remaining bound loss noise round)

/-- Every original behavioral deviation is covered. Prediction noise, child
loss and the finite parent-iteration term survive the chance-root translation.
The one administrative step is not mistaken for an original game transition. -/
theorem pbsInformationDepthCFR_isNash
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun history who => payoff who history)) (cut remaining : Nat)
    (bound error loss : ℝ) (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (noise : PBSRootDepthNoise M belief.law)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (t : Nat) [NeZero t] :
    IsNash (behavioralBeliefForm (fullInformation M) belief (cut + remaining))
      (euPreferenceWithin
        (pbsRootDepthBudget M belief.law fallback cut remaining bound error loss t)
        (fun history who => payoff who history))
      (pbsInformationDepthCFR M belief fallback payoff cut remaining bound loss noise t) := by
  apply pbsRootDecodeProfile_isNash
  have horizon : cut + 1 + remaining = cut + remaining + 1 := by omega
  rw [← horizon]
  exact pbsRootDepthAverage_isNash M belief.law fallback payoff zeroSum
    cut remaining bound error loss hb he hl bounded noise noiseBound t

/-- Uniform private sampling of actual decoded depth-limited iterates has
exactly the averaged strategy's original history law against fixed opponents.
This is a law identity, not an assumption that each sampled iterate is Nash. -/
theorem pbsInformationDepthCFR_sampling_law
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : PBSRootDepthNoise M belief.law)
    (t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat) :
    (cfrIterationLaw t).bind (fun n => belief.law.bind
      ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationDepthCFRIterate M belief fallback payoff
          cut remaining bound loss noise n.val who)) steps)) =
      belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationDepthCFR M belief fallback payoff
          cut remaining bound loss noise t who)) steps) := by
  have equal := congrArg
    (fun law : FinDist (pbsRootProtocol belief.law).History => law.map History.state)
    (pbsRootDepthAverage_uniform_law M belief.law fallback payoff cut remaining bound loss
      noise t (pbsRootBehavioralFullProfile M belief.law unknown) who steps)
  rw [FinDist.map_bind] at equal
  simp_rw [pbsRootDecodeOwn_law M belief.law (observations.length - 1)
    (pbsRoot_publicBelief_depth M belief)] at equal
  rw [← FinDist.map_bind] at equal
  apply FinDist.map_injective (Option.some_injective E.History)
  exact equal.symm

/-- Root chance and the private iterate draw may be exchanged, while the
selected iterate is held fixed for the whole continuation. -/
theorem pbsInformationDepthCFR_delayed_sampling
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : PBSRootDepthNoise M belief.law)
    (t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat) :
    belief.law.bind (fun history => (cfrIterationLaw t).bind (fun n =>
      (fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationDepthCFRIterate M belief fallback payoff
          cut remaining bound loss noise n.val who)) steps history)) =
      belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationDepthCFR M belief fallback payoff
          cut remaining bound loss noise t who)) steps) := by
  rw [FinDist.bind_comm]
  exact pbsInformationDepthCFR_sampling_law M belief fallback payoff cut remaining bound loss
    noise t unknown who steps

/-- The value consumer receives the expectation of the same finite private
iteration family. Arbitrary original-history observables are preserved. -/
theorem pbsInformationDepthCFR_sampling_value
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : PBSRootDepthNoise M belief.law)
    (t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2) (steps : Nat)
    (value : E.History → ℝ) :
    (cfrIterationLaw t).expect (fun n => (belief.law.bind
      ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationDepthCFRIterate M belief fallback payoff
          cut remaining bound loss noise n.val who)) steps)).expect value) =
      (belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationDepthCFR M belief fallback payoff
          cut remaining bound loss noise t who)) steps)).expect value := by
  have equal := congrArg (fun law : FinDist E.History => law.expect value)
    (pbsInformationDepthCFR_sampling_law M belief fallback payoff cut remaining bound loss
      noise t unknown who steps)
  simpa only [FinDist.expect_bind] using equal

end GameTheory.ReBeL
