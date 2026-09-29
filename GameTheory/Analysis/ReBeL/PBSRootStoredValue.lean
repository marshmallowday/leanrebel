/-
# Saved public posteriors across rooted and original recursive solves

Decode the actual unfiltered public posterior, retaining its stopped mass.
The internal live-child solve and the fresh original-game solve are different
computations. Only scalar values and seed-blind private security are compared.
-/

import GameTheory.Analysis.ReBeL.PBSRootChildRecursive
import GameTheory.Analysis.ReBeL.CFRDStoredChildDefect

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u v
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)

/-- The actual public-only posterior before any live-child filtering.
Possibility is supplied by the parent's positive live query. -/
def pbsRootPublicPosterior (roots : FinDist E.History)
    (trunk : Profile (pbsRootFullInformation M roots).behavioralSignature)
    (cut remaining : Nat)
    (observations : List M.PublicSignal) (past : List (Option (List M.PublicSignal)))
    (possible : CFRDFactualChildPossible
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots)
      trunk cut remaining (some observations :: past)) :
    PublicBelief (pbsRootFullInformation M roots).toInfoSignals (some observations :: past) :=
  PublicBelief.condition (S := (pbsRootFullInformation M roots).toInfoSignals)
    ((pbsRootFullInformation M roots).runBehavioral trunk cut) (some observations :: past)
    (cfrDFactualChildPossible_public
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots)
      trunk cut remaining (some observations :: past) possible)

/-- Stopped mass divided by the same public reach. This conditional fraction
is not assumed small, and contains no solver tolerance. -/
def pbsRootStoppedFraction (roots : FinDist E.History)
    (trunk : Profile (pbsRootFullInformation M roots).behavioralSignature)
    (cut remaining : Nat)
    (observations : List M.PublicSignal) (past : List (Option (List M.PublicSignal))) : ℝ :=
  ((pbsRootFullInformation M roots).runBehavioral trunk cut).probOf
    {h | publicTrace (pbsRootFullInformation M roots).toInfoSignals h.trace =
      some observations :: past ∧ cfrDCutLive remaining h ≠ true} /
    ((pbsRootFullInformation M roots).runBehavioral trunk cut).probOf
      {h | publicTrace (pbsRootFullInformation M roots).toInfoSignals h.trace =
        some observations :: past}

/-- Decoding preserves the public/live error for every common original
continuation kernel, including an entire retained-draw stage and late tail. -/
theorem pbsRootDecoded_public_error {Outcome : Type v}
    (roots : FinDist E.History)
    (trunk : Profile (pbsRootFullInformation M roots).behavioralSignature)
    (cut remaining : Nat)
    (observations : List M.PublicSignal) (past : List (Option (List M.PublicSignal)))
    (possible : CFRDFactualChildPossible
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots)
      trunk cut remaining (some observations :: past))
    (kernel : E.History → FinDist Outcome) (value : Outcome → ℝ)
    (bound : ℝ) (bounded : ∀ outcome, |value outcome| ≤ bound) :
    let posterior := pbsRootPublicPosterior M roots trunk cut remaining observations past possible
    let child := cfrDFactualChildBelief
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots)
      trunk cut remaining (some observations :: past) possible
    |((pbsRootChildBelief M roots posterior).law.bind kernel).expect value -
      ((pbsRootChildBelief M roots child).law.bind kernel).expect value| ≤
      2 * bound * pbsRootStoppedFraction M roots trunk cut remaining observations past := by
  intro posterior child
  have estimate := cfrDFactualChild_public_error
    (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots)
    trunk cut remaining (some observations :: past) possible
    (fun h => (kernel (pbsRootChildRead roots h)).expect value) bound
    (fun h => FinDist.abs_expect_le_of_abs_bound _ value (fun x _ => bounded x))
  dsimp only [pbsRootChildBelief]
  rw [FinDist.bind_map, FinDist.bind_map, FinDist.expect_bind, FinDist.expect_bind]
  exact estimate

variable {outerObs : List M.PublicSignal}
variable (outer : PublicBelief (fullInformation.{0, u, u, u, u, u} M).toInfoSignals outerObs)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- Independently recompute on the decoded saved public law, while the
internal solver uses its live child. Keep both tolerances and stopped mass. -/
theorem pbsRootStored_fresh_value
    (trunk : Profile (pbsRootFullInformation M outer.law).behavioralSignature)
    (cut remaining : Nat)
    (observations : List M.PublicSignal) (past : List (Option (List M.PublicSignal)))
    (possible : CFRDFactualChildPossible
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law)
      trunk cut remaining (some observations :: past))
    (internalNoise freshNoise : PBSRecursiveDepthNoise.{u})
    (internalNoiseBound : PBSRecursiveDepthNoiseBound internalNoise)
    (freshNoiseBound : PBSRecursiveDepthNoiseBound freshNoise)
    (internalCuts freshCuts : List Nat)
    (internalHorizon : internalCuts.sum = remaining) (freshHorizon : freshCuts.sum = remaining)
    (internalFallback freshFallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h who => payoff who h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ who h, |payoff who h| ≤ bound)
    (internalError freshError : ℝ)
    (internalPositive : 0 < internalError) (freshPositive : 0 < freshError) (who : Fin 2) :
    let posterior := pbsRootPublicPosterior M outer.law trunk cut remaining
      observations past possible
    let child := cfrDFactualChildBelief
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law)
      trunk cut remaining (some observations :: past) possible
    let decodedPublic := pbsRootChildBelief M outer.law posterior
    let decodedChild := pbsRootChildBelief M outer.law child
    let internal := pbsRootChildRecursiveProfile M outer internalNoise internalCuts
      internalFallback payoff bound child internalError
    let fresh := pbsRecursiveDepth freshNoise freshCuts E M freshFallback payoff bound
      decodedPublic freshError
    |(decodedChild.law.bind
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom internal remaining)).expect
        (payoff who) -
      (decodedPublic.law.bind
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom fresh remaining)).expect
        (payoff who)| ≤ internalError + freshError +
      2 * bound * pbsRootStoppedFraction M outer.law trunk cut remaining observations past := by
  intro posterior child decodedPublic decodedChild internal fresh
  have internalNash := pbsRootChildRecursiveProfile_isNash M outer internalNoise
    internalNoiseBound internalCuts internalFallback payoff zeroSum bound nonneg bounded
    child internalError internalPositive
  have freshNash := @pbsRecursiveDepth_isNash.{u} freshNoise freshNoiseBound freshCuts E M
    inferInstance inferInstance freshFallback payoff zeroSum bound nonneg bounded
    observations decodedPublic freshError freshPositive
  rw [internalHorizon] at internalNash
  rw [freshHorizon] at freshNash
  apply @behavioralNash_crossRoot_value_abs_le.{u} E
    (fullInformation.{0, u, u, u, u, u} M) observations observations decodedChild decodedPublic
    internal fresh who remaining payoff zeroSum internalError freshError _
    internalNash freshNash
  intro profile
  have error := pbsRootDecoded_public_error M outer.law trunk cut remaining
    observations past possible
    ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom profile remaining)
    (payoff who) bound (bounded who)
  dsimp only at error
  rw [abs_sub_comm] at error
  exact error

/-- Fresh private execution on the unfiltered saved MODEL law secures the
decoded internal self-play value, with an extra fresh tolerance. The unknown
opponent cannot observe the private draw. This is not factual calibration. -/
theorem pbsRootStored_fresh_security
    (trunk : Profile (pbsRootFullInformation M outer.law).behavioralSignature)
    (cut remaining : Nat)
    (observations : List M.PublicSignal) (past : List (Option (List M.PublicSignal)))
    (possible : CFRDFactualChildPossible
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law)
      trunk cut remaining (some observations :: past))
    (internalNoise freshNoise : PBSRecursiveDepthNoise.{u})
    (internalNoiseBound : PBSRecursiveDepthNoiseBound internalNoise)
    (freshNoiseBound : PBSRecursiveDepthNoiseBound freshNoise)
    (internalCuts freshCuts : List Nat)
    (internalHorizon : internalCuts.sum = remaining) (freshHorizon : freshCuts.sum = remaining)
    (internalFallback freshFallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h who => payoff who h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ who h, |payoff who h| ≤ bound)
    (internalError freshError : ℝ)
    (internalPositive : 0 < internalError) (freshPositive : 0 < freshError)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (who : Fin 2) :
    let posterior := pbsRootPublicPosterior M outer.law trunk cut remaining
      observations past possible
    let child := cfrDFactualChildBelief
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law)
      trunk cut remaining (some observations :: past) possible
    let decodedPublic := pbsRootChildBelief M outer.law posterior
    let decodedChild := pbsRootChildBelief M outer.law child
    let internal := pbsRootChildRecursiveProfile M outer internalNoise internalCuts
      internalFallback payoff bound child internalError
    (decodedChild.law.bind
      ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom internal remaining)).expect
        (payoff who) - (internalError + 2 * freshError +
          2 * bound * pbsRootStoppedFraction M outer.law trunk cut remaining observations past) ≤
      (pbsRecursiveDepthDraw freshNoise freshCuts M freshFallback payoff bound
        decodedPublic freshError).expect
        (fun chosen => (decodedPublic.law.bind
          ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom
            (Profile.update unknown who (chosen who)) remaining)).expect (payoff who)) := by
  intro posterior child decodedPublic decodedChild internal
  have gap := pbsRootStored_fresh_value M outer trunk cut remaining observations past possible
    internalNoise freshNoise internalNoiseBound freshNoiseBound internalCuts freshCuts
    internalHorizon freshHorizon internalFallback freshFallback payoff zeroSum bound nonneg bounded
    internalError freshError internalPositive freshPositive who
  have security := pbsRecursiveDepth_private_model_security M freshNoise freshNoiseBound freshCuts
    freshFallback payoff zeroSum bound nonneg bounded decodedPublic freshError freshPositive
    unknown who
  dsimp only at gap security
  rw [freshHorizon] at security
  have upper := (abs_le.mp gap).2
  linarith only [upper, security]

end GameTheory.ReBeL
