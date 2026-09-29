/-
# Comparing actual recursive solves on saved public and live-child PBSs

The two solvers recompute their policies independently. Cross deviations and
the uniform fixed-profile stopped-mass bound compare their scalar self-play
values. The actual public posterior is never silently filtered before solving.
-/

import GameTheory.Analysis.ReBeL.PBSRecursiveValueStability
import GameTheory.Analysis.ReBeL.CFRDStoredChildDefect

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- Independent recursive searches on the public-only and live-child inputs
have a scalar error consisting of two solve tolerances and explicit discarded
conditional mass. Noise families, fallbacks and cut partitions may differ. -/
theorem cfrDStoredChild_recursive_value_error
    (trunk : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (cut remaining : Nat) (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs)
    (firstNoise secondNoise : PBSRecursiveDepthNoise.{u})
    (firstNoiseBound : PBSRecursiveDepthNoiseBound firstNoise)
    (secondNoiseBound : PBSRecursiveDepthNoiseBound secondNoise)
    (firstCuts secondCuts : List Nat) (firstHorizon : firstCuts.sum = remaining)
    (secondHorizon : secondCuts.sum = remaining)
    (firstFallback secondFallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h p => payoff p h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ player h, |payoff player h| ≤ bound)
    (firstError secondError : ℝ) (firstPositive : 0 < firstError)
    (secondPositive : 0 < secondError) (who : Fin 2) :
    let posterior := PublicBelief.condition
      (S := (fullInformation.{0, u, u, u, u, u} M).toInfoSignals)
      ((fullInformation.{0, u, u, u, u, u} M).runBehavioral trunk cut) obs
      (cfrDFactualChildPossible_public M trunk cut remaining obs possible)
    let child := cfrDFactualChildBelief M trunk cut remaining obs possible
    let first := pbsRecursiveDepth firstNoise firstCuts E M firstFallback payoff bound
      posterior firstError
    let second := pbsRecursiveDepth secondNoise secondCuts E M secondFallback payoff bound
      child secondError
    |(posterior.law.bind
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom first remaining)).expect
        (payoff who) -
      (child.law.bind
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom second remaining)).expect
        (payoff who)| ≤ firstError + secondError + 2 * bound *
      (((fullInformation.{0, u, u, u, u, u} M).runBehavioral trunk cut).probOf
        {h | publicTrace (fullInformation.{0, u, u, u, u, u} M).toInfoSignals h.trace = obs ∧
          cfrDCutLive remaining h ≠ true} /
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioral trunk cut).probOf
          {h | publicTrace (fullInformation.{0, u, u, u, u, u} M).toInfoSignals
            h.trace = obs}) := by
  intro posterior child first second
  have estimate := pbsRecursiveDepth_crossQuery_value_error M firstNoise secondNoise
    firstNoiseBound secondNoiseBound firstCuts secondCuts
    (firstHorizon.trans secondHorizon.symm) firstFallback secondFallback payoff zeroSum bound
    nonneg bounded posterior child firstError secondError firstPositive secondPositive who _
    (fun profile => cfrDFactualChild_public_continuation_error M trunk cut remaining obs possible
      ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom profile firstCuts.sum)
      (payoff who) bound (bounded who))
  simpa only [firstHorizon, secondHorizon] using estimate

end GameTheory.ReBeL
