/-
# Native conditional value gaps of the noisy depth-limited parent

The actual private parent iterates, including their computed child continuations,
are compared against the SAME computed average opponent. Their nonnegative
conditional best-response gaps average to the average policy's gap. The bound
retains prediction noise, positive child tolerance and finite parent iterations.
Selecting an actual execution event costs its actual probability denominator;
it does not replace the original conditional kernels with a changed PBS.
-/

import GameTheory.Analysis.ReBeL.PBSConditionalValueStability
import GameTheory.Analysis.ReBeL.PBSCarriedDepthSampling
import GameTheory.Analysis.ReBeL.PBSInformationDepthBudget
import GameTheory.Math.Probability.FinDistSelection

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk ut
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {observations : List M.PublicSignal} {who : Fin 2} {T : Type ut}

/-- Supported type conditioning preserves the actual noisy parent's sampling
identity. The opposing policies and execution horizon are arbitrary but fixed. -/
theorem pbsInformationDepthCFR_conditional_sampling_value
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M (slice.mixture own).law) (t : Nat) [NeZero t]
    (opponents : Profile (fullInformation M).behavioralSignature)
    (steps : Nat) (value : E.History → ℝ) (type : T) (supported : type ∈ own.support) :
    (cfrIterationLaw t).expect (fun n => slice.conditionalPayoff opponents steps value
        (pbsInformationDepthCFRIterate M (slice.mixture own) fallback payoff cut remaining
          bound loss noise n.val who) type) =
      slice.conditionalPayoff opponents steps value
        (pbsInformationDepthCFR M (slice.mixture own) fallback payoff cut remaining
          bound loss noise t who) type := by
  unfold TypeBeliefSlice.conditionalPayoff PublicBelief.continuationLaw
  simp only [FinDist.expect_bind]
  rw [FinDist.expect_comm]
  apply FinDist.expect_congr
  intro history reached
  have inRoot : history ∈ (slice.mixture own).law.support := by
    rw [TypeBeliefSlice.mixture, FinDist.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨type, supported, reached⟩
  have same := congrArg (fun law : FinDist E.History => law.expect value)
    (pbsInformationDepthCFR_sampling_from_support M (slice.mixture own) fallback payoff
      cut remaining bound loss noise t opponents who steps history inRoot)
  simpa only [FinDist.expect_bind] using same

/-- One actual depth-limited parent draw's conditional best-response gap.
Only the own iterate is sampled; its opponent is the fixed computed average,
not its same-index opposing iterate and not a separately recomputed opponent. -/
def pbsInformationDepthCFRConditionalDrawGap
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M (slice.mixture own).law) (t : Nat) [NeZero t]
    (type : T) (round : Fin t) : ℝ :=
  let average := pbsInformationDepthCFR M (slice.mixture own) fallback payoff cut remaining
    bound loss noise t
  slice.infoValue (fun player => liftPolicy M player (fallback player)) (cut + remaining)
      (payoff who) average type -
    slice.conditionalPayoff average (cut + remaining) (payoff who)
      (pbsInformationDepthCFRIterate M (slice.mixture own) fallback payoff cut remaining
        bound loss noise round.val who) type

/-- Nonnegativity is per draw, including absent types. It follows from legal
best-response domination, not a per-iterate Nash or numerical accuracy claim. -/
theorem pbsInformationDepthCFRConditionalDrawGap_nonneg
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M (slice.mixture own).law) (t : Nat) [NeZero t]
    (type : T) (round : Fin t) :
    0 ≤ pbsInformationDepthCFRConditionalDrawGap M slice own fallback payoff cut remaining
      bound loss noise t type round :=
  sub_nonneg.mpr (slice.conditionalPayoff_le_infoValue
    (fullSignals_perfectRecall M.toInfoSignals)
    (fun player => liftPolicy M player (fallback player)) (cut + remaining) (payoff who)
    (pbsInformationDepthCFR M (slice.mixture own) fallback payoff cut remaining bound loss noise t)
    type (pbsInformationDepthCFRIterate M (slice.mixture own) fallback payoff cut remaining
      bound loss noise round.val who))

/-- The mean absolute draw gap equals the average gap on supported types.
Absolute value is removed using the preceding sign theorem, not commuted with
expectation for an arbitrary signed quantity. -/
theorem pbsInformationDepthCFRConditionalDrawGap_mean_abs
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M (slice.mixture own).law) (t : Nat) [NeZero t]
    (type : T) (supported : type ∈ own.support) :
    let average := pbsInformationDepthCFR M (slice.mixture own) fallback payoff cut remaining
      bound loss noise t
    (cfrIterationLaw t).expect (fun n => |pbsInformationDepthCFRConditionalDrawGap M slice own
        fallback payoff cut remaining bound loss noise t type n|) =
      |slice.infoValue (fun player => liftPolicy M player (fallback player)) (cut + remaining)
          (payoff who) average type -
        slice.conditionalPayoff average (cut + remaining) (payoff who) (average who) type| := by
  let average := pbsInformationDepthCFR M (slice.mixture own) fallback payoff cut remaining
    bound loss noise t
  calc
    _ = (cfrIterationLaw t).expect (pbsInformationDepthCFRConditionalDrawGap M slice own
        fallback payoff cut remaining bound loss noise t type) := by
      apply FinDist.expect_congr
      intro n _
      exact abs_of_nonneg (pbsInformationDepthCFRConditionalDrawGap_nonneg M slice own
        fallback payoff cut remaining bound loss noise t type n)
    _ = slice.infoValue (fun player => liftPolicy M player (fallback player)) (cut + remaining)
          (payoff who) average type -
        slice.conditionalPayoff average (cut + remaining) (payoff who) (average who) type := by
      unfold pbsInformationDepthCFRConditionalDrawGap
      rw [FinDist.expect_sub, FinDist.expect_const,
        pbsInformationDepthCFR_conditional_sampling_value M slice own fallback payoff
          cut remaining bound loss noise t average (cut + remaining) (payoff who) type supported]
    _ = _ := (abs_of_nonneg (sub_nonneg.mpr (slice.conditionalPayoff_le_infoValue
      (fullSignals_perfectRecall M.toInfoSignals)
      (fun player => liftPolicy M player (fallback player)) (cut + remaining) (payoff who)
      average type (average who)))).symm

/-- The constructed noisy depth-CFR solver supplies its native mean-absolute
conditional error. No Nash witness, supplied root-regret decomposition, minimum
type probability or learner-convergence hypothesis is taken from the caller. -/
theorem pbsInformationDepthCFR_native_mean_abs_le
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun history player => payoff player history))
    (cut remaining : Nat) (bound error loss : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ player history, |payoff player history| ≤ bound)
    (noise : PBSRootDepthNoise M (slice.mixture own).law)
    (noiseBound : ∀ n trunk player info, |noise n trunk player info| ≤ error)
    (t : Nat) [NeZero t] :
    own.expect (fun type => (cfrIterationLaw t).expect (fun n =>
      |pbsInformationDepthCFRConditionalDrawGap M slice own fallback payoff cut remaining
        bound loss noise t type n|)) ≤
      pbsRootDepthBudget M (slice.mixture own).law fallback cut remaining bound error loss t := by
  let average := pbsInformationDepthCFR M (slice.mixture own) fallback payoff cut remaining
    bound loss noise t
  calc
    _ = own.expect (fun type =>
        |slice.infoValue (fun player => liftPolicy M player (fallback player)) (cut + remaining)
            (payoff who) average type -
          slice.conditionalPayoff average (cut + remaining) (payoff who) (average who) type|) := by
      apply FinDist.expect_congr
      intro type supported
      exact pbsInformationDepthCFRConditionalDrawGap_mean_abs M slice own fallback payoff
        cut remaining bound loss noise t type supported
    _ ≤ _ := slice.mean_infoGap_abs_le_of_approxNash
      (fullSignals_perfectRecall M.toInfoSignals)
      (fun player => liftPolicy M player (fallback player)) (cut + remaining)
      (fun history player => payoff player history) own average _
      (pbsInformationDepthCFR_isNash M (slice.mixture own) fallback payoff zeroSum
        cut remaining bound error loss hb he hl bounded noise noiseBound t)

/-- A feasible requested tolerance selects the actual positive finite parent
count for the native conditional gap. Increasing this count does not remove
the fixed numerical or child-loss terms from the feasibility condition. -/
theorem pbsInformationDepthBudget_native_mean_abs_le
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun history player => payoff player history))
    (cut remaining : Nat) (bound error loss tolerance : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ player history, |payoff player history| ≤ bound)
    (noise : PBSRootDepthNoise M (slice.mixture own).law)
    (noiseBound : ∀ n trunk player info, |noise n trunk player info| ≤ error)
    (feasible : pbsRootDepthErrorFactor M (slice.mixture own).law fallback cut remaining *
      error + 2 * loss < tolerance) :
    let t := pbsRootDepthBudgetRounds M (slice.mixture own).law fallback cut remaining
      bound error loss tolerance
    own.expect (fun type => (cfrIterationLaw t).expect (fun n =>
      |pbsInformationDepthCFRConditionalDrawGap M slice own fallback payoff cut remaining
        bound loss noise t type n|)) ≤ tolerance := by
  exact (pbsInformationDepthCFR_native_mean_abs_le M slice own fallback payoff zeroSum
    cut remaining bound error loss hb he hl bounded noise noiseBound
    (pbsRootDepthBudgetRounds M (slice.mixture own).law fallback cut remaining
      bound error loss tolerance)).trans
    (pbsRootDepthBudgetRounds_error M (slice.mixture own).law fallback cut remaining
      bound error loss tolerance he feasible)

/-- Execute the actual depth-parent iterate after independent private seed and
root-type draws, retaining both tags. The unknown opponent receives neither tag
as a new argument; its existing information-local policy stays fixed. -/
def pbsInformationDepthCFRTaggedExecution
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M (slice.mixture own).law) (t : Nat) [NeZero t]
    (opponents : Profile (fullInformation M).behavioralSignature) (steps : Nat) :
    FinDist ((Fin t × T) × E.History) :=
  ((cfrIterationLaw t).product own).bind (fun pair =>
    ((slice.kernel pair.2).law.bind ((fullInformation M).runBehavioralFrom
      (Profile.update opponents who (pbsInformationDepthCFRIterate M (slice.mixture own)
        fallback payoff cut remaining bound loss noise pair.1.val who)) steps)).map
          (fun history => (pair, history)))

/-- Before event selection, the unchanged retained tags still have their
original product law. After selection they need not be independent. -/
theorem pbsInformationDepthCFRTaggedExecution_tags
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M (slice.mixture own).law) (t : Nat) [NeZero t]
    (opponents : Profile (fullInformation M).behavioralSignature) (steps : Nat) :
    (pbsInformationDepthCFRTaggedExecution M slice own fallback payoff cut remaining
      bound loss noise t opponents steps).map Prod.fst = (cfrIterationLaw t).product own := by
  simp only [pbsInformationDepthCFRTaggedExecution, FinDist.map_bind, FinDist.map_comp,
    Function.comp_def, FinDist.map_const, FinDist.bind_pure]

/-- Selecting an actual execution event derives the reciprocal-event bound
for the JOINT seed/type query. The gap still uses the original type kernels
and the fixed computed average opponent, not the execution opponent. -/
theorem pbsInformationDepthCFR_conditioned_native_mean_abs_le
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun history player => payoff player history))
    (cut remaining : Nat) (bound error loss : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ player history, |payoff player history| ≤ bound)
    (noise : PBSRootDepthNoise M (slice.mixture own).law)
    (noiseBound : ∀ n trunk player info, |noise n trunk player info| ≤ error)
    (t : Nat) [NeZero t]
    (opponents : Profile (fullInformation M).behavioralSignature) (steps : Nat)
    (event : Set ((Fin t × T) × E.History))
    (possible : ∃ point ∈ event, point ∈
      (pbsInformationDepthCFRTaggedExecution M slice own fallback payoff cut remaining
        bound loss noise t opponents steps).support) :
    (((pbsInformationDepthCFRTaggedExecution M slice own fallback payoff cut remaining
      bound loss noise t opponents steps).condOn event possible).map Prod.fst).expect
        (fun pair => |pbsInformationDepthCFRConditionalDrawGap M slice own fallback payoff
          cut remaining bound loss noise t pair.2 pair.1|) ≤
      pbsRootDepthBudget M (slice.mixture own).law fallback cut remaining bound error loss t /
        (pbsInformationDepthCFRTaggedExecution M slice own fallback payoff cut remaining
          bound loss noise t opponents steps).probOf event := by
  have selected := FinDist.tagged_condOn_expect_le_div ((cfrIterationLaw t).product own)
    (fun pair => (slice.kernel pair.2).law.bind ((fullInformation M).runBehavioralFrom
      (Profile.update opponents who (pbsInformationDepthCFRIterate M (slice.mixture own)
        fallback payoff cut remaining bound loss noise pair.1.val who)) steps)) event possible
    (fun pair => |pbsInformationDepthCFRConditionalDrawGap M slice own fallback payoff
      cut remaining bound loss noise t pair.2 pair.1|) (fun _ => abs_nonneg _)
  rw [FinDist.expect_product, FinDist.expect_comm] at selected
  exact selected.trans (div_le_div_of_nonneg_right
    (pbsInformationDepthCFR_native_mean_abs_le M slice own fallback payoff zeroSum
      cut remaining bound error loss hb he hl bounded noise noiseBound t)
    (FinDist.probOf_pos possible).le)

end GameTheory.ReBeL
