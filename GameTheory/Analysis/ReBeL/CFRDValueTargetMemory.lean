/-
# Retained root labels and full-horizon meaning of CFR-D targets

A label preserved by the execution kernel may be conditioned before or after
execution. The root readout is proved to have this property for the canonical
runner, including early termination. This connects backed-up vectors to actual
full-horizon conditional values, without a convergence assumption.
-/

import GameTheory.Analysis.ReBeL.CFRDValueTarget
import GameTheory.Math.Probability.FinDistConditioning
import GameTheory.Math.Probability.FinDistRetainedLabel

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

section Execution

universe uι us ua
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

/-- Every supported canonical randomized run gives legal bounded reachability.
This is a support theorem about the existing runner, not a new execution law. -/
theorem valueTarget_run_reaches (chooser : E.RandomizedChooser) (fuel : Nat)
    (first later : E.History)
    (sampled : later ∈ (E.runRandomizedFor chooser fuel first).support) :
    E.ReachesWithin fuel first later := by
  induction fuel generalizing first with
  | zero =>
      rw [runRandomizedFor_zero, FinDist.mem_support_pure] at sampled
      subst later
      exact .refl _ _
  | succ fuel ih =>
      by_cases stopped : E.terminal first.state
      · rw [runRandomizedFor_of_terminal _ _ stopped, FinDist.mem_support_pure] at sampled
        subst later
        exact .refl _ _
      · rw [runRandomizedFor_succ_of_not_terminal chooser fuel stopped,
          FinDist.support_bind] at sampled
        obtain ⟨draw, _, sampled⟩ := Set.mem_iUnion₂.mp sampled
        rw [FinDist.support_bindOnSupport] at sampled
        obtain ⟨next, realized, sampled⟩ := Set.mem_iUnion₂.mp sampled
        exact .step draw.val draw.property realized (ih _ sampled)

/-- Positive fuel from a nonterminal history performs at least one step,
even when the first successor is already terminal. -/
theorem valueTarget_run_advances (chooser : E.RandomizedChooser) (fuel : Nat)
    (first later : E.History) (active : ¬ E.terminal first.state)
    (sampled : later ∈ (E.runRandomizedFor chooser (fuel + 1) first).support) :
    first.trace.length + 1 ≤ later.trace.length := by
  rw [runRandomizedFor_succ_of_not_terminal chooser fuel active, FinDist.support_bind] at sampled
  obtain ⟨draw, _, sampled⟩ := Set.mem_iUnion₂.mp sampled
  rw [FinDist.support_bindOnSupport] at sampled
  obtain ⟨next, realized, sampled⟩ := Set.mem_iUnion₂.mp sampled
  exact (valueTarget_run_reaches chooser fuel (first.extend draw.property realized)
    later sampled).trace_length_le

end Execution

section Rooted

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable (roots : FinDist E.History)

/-- Later execution retains the original administrative root observation.
The premise excludes the pre-draw state, where no root has been observed yet. -/
theorem pbsRootValueReadout_persistent
    (profile : Profile (pbsRootFullInformation M roots).behavioralSignature) (who : Fin 2)
    (first later : (pbsRootProtocol roots).History) (fuel : Nat)
    (afterDraw : 1 ≤ first.trace.length)
    (sampled : later ∈ ((pbsRootFullInformation M roots).runBehavioralFrom
      profile fuel first).support) :
    pbsRootValueReadout M roots who
        ((pbsRootFullInformation M roots).infoOf who later.trace) =
      pbsRootValueReadout M roots who
        ((pbsRootFullInformation M roots).infoOf who first.trace) := by
  exact congrArg
    (reduceAOH (pbsRootInformation (fullInformation M) roots).toInfoSignals who)
    (prefixAt_infoOf_reaches (pbsRootInformation (fullInformation M) roots) 1 who
      (valueTarget_run_reaches _ fuel first later sampled) afterDraw)

/-- Splitting at the depth limit and then continuing has exactly the same
root-conditional value as the complete run. Terminal roots remain in the law. -/
theorem pbsRootValueReadout_tower
    (profile : Profile (pbsRootFullInformation M roots).behavioralSignature)
    (cut remaining : Nat) (who : Fin 2)
    (type : Option ((fullInformation M).InfoState who))
    (value : (pbsRootProtocol roots).History → ℝ) :
    conditionalOracleValue
        ((pbsRootFullInformation M roots).runBehavioral profile (cut + 1 + remaining))
        (fun h => pbsRootValueReadout M roots who
          ((pbsRootFullInformation M roots).infoOf who h.trace)) value type =
      conditionalOracleValue
        ((pbsRootFullInformation M roots).runBehavioral profile (cut + 1))
        (fun h => pbsRootValueReadout M roots who
          ((pbsRootFullInformation M roots).infoOf who h.trace))
        (fun h => ((pbsRootFullInformation M roots).runBehavioralFrom
          profile remaining h).expect value) type := by
  rw [runBehavioral, runBehavioralFrom_add]
  apply FinDist.condOnFibre_expect_bind
  intro first sampled later reached
  apply pbsRootValueReadout_persistent M roots profile who first later remaining _ reached
  exact valueTarget_run_advances _ cut (pbsRootProtocol roots).initHistory first
    not_false sampled

/-- The reconstructed local sequence always contains its initial root draw. -/
theorem valueTarget_rootedAt_positive {Action Private Public : Type*}
    (cut : Nat) (info : AOH Action Private Public) :
    1 ≤ (info.rootedAt cut).length := by
  cases info with
  | initial => exact Nat.le_refl 1
  | step prior action privateObs publicObs =>
      dsimp only [AOH.rootedAt]
      split
      · exact Nat.le_refl 1
      · exact Nat.succ_le_succ (Nat.zero_le _)

/-- Reading the first rooted observation reconstructs the original local
prefix at the public cut, even after later private information is revealed. -/
theorem valueTarget_rootedAt_prefix {Action Private Public : Type*}
    (cut : Nat) (info : AOH Action Private Public) :
    (info.rootedAt cut).prefixAt 1 = (info.prefixAt cut).rootedSnapshot := by
  induction info with
  | initial => rfl
  | step prior action privateObs publicObs ih =>
      by_cases before : prior.length < cut
      · have atCut : (AOH.step prior action privateObs publicObs).length ≤ cut := by
          simp only [AOH.length]
          omega
        rw [AOH.rootedAt_eq_snapshot_of_length_le cut _ atCut,
          AOH.prefixAt_eq_of_length_le 1
            (AOH.rootedSnapshot (AOH.step prior action privateObs publicObs)) (Nat.le_refl 1),
          AOH.prefixAt_eq_of_length_le cut _ atCut]
      · rw [AOH.rootedAt_step cut prior (Nat.le_of_not_gt before),
          AOH.prefixAt_step_of_le 1 _ _ _ _ (valueTarget_rootedAt_positive cut prior),
          AOH.prefixAt_step_of_le cut prior _ _ _ (Nat.le_of_not_gt before), ih]

/-- At every legal trace the readout is the original player's remembered
prefix. This also specifies the unobserved administrative state as none. -/
theorem pbsRootValueReadout_trace (rootCut : Nat)
    (rootDepth : ∀ h ∈ roots.support, h.trace.length = rootCut) (who : Fin 2)
    (history : (pbsRootProtocol roots).History) :
    pbsRootValueReadout M roots who
        ((pbsRootFullInformation M roots).infoOf who history.trace) =
      history.state.map (fun h => ((fullInformation M).infoOf who h.trace).prefixAt rootCut) := by
  rcases history with ⟨state, trace⟩
  have localHistory := pbsRootLocalHistory_trace M roots rootCut rootDepth who trace
  cases state with
  | none =>
      exact congrArg (pbsRootValueReadout M roots who) localHistory
  | some original =>
      calc
        _ = pbsRootValueReadout M roots who
            (((fullInformation M).infoOf who original.trace).rootedAt rootCut) :=
          congrArg (pbsRootValueReadout M roots who) localHistory.2
        _ = _ := by
          dsimp only [pbsRootValueReadout]
          rw [valueTarget_rootedAt_prefix]
          rfl

/-- The full law of root labels is the input PBS own-type law, independent
of the searched profile, elapsed fuel and subsequent private observations. -/
theorem pbsRootValueReadout_law (rootCut : Nat)
    (rootDepth : ∀ h ∈ roots.support, h.trace.length = rootCut)
    (profile : Profile (pbsRootFullInformation M roots).behavioralSignature)
    (fuel : Nat) (who : Fin 2) :
    (((pbsRootFullInformation M roots).runBehavioral profile (fuel + 1)).map
      (fun h => pbsRootValueReadout M roots who
        ((pbsRootFullInformation M roots).infoOf who h.trace))) =
      roots.map (fun h => some ((fullInformation M).infoOf who h.trace)) := by
  let label : E.History → (fullInformation M).InfoState who :=
    fun h => ((fullInformation M).infoOf who h.trace).prefixAt rootCut
  have recode :
      (((pbsRootFullInformation M roots).runBehavioral profile (fuel + 1)).map
        (fun h => pbsRootValueReadout M roots who
          ((pbsRootFullInformation M roots).infoOf who h.trace))) =
      ((((pbsRootFullInformation M roots).runBehavioral profile (fuel + 1)).map
        History.state).map (fun state => state.map label)) := by
    rw [FinDist.map_comp]
    exact FinDist.map_congr_of_eq_on_support (fun h _ =>
      pbsRootValueReadout_trace M roots rootCut rootDepth who h)
  rw [recode, pbsRootDecodeProfile_law M roots rootCut rootDepth, FinDist.map_comp]
  apply FinDist.map_bind_of_retained
  intro first hf later hl
  have memory := prefixAt_infoOf_reaches M rootCut who
    (valueTarget_run_reaches _ fuel first later hl)
    (by rw [rootDepth first hf])
  have atRoot := AOH.prefixAt_eq_of_length_le rootCut
    ((fullInformation M).infoOf who first.trace)
    (by rw [length_infoOf, rootDepth first hf])
  exact congrArg some (memory.trans atRoot)

/-- Root conditioning commutes all the way through decoding to the original
game. The conditional root law retains correlations between private types. -/
theorem pbsRootValueReadout_original (rootCut : Nat)
    (rootDepth : ∀ h ∈ roots.support, h.trace.length = rootCut)
    (profile : Profile (pbsRootFullInformation M roots).behavioralSignature)
    (fuel : Nat) (who : Fin 2) (type : (fullInformation M).InfoState who)
    (payoff : E.History → ℝ) :
    conditionalOracleValue
        ((pbsRootFullInformation M roots).runBehavioral profile (fuel + 1))
        (fun h => pbsRootValueReadout M roots who
          ((pbsRootFullInformation M roots).infoOf who h.trace))
        (fun h => h.state.elim 0 payoff) (some type) =
      conditionalOracleValue roots (fun h => (fullInformation M).infoOf who h.trace)
        (fun h => ((fullInformation M).runBehavioralFrom
          (pbsRootDecodeProfile M roots rootCut profile) fuel h).expect payoff) type := by
  let label : E.History → (fullInformation M).InfoState who :=
    fun h => ((fullInformation M).infoOf who h.trace).prefixAt rootCut
  let rootLabel : Option E.History → Option ((fullInformation M).InfoState who) :=
    fun state => state.map label
  have readout :
      (fun h : (pbsRootProtocol roots).History => pbsRootValueReadout M roots who
        ((pbsRootFullInformation M roots).infoOf who h.trace)) =
      (fun h => rootLabel h.state) := by
    funext h
    exact pbsRootValueReadout_trace M roots rootCut rootDepth who h
  have mapped := FinDist.condOnFibre_expect_map
    ((pbsRootFullInformation M roots).runBehavioral profile (fuel + 1))
    (fun h : (pbsRootProtocol roots).History => h.state) rootLabel (some type)
    (fun state : Option E.History => state.elim 0 payoff)
  dsimp only [conditionalOracleValue]
  rw [readout, ← mapped, pbsRootDecodeProfile_law M roots rootCut rootDepth]
  rw [FinDist.condOnFibre_expect_map _ some rootLabel]
  have recode :
      conditionalOracleValue
        (roots.bind ((fullInformation M).runBehavioralFrom
          (pbsRootDecodeProfile M roots rootCut profile) fuel))
        (fun h => rootLabel (some h)) (fun h => (some h).elim 0 payoff) (some type) =
      conditionalOracleValue
        (roots.bind ((fullInformation M).runBehavioralFrom
          (pbsRootDecodeProfile M roots rootCut profile) fuel))
        label payoff type := by
    dsimp only [conditionalOracleValue]
    rw [FinDist.condOnFibre_eq_of_support_iff _ _ label (some type) type
      (by
        intro h _
        constructor
        · exact Option.some.inj
        · exact congrArg some)]
    rfl
  dsimp only [conditionalOracleValue] at recode
  rw [recode]
  apply FinDist.condOnFibre_expect_bind
  intro first hf later hl
  have memory := prefixAt_infoOf_reaches M rootCut who
    (valueTarget_run_reaches _ fuel first later hl)
    (by rw [rootDepth first hf])
  exact memory.trans (AOH.prefixAt_eq_of_length_le rootCut
    ((fullInformation M).infoOf who first.trace)
    (by rw [length_infoOf, rootDepth first hf]))

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- Same finite rooted carriers as the actual parent solver. -/
local instance targetMemoryHistory : Fintype (pbsRootProtocol roots).History :=
  pbsRootHistoryFintype roots

/-- Classical equality is confined to the reference solver. -/
local instance targetMemoryInfo (who : Fin 2) :
    DecidableEq ((pbsRootFullInformation M roots).InfoState who) := Classical.decEq _

/-- Finite legal options are inherited from the action carrier. -/
local instance targetMemoryChoice (who : Fin 2)
    (info : (pbsRootFullInformation M roots).InfoState who) :
    Fintype ((pbsRootFullInformation M roots).Choice who info) := by
  classical
  infer_instance

/-- Proof-side full-horizon value of the actual current round, conditioned
on its retained root observation. The training algorithm still uses backups. -/
def pbsRootDepthFullTarget (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M roots) (round : Nat) (who : Fin 2)
    (type : (fullInformation M).InfoState who) : ℝ :=
  conditionalOracleValue
    ((pbsRootFullInformation M roots).runBehavioral
      (pbsRootDepthIterate M roots fallback payoff cut remaining bound loss noise round)
      (cut + 1 + remaining))
    (fun h => pbsRootValueReadout M roots who
      ((pbsRootFullInformation M roots).infoOf who h.trace))
    (pbsRootPayoff roots payoff who) (some type)

/-- The old cut-conditioned comparator is exactly the actual complete
same-round value. No lower bound on a root's probability is introduced. -/
theorem pbsRootDepthFullTarget_eq (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M roots) (round : Nat) (who : Fin 2)
    (type : (fullInformation M).InfoState who) :
    pbsRootDepthFullTarget M roots fallback payoff cut remaining bound loss noise round who type =
      cfrDDepthExactTarget (pbsRootFullInformation M roots)
        (fullObservationClock (pbsRootInformation (fullInformation M) roots))
        (pbsRootFallback M roots fallback) (pbsRootPayoff roots payoff) (cut + 1) remaining
        (pbsRootDepthOracle M roots fallback payoff cut remaining bound loss noise) round who
        (pbsRootValueReadout M roots who) (some type) :=
  pbsRootValueReadout_tower M roots
    (pbsRootDepthIterate M roots fallback payoff cut remaining bound loss noise round)
    cut remaining who (some type) (pbsRootPayoff roots payoff who)

/-- A public belief supplies the common-depth condition. The full target is
the continuation value from the original PBS conditioned on one's root AOH. -/
theorem pbsRootDepthFullTarget_original {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : PBSRootDepthNoise M belief.law)
    (round : Nat) (who : Fin 2) (type : (fullInformation M).InfoState who) :
    pbsRootDepthFullTarget M belief.law fallback payoff cut remaining bound loss
        noise round who type =
      conditionalOracleValue belief.law (fun h => (fullInformation M).infoOf who h.trace)
        (fun h => ((fullInformation M).runBehavioralFrom
          (pbsRootDecodeProfile M belief.law (observations.length - 1)
            (pbsRootDepthIterate M belief.law fallback payoff
              cut remaining bound loss noise round))
          (cut + remaining) h).expect (payoff who)) type := by
  have payoffRead : pbsRootPayoff belief.law payoff who =
      (fun h : (pbsRootProtocol belief.law).History => h.state.elim 0 (payoff who)) := by
    funext h
    dsimp only [pbsRootPayoff]
    cases h.state <;> rfl
  dsimp only [pbsRootDepthFullTarget]
  rw [show cut + 1 + remaining = (cut + remaining) + 1 by omega, payoffRead]
  exact pbsRootValueReadout_original M belief.law (observations.length - 1)
    (pbsRoot_publicBelief_depth M belief)
    (pbsRootDepthIterate M belief.law fallback payoff cut remaining bound loss noise round)
    (cut + remaining) who type (payoff who)

/-- Root target support is exactly the original PBS type support for every
actual noisy round. Neither zero-reach actions nor later stopping delete roots. -/
theorem pbsRootDepthValueTarget_support (rootCut : Nat)
    (rootDepth : ∀ h ∈ roots.support, h.trace.length = rootCut)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : PBSRootDepthNoise M roots)
    (round : Nat) (who : Fin 2) :
    cfrDDepthValueTargetSupport (pbsRootFullInformation M roots)
        (fullObservationClock (pbsRootInformation (fullInformation M) roots))
        (pbsRootFallback M roots fallback) (pbsRootPayoff roots payoff) (cut + 1) remaining
        (pbsRootDepthOracle M roots fallback payoff cut remaining bound loss noise) round who
        (pbsRootValueReadout M roots who) =
      (roots.map (fun h => some ((fullInformation M).infoOf who h.trace))).support :=
  congrArg FinDist.support
    (pbsRootValueReadout_law M roots rootCut rootDepth
      (pbsRootDepthIterate M roots fallback payoff cut remaining bound loss noise round) cut who)

/-- Numerical accuracy now compares the computed average with genuine
full-horizon per-root values of these same noisy learning rounds. -/
theorem pbsRootDepthValueTargetMean_full_error (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M roots) (error : ℝ) (nonneg : 0 ≤ error)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (t : Nat) [NeZero t] (who : Fin 2) (type : (fullInformation M).InfoState who) :
    |pbsRootDepthValueTargetMean M roots fallback payoff cut remaining bound loss noise
        t who type -
      cfrDValueTargetMean
        (fun n => pbsRootDepthFullTarget M roots fallback payoff
          cut remaining bound loss noise n who)
        t type| ≤ error := by
  apply cfrDValueTargetMean_error
  intro n _
  rw [pbsRootDepthFullTarget_eq]
  exact pbsRootDepthValueTarget_error M roots fallback payoff cut remaining bound loss noise
    error nonneg noiseBound n who type

/-- The stored mean is compared directly with original-game continuations,
using the original correlated PBS conditioned on each player's own root AOH. -/
theorem pbsRootDepthValueTargetMean_original_error {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : PBSRootDepthNoise M belief.law)
    (error : ℝ) (nonneg : 0 ≤ error)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (t : Nat) [NeZero t] (who : Fin 2) (type : (fullInformation M).InfoState who) :
    |pbsRootDepthValueTargetMean M belief.law fallback payoff cut remaining bound loss
        noise t who type -
      cfrDValueTargetMean (fun n tag =>
        conditionalOracleValue belief.law (fun h => (fullInformation M).infoOf who h.trace)
          (fun h => ((fullInformation M).runBehavioralFrom
            (pbsRootDecodeProfile M belief.law (observations.length - 1)
              (pbsRootDepthIterate M belief.law fallback payoff
                cut remaining bound loss noise n))
            (cut + remaining) h).expect (payoff who)) tag) t type| ≤ error := by
  have result := pbsRootDepthValueTargetMean_full_error M belief.law fallback payoff
    cut remaining bound loss noise error nonneg noiseBound t who type
  have same :
      (fun n => pbsRootDepthFullTarget M belief.law fallback payoff
        cut remaining bound loss noise n who) =
      (fun n tag =>
        conditionalOracleValue belief.law (fun h => (fullInformation M).infoOf who h.trace)
          (fun h => ((fullInformation M).runBehavioralFrom
            (pbsRootDecodeProfile M belief.law (observations.length - 1)
              (pbsRootDepthIterate M belief.law fallback payoff
                cut remaining bound loss noise n))
            (cut + remaining) h).expect (payoff who)) tag) := by
    funext n tag
    exact pbsRootDepthFullTarget_original M belief fallback payoff
      cut remaining bound loss noise n who tag
  rw [same] at result
  exact result

end Rooted

end GameTheory.ReBeL
