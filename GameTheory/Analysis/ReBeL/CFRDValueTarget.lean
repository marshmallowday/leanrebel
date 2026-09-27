/-
# Root information-value targets from the actual coupled CFR-D trace

Targets back up this round's predicted live-cut values and exact terminal
utilities, then retain an information-local root label. Uniform averaging is
over completed rounds of the same learner. It is not evaluation of a joint
average profile, and no last-iterate or network-training convergence is claimed.
-/

import GameTheory.Analysis.ReBeL.PBSRootDepthCFR

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

section Conditional

variable {Leaf Info Root : Type*}

/-- Conditioning on an information-local root label preserves a live vector's
error bound. The total absent-fiber convention is the original law; this lemma
does not turn that convention into a supported posterior. -/
theorem terminalExact_root_error (law : FinDist Leaf) (observe : Leaf → Info)
    (root : Info → Root) (type : Root) (live : Leaf → Bool)
    (value : Leaf → ℝ) (prediction : Info → ℝ) (error : ℝ) (nonneg : 0 ≤ error)
    (accurate : ∀ info,
      (info, true) ∈ (law.map (fun leaf => (observe leaf, live leaf))).support →
      |prediction info - conditionalOracleValue law
        (fun leaf => (observe leaf, live leaf)) value (info, true)| ≤ error) :
    |(law.condOnFibre (fun leaf => root (observe leaf)) type).expect
        (fun leaf => if live leaf = true then prediction (observe leaf) else value leaf) -
      (law.condOnFibre (fun leaf => root (observe leaf)) type).expect value| ≤ error := by
  classical
  let event := (fun leaf => root (observe leaf)) ⁻¹' {type}
  by_cases possible : ∃ leaf ∈ (fun leaf => root (observe leaf)) ⁻¹' {type},
      leaf ∈ law.support
  · have density : ∀ leaf, (law.condOn event possible).prob leaf =
        law.prob leaf * (if root (observe leaf) = type then (law.probOf event)⁻¹ else 0) := by
      intro leaf
      rw [FinDist.prob_condOn]
      by_cases same : root (observe leaf) = type
      · simp only [event, Set.mem_preimage, Set.mem_singleton_iff, same, if_true,
          div_eq_mul_inv]
      · simp only [event, Set.mem_preimage, Set.mem_singleton_iff, same, if_false, mul_zero]
    have conditioned : law.condOnFibre (fun leaf => root (observe leaf)) type =
        law.condOn event possible := by
      dsimp only [FinDist.condOnFibre]
      rw [dif_pos possible]
    simp only [conditioned]
    exact terminalExact_reweight_error law (law.condOn event possible) observe live
      (fun info => if root info = type then (law.probOf event)⁻¹ else 0)
      density value prediction error nonneg accurate
  · have conditioned : law.condOnFibre (fun leaf => root (observe leaf)) type = law := by
      dsimp only [FinDist.condOnFibre]
      rw [dif_neg possible]
    simp only [conditioned]
    exact terminalExact_reweight_error law law observe live (fun _ => 1)
      (fun _ => (mul_one _).symm) value prediction error nonneg accurate

/-- A vector is averaged componentwise, uniformly over exactly rounds 0 through
T-1. The positive-round index prevents a fictitious empty sampling law. -/
def cfrDValueTargetMean {Index : Type*} (target : Nat → Index → ℝ)
    (t : Nat) [NeZero t] (index : Index) : ℝ :=
  (cfrIterationLaw t).expect (fun n => target n.val index)

/-- Explicit finite sum form of the stored target vector. -/
theorem cfrDValueTargetMean_eq_sum {Index : Type*} (target : Nat → Index → ℝ)
    (t : Nat) [NeZero t] (index : Index) :
    cfrDValueTargetMean target t index =
      (∑ n ∈ Finset.range t, target n index) / t :=
  cfrIterationLaw_expect t (fun n => target n index)

/-- One completed round stores the initial learner's backed-up vector. -/
theorem cfrDValueTargetMean_one {Index : Type*} (target : Nat → Index → ℝ)
    (index : Index) : cfrDValueTargetMean target 1 index = target 0 index := by
  rw [cfrDValueTargetMean_eq_sum]
  simp

/-- Online uniform accumulation agrees with the finite stored-vector mean.
This is the main-paper update, not the supplement's linear-weight schedule. -/
theorem cfrDValueTargetMean_succ {Index : Type*} (target : Nat → Index → ℝ)
    (t : Nat) [NeZero t] (index : Index) :
    cfrDValueTargetMean target (t + 1) index =
      (t : ℝ) / (t + 1) * cfrDValueTargetMean target t index +
        1 / (t + 1) * target t index := by
  rw [cfrDValueTargetMean_eq_sum, cfrDValueTargetMean_eq_sum, Finset.sum_range_succ]
  have nonzero : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  have nextNonzero : (t : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp [nonzero, nextNonzero]

/-- Per-round numerical error survives averaging without a factor of T.
This compares two value traces, not either trace with a Nash value. -/
theorem cfrDValueTargetMean_error {Index : Type*}
    (target exactValue : Nat → Index → ℝ) (t : Nat) [NeZero t]
    (index : Index) (error : ℝ)
    (accurate : ∀ n < t, |target n index - exactValue n index| ≤ error) :
    |cfrDValueTargetMean target t index - cfrDValueTargetMean exactValue t index| ≤ error := by
  unfold cfrDValueTargetMean
  rw [← FinDist.expect_sub]
  exact FinDist.abs_expect_le_of_abs_bound _ _ (fun n _ => accurate n.val n.isLt)

end Conditional

section Driver

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι]
variable [∀ who info, Fintype (M.Choice who info)]
variable [∀ who, DecidableEq (M.InfoState who)]

/-- The current predicted backup is retained as a vector of root types. A
root readout must be information-local; it cannot inspect hidden histories.
Absent labels retain the explicit total conditional convention, not a claim
that they were sampled. Use the companion support set for training selection. -/
def cfrDDepthValueTarget (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (payoff : ι → E.History → ℝ)
    (cut remaining : Nat) (oracle : CFRDValueOracle M) (round : Nat)
    (who : ι) {Root : Type*} (root : M.InfoState who → Root) (type : Root) : ℝ :=
  let profile := cfrDDepthPlay M clock fallback payoff cut remaining oracle round
  conditionalOracleValue (M.runBehavioral profile cut)
    (fun history => root (M.infoOf who history.trace))
    (cfrDCutLeafValue M who (payoff who) remaining
      ((cfrDDepthQuery M clock fallback payoff cut remaining oracle round).prediction who)) type

/-- Supported root labels of this very round, kept separately from total
off-support vector entries. No observation is fabricated from zero mass. -/
def cfrDDepthValueTargetSupport (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (payoff : ι → E.History → ℝ)
    (cut remaining : Nat) (oracle : CFRDValueOracle M) (round : Nat)
    (who : ι) {Root : Type*} (root : M.InfoState who → Root) : Set Root :=
  ((M.runBehavioral (cfrDDepthPlay M clock fallback payoff cut remaining oracle round) cut).map
    (fun history => root (M.infoOf who history.trace))).support

/-- The proof-side comparator continues the SAME round's profile. The
computed target above never performs this full remaining-horizon rollout. -/
def cfrDDepthExactTarget (clock : ObservationClock M)
    (fallback : Profile M.strategicSignature) (payoff : ι → E.History → ℝ)
    (cut remaining : Nat) (oracle : CFRDValueOracle M) (round : Nat)
    (who : ι) {Root : Type*} (root : M.InfoState who → Root) (type : Root) : ℝ :=
  let profile := cfrDDepthPlay M clock fallback payoff cut remaining oracle round
  conditionalOracleValue (M.runBehavioral profile cut)
    (fun history => root (M.infoOf who history.trace))
    (fun history => (M.runBehavioralFrom profile remaining history).expect (payoff who)) type

/-- Reweight the actual live-vector contract to each root information label.
Hidden-state pointwise accuracy and a minimum root mass are unnecessary. -/
theorem cfrDDepthValueTarget_error (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (payoff : ι → E.History → ℝ)
    (cut remaining : Nat) (oracle : CFRDValueOracle M) (round : Nat)
    (who : ι) {Root : Type*} (root : M.InfoState who → Root) (type : Root)
    (error : ℝ) (nonneg : 0 ≤ error)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error) :
    |cfrDDepthValueTarget M clock fallback payoff cut remaining oracle round who root type -
      cfrDDepthExactTarget M clock fallback payoff cut remaining oracle round who root type| ≤
        error := by
  let profile := cfrDDepthPlay M clock fallback payoff cut remaining oracle round
  let prediction := (cfrDDepthQuery M clock fallback payoff cut remaining oracle round).prediction
  have bound := terminalExact_root_error (M.runBehavioral profile cut)
    (fun history => M.infoOf who history.trace) root type (cfrDCutLive remaining)
    (fun history => (M.runBehavioralFrom profile remaining history).expect (payoff who))
    (prediction who) error nonneg
    (cfrDCutAccurate_factual M hrecall profile fallback who (payoff who) cut remaining
      (prediction who) error (accurate round who))
  have terminalExact :
      cfrDCutLeafValue M who (payoff who) remaining (prediction who) =
        fun history => if cfrDCutLive remaining history = true then
          prediction who (M.infoOf who history.trace) else
          (M.runBehavioralFrom profile remaining history).expect (payoff who) := by
    funext history
    dsimp only [cfrDCutLeafValue]
    by_cases live : cfrDCutLive remaining history = true
    · simp only [if_pos live]
    · simp only [if_neg live, cfrDCutValue_stopped M profile _ _ _ live]
  dsimp only [cfrDDepthValueTarget, cfrDDepthExactTarget, conditionalOracleValue]
  rw [terminalExact]
  exact bound

/-- The stored average vector inherits the oracle's numerical accuracy.
The comparator is the mean of same-round conditional continuations, not the
last iterate and not evaluation of independently averaged player policies. -/
theorem cfrDDepthValueTargetMean_error (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (payoff : ι → E.History → ℝ)
    (cut remaining : Nat) (oracle : CFRDValueOracle M) (t : Nat) [NeZero t]
    (who : ι) {Root : Type*} (root : M.InfoState who → Root) (type : Root)
    (error : ℝ) (nonneg : 0 ≤ error)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error) :
    |cfrDValueTargetMean
        (fun n => cfrDDepthValueTarget M clock fallback payoff cut remaining oracle n who root)
        t type -
      cfrDValueTargetMean
        (fun n => cfrDDepthExactTarget M clock fallback payoff cut remaining oracle n who root)
        t type| ≤ error := by
  apply cfrDValueTargetMean_error
  intro n _
  exact cfrDDepthValueTarget_error M clock hrecall fallback payoff cut remaining oracle
    n who root type error nonneg accurate

end Driver

section Rooted

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable (roots : FinDist E.History)

/-- Read the original root AOH from the administrative chance observation.
Later private observations cannot change this retained prefix. -/
def pbsRootValueReadout (who : Fin 2) (info : (pbsRootFullInformation M roots).InfoState who) :
    Option ((fullInformation M).InfoState who) :=
  reduceAOH (pbsRootInformation (fullInformation M) roots).toInfoSignals who (info.prefixAt 1)

/-- The original player's complete root information is retained, not averaged
into a scalar and not replaced by a hidden-state label. -/
theorem pbsRootValueReadout_snapshot (who : Fin 2) (info : (fullInformation M).InfoState who) :
    pbsRootValueReadout M roots who info.rootedSnapshot = some info := by
  dsimp only [pbsRootValueReadout]
  rw [AOH.prefixAt_eq_of_length_le _ _ (Nat.le_refl 1)]
  rfl

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- Supply finite rooted histories from the canonical protocol construction. -/
local instance valueTargetRootHistory : Fintype (pbsRootProtocol roots).History :=
  pbsRootHistoryFintype roots

/-- Equality is classical only in the real-valued reference solver. -/
local instance valueTargetRootInfo (who : Fin 2) :
    DecidableEq ((pbsRootFullInformation M roots).InfoState who) := Classical.decEq _

/-- Rooted local menus inherit finite action carriers. -/
local instance valueTargetRootChoice (who : Fin 2)
    (info : (pbsRootFullInformation M roots).InfoState who) :
    Fintype ((pbsRootFullInformation M roots).Choice who info) := by
  classical
  infer_instance

/-- Root information-value labels generated by the actual noisy finite-child
parent. Cut includes the one administrative chance step; remaining does not. -/
def pbsRootDepthValueTarget (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M roots) (round : Nat) (who : Fin 2)
    (type : (fullInformation M).InfoState who) : ℝ :=
  cfrDDepthValueTarget (pbsRootFullInformation M roots)
    (fullObservationClock (pbsRootInformation (fullInformation M) roots))
    (pbsRootFallback M roots fallback) (pbsRootPayoff roots payoff) (cut + 1) remaining
    (pbsRootDepthOracle M roots fallback payoff cut remaining bound loss noise) round who
    (pbsRootValueReadout M roots who) (some type)

/-- Accuracy for the actual constructed parent is supplied by its explicit
noise bound. No per-round equilibrium or accuracy certificate is an input. -/
theorem pbsRootDepthValueTarget_error (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M roots) (error : ℝ) (nonneg : 0 ≤ error)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (round : Nat) (who : Fin 2) (type : (fullInformation M).InfoState who) :
    |pbsRootDepthValueTarget M roots fallback payoff cut remaining bound loss noise
        round who type -
      cfrDDepthExactTarget (pbsRootFullInformation M roots)
        (fullObservationClock (pbsRootInformation (fullInformation M) roots))
        (pbsRootFallback M roots fallback) (pbsRootPayoff roots payoff) (cut + 1) remaining
        (pbsRootDepthOracle M roots fallback payoff cut remaining bound loss noise) round who
        (pbsRootValueReadout M roots who) (some type)| ≤ error := by
  apply cfrDDepthValueTarget_error
  · exact fullSignals_perfectRecall (pbsRootInformation (fullInformation M) roots).toInfoSignals
  · exact nonneg
  · rw [pbsRootDepthOracle_eq]
    exact cfrDConstructedInformationOracle_accurate
      (pbsRootInformation (fullInformation M) roots) (pbsRootDepthFallback M roots fallback)
      (pbsRootPayoff roots payoff) (cut + 1) remaining bound loss noise error noiseBound

/-- The complete training vector mean of the constructed noisy parent. -/
def pbsRootDepthValueTargetMean (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M roots) (t : Nat) [NeZero t] (who : Fin 2)
    (type : (fullInformation M).InfoState who) : ℝ :=
  cfrDValueTargetMean
    (fun n => pbsRootDepthValueTarget M roots fallback payoff cut remaining bound loss noise n who)
    t type

/-- The actual parent supplies every round's estimate before averaging. The
finite iteration count and the nonzero noise remain explicit; this proves
numerical propagation, not convergence of the target to a Nash value. -/
theorem pbsRootDepthValueTargetMean_error (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (bound loss : ℝ)
    (noise : PBSRootDepthNoise M roots) (error : ℝ) (nonneg : 0 ≤ error)
    (noiseBound : ∀ n trunk who info, |noise n trunk who info| ≤ error)
    (t : Nat) [NeZero t] (who : Fin 2) (type : (fullInformation M).InfoState who) :
    |pbsRootDepthValueTargetMean M roots fallback payoff cut remaining bound loss noise
        t who type -
      cfrDValueTargetMean (fun n tag =>
        cfrDDepthExactTarget (pbsRootFullInformation M roots)
          (fullObservationClock (pbsRootInformation (fullInformation M) roots))
          (pbsRootFallback M roots fallback) (pbsRootPayoff roots payoff) (cut + 1) remaining
          (pbsRootDepthOracle M roots fallback payoff cut remaining bound loss noise) n who
          (pbsRootValueReadout M roots who) (some tag)) t type| ≤ error := by
  apply cfrDValueTargetMean_error
  intro n _
  exact pbsRootDepthValueTarget_error M roots fallback payoff cut remaining bound loss noise
    error nonneg noiseBound n who type

end Rooted

end GameTheory.ReBeL
