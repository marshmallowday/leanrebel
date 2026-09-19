/-
# A genuinely live cut in the two-stage hidden-type game

Only the first strategic round is searched. The second round remains live
and is evaluated by a continuation oracle. Independent fair continuation
play is optimal at every legal live history, including off-path histories.
-/

import GameTheory.Analysis.ReBeL.Examples.CFRDExecution
import GameTheory.Analysis.ReBeL.Examples.CFRDSeedControl

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Finite canonical histories for the genuine live-cut control. -/
local instance cfrDLiveHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior
/-- Decidable information-state equality for this proof-only live-cut control. -/
local instance cfrDLiveInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) :=
  Classical.decEq _
/-- Finite legal menus at every information state of the live-cut control. -/
local instance cfrDLiveChoiceFintype (who : Player) (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Each player's continuation action is an independent fair legal bit. -/
def liveFairContinuation : Profile (model fullPrior).behavioralSignature :=
  fun who info => carriedBitLaw.bind fun bit => carriedBitProfile bit who info

/-- The live menu is exactly a Boolean choice, with no hidden-history action. -/
def liveSecondEquiv (x y a b : Bool) (who : Player) :
    Bool ≃ (model fullPrior).Choice who
      ((model fullPrior).infoOf who (decode (.second x y a b)).trace) :=
  rowChoiceEquiv who (.second x y a b)

/-- Reindex only the two active canonical choices, not hidden information. -/
def liveSecondLaw (strategy : Profile (model fullPrior).behavioralSignature)
    (x y a b : Bool) (who : Player) : FinDist Bool :=
  (strategy who ((model fullPrior).infoOf who (decode (.second x y a b)).trace)).map
    (liveSecondEquiv x y a b who).symm

/-- The actual one-step canonical history law retains all earlier hidden
and public events and both final simultaneous actions. -/
theorem liveSecond_run (strategy : Profile (model fullPrior).behavioralSignature)
    (x y a b : Bool) :
    (model fullPrior).runBehavioralFrom strategy 1 (decode (.second x y a b)) =
      (FinDist.pi (liveSecondLaw strategy x y a b)).map
        (fun draws => decode (.finished x y a b (draws 0) (draws 1))) := by
  have hterm : ¬ (protocol fullPrior).terminal (decode (.second x y a b)).state :=
    fun impossible => impossible
  rw [run_one_reindexed strategy (.second x y a b) hterm]
  unfold liveSecondLaw
  rw [FinDist.pi_map, FinDist.map_comp, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro draw _
  exact rowDrawLaw_second x y a b hterm ((rowJointEquiv (.second x y a b)).symm draw)

/-- Independent fair play survives the menu bijection exactly. -/
theorem liveFairSecondLaw (x y a b : Bool) (who : Player) :
    liveSecondLaw liveFairContinuation x y a b who = carriedBitLaw := by
  unfold liveSecondLaw liveFairContinuation
  rw [FinDist.map_bind]
  have same (bit : Bool) :
      ((carriedBitProfile bit who
          ((model fullPrior).infoOf who (decode (.second x y a b)).trace)).map
          (liveSecondEquiv x y a b who).symm) = FinDist.pure bit := by
    rw [show carriedBitProfile bit who
        ((model fullPrior).infoOf who (decode (.second x y a b)).trace) =
        FinDist.pure (liveSecondEquiv x y a b who bit) from rfl,
      FinDist.map_pure, Equiv.symm_apply_apply]
  simp_rw [same]
  exact FinDist.bind_pure _

/-- The second round's expectation is exactly its two independent local draws. -/
theorem liveSecond_value (strategy : Profile (model fullPrior).behavioralSignature)
    (x y a b : Bool) (who : Player) :
    ((model fullPrior).runBehavioralFrom strategy 1 (decode (.second x y a b))).expect
        (cfrPayoff who) =
      (liveSecondLaw strategy x y a b 0).expect (fun c =>
        (liveSecondLaw strategy x y a b 1).expect (fun d =>
          signed who (winValue (a == b) + winValue ((c == y) == d)))) := by
  rw [liveSecond_run, FinDist.expect_map, ← FinDist.piFin_eq_pi]
  simp only [FinDist.piFin, FinDist.expect_map, FinDist.expect_product, FinDist.expect_pure]
  apply FinDist.expect_congr
  intro c _
  apply FinDist.expect_congr
  intro d _
  have h := payoff_correct (.finished x y a b c d) who
  unfold cfrPayoff
  refine h.symm.trans ?_
  rcases (by decide : ∀ player : Fin 2, player = 0 ∨ player = 1) who with rfl | rfl <;>
    cases a <;> cases b <;> cases c <;> cases y <;> cases d <;>
      norm_num [GameTheory.ReBeL.Rational.HiddenTypes.payoff,
        GameTheory.ReBeL.Rational.HiddenTypes.winValue, signed, winValue]

private theorem live_uniform_right (y a b c : Bool) :
    carriedBitLaw.expect (fun d =>
      signed 0 (winValue (a == b) + winValue ((c == y) == d))) =
      signed 0 (winValue (a == b)) := by
  rw [carriedBitLaw, FinDist.expect_mix, FinDist.expect_pure, FinDist.expect_pure]
  cases y <;> cases a <;> cases b <;> cases c <;> norm_num [signed, winValue]

private theorem live_uniform_left (y a b d : Bool) :
    carriedBitLaw.expect (fun c =>
      signed 1 (winValue (a == b) + winValue ((c == y) == d))) =
      signed 1 (winValue (a == b)) := by
  rw [carriedBitLaw, FinDist.expect_mix, FinDist.expect_pure, FinDist.expect_pure]
  cases y <;> cases a <;> cases b <;> cases d <;> norm_num [signed, winValue]

/-- An arbitrary legal focal law cannot improve against the other player's
fair continuation, even at a hidden history with zero current reach. -/
theorem liveSecond_uniform_opponent (strategy : Profile (model fullPrior).behavioralSignature)
    (x y a b : Bool) (who : Player)
    (fair : ∀ other : Player, other ≠ who →
      liveSecondLaw strategy x y a b other = carriedBitLaw) :
    ((model fullPrior).runBehavioralFrom strategy 1 (decode (.second x y a b))).expect
        (cfrPayoff who) = signed who (winValue (a == b)) := by
  rw [liveSecond_value]
  rcases (by decide : ∀ player : Fin 2, player = 0 ∨ player = 1) who with rfl | rfl
  · rw [fair 1 (by decide)]
    simp only [live_uniform_right, FinDist.expect_const]
  · rw [fair 0 (by decide), FinDist.expect_comm]
    simp only [live_uniform_left, FinDist.expect_const]

/-- A genuinely live depth-two cut uses a constructed fair continuation,
with exact conditional information values rather than an assumed score bound. -/
def liveControlOracle : CFRDValueOracle (model fullPrior) :=
  cfrDExactValueOracle (model fullPrior) decisionClock cfrFallback cfrPayoff 2 1
    (fun _ _ => liveFairContinuation)

/-- Exact information-state accuracy holds at every round of the actual driver. -/
theorem liveControl_accurate :
    CFRDDepthAccurate (model fullPrior) decisionClock cfrFallback cfrPayoff 2 1
      liveControlOracle 0 :=
  cfrDExactValueOracle_accurate (model fullPrior) decisionClock cfrFallback cfrPayoff 2 1 _

/-- The next-stage action is the constructed continuation, not a trunk action. -/
theorem liveControl_second_policy (n : Nat) (x y a b : Bool) (who : Player) :
    cfrDDepthPlay (model fullPrior) decisionClock cfrFallback cfrPayoff 2 1
        liveControlOracle n who
        ((model fullPrior).infoOf who (decode (.second x y a b)).trace) =
      liveFairContinuation who
        ((model fullPrior).infoOf who (decode (.second x y a b)).trace) := by
  rw [cfrDDepthPlay_eq]
  unfold cfrDDepthProfile
  have depth : decisionClock.depth who
      ((model fullPrior).infoOf who (decode (.second x y a b)).trace) = 2 := by
    rw [decisionClock.correct]
    rfl
  rw [show cfrDDepthTrunk (model fullPrior) decisionClock 2 who
      ((model fullPrior).infoOf who (decode (.second x y a b)).trace) = false by
    simp only [cfrDDepthTrunk, depth, lt_self_iff_false, decide_false], if_neg (by decide)]
  rfl

/-- Independent fair second-round choices are present at every legal hidden history. -/
theorem liveControl_second_law (n : Nat) (x y a b : Bool) (who : Player) :
    liveSecondLaw
        (cfrDDepthPlay (model fullPrior) decisionClock cfrFallback cfrPayoff 2 1
          liveControlOracle n) x y a b who = carriedBitLaw := by
  unfold liveSecondLaw
  rw [liveControl_second_policy]
  exact liveFairSecondLaw x y a b who

/-- Every complete legal future deviation has zero gain at every live cut
history. This supplies, rather than assumes, conditional continuation optimality. -/
theorem liveControl_leaf_gain (n : Nat) (x y a b : Bool) (who : Player)
    (target : (model fullPrior).BehavioralPolicy who) :
    cfrDLeafGain (model fullPrior)
      (cfrDDepthPlay (model fullPrior) decisionClock cfrFallback cfrPayoff 2 1
        liveControlOracle n) who target (cfrPayoff who) 1 (decode (.second x y a b)) = 0 := by
  unfold cfrDLeafGain
  rw [liveSecond_uniform_opponent _ x y a b who (by
      intro other different
      unfold liveSecondLaw
      rw [Profile.update_of_ne _ _ different, liveControl_second_policy]
      exact liveFairSecondLaw x y a b other),
    liveSecond_uniform_opponent _ x y a b who (by
      intro other _
      exact liveControl_second_law n x y a b other), sub_self]

private theorem live_fibre_support {A B : Type*} (law : FinDist A)
    (observe : A → B) (info : B) (value : A)
    (reached : value ∈ (law.condOnFibre observe info).support) : value ∈ law.support := by
  unfold FinDist.condOnFibre at reached
  split at reached
  · exact (FinDist.support_condOn _ _ _ reached).2
  · exact reached

private theorem live_gain_of_depth_two
    (base : Profile (model fullPrior).behavioralSignature) (who : Player)
    (target : (model fullPrior).BehavioralPolicy who)
    (gain : ∀ x y a b : Bool,
      cfrDLeafGain (model fullPrior) base who target (cfrPayoff who) 1
        (decode (.second x y a b)) = 0)
    (history : (protocol fullPrior).History) (depth : history.trace.length = 2) :
    cfrDLeafGain (model fullPrior) base who target (cfrPayoff who) 1 history = 0 := by
  obtain ⟨row, rfl⟩ := decode_surjective history
  cases row with
  | initial => have bad : (0 : Nat) = 2 := depth; omega
  | drawn x y => have bad : (1 : Nat) = 2 := depth; omega
  | second x y a b => exact gain x y a b
  | finished x y a b c d => have bad : (3 : Nat) = 2 := depth; omega

private theorem live_optimal_of_pointwise
    (base : Profile (model fullPrior).behavioralSignature) (who : Player)
    (gain : ∀ (target : (model fullPrior).BehavioralPolicy who) (x y a b : Bool),
      cfrDLeafGain (model fullPrior) base who target (cfrPayoff who) 1
        (decode (.second x y a b)) = 0) :
    CFRDLeafOptimal (model fullPrior) base cfrFallback who (cfrPayoff who) 2 1 0 := by
  intro target info sampled
  unfold conditionalOracleValue
  apply FinDist.expect_le_of_forall
  intro history reached
  have observed := congrArg Prod.snd (conditionalOracle_support
    (unilateralReferenceLaw (model fullPrior) base cfrFallback who 2)
    (fun h : (protocol fullPrior).History =>
      ((model fullPrior).infoOf who h.trace, cfrDCutLive 1 h))
    (info, true) sampled history reached)
  have not_terminal : ¬ (protocol fullPrior).terminal history.state := by
    have live : cfrDCutLive 1 history = true := observed
    simpa only [cfrDCutLive, decide_eq_true_eq, ne_eq, one_ne_zero, not_false_eq_true,
      true_and] using live
  have sampled_history := live_fibre_support _ _ _ history reached
  have depth : history.trace.length = 2 := by
    rcases (model fullPrior).terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
      _ 2 (protocol fullPrior).initHistory history sampled_history with terminal | length
    · exact False.elim (not_terminal terminal)
    · exact length
  rw [live_gain_of_depth_two base who target (gain target) history depth]

/-- All live cut fibers satisfy optimality, including histories reached only
under the positive counterfactual reference and arbitrary future deviations. -/
theorem liveControl_leaf_optimal :
    CFRDDepthLeafOptimal (model fullPrior) decisionClock cfrFallback cfrPayoff 2 1
      liveControlOracle 0 := by
  intro n who
  exact live_optimal_of_pointwise _ who (fun target x y a b =>
    liveControl_leaf_gain n x y a b who target)

/-- Positive validation at a genuine live cut: the complete driver satisfies
its finite-time guarantee with both leaf contracts proved from game semantics. -/
theorem liveControl_isNash (t : Nat) [NeZero t] :
    IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreferenceWithin
        (cfrDDepthMeanBudget (model fullPrior) decisionClock cfrFallback 2 1 2 0 0 0 t +
          cfrDDepthMeanBudget (model fullPrior) decisionClock cfrFallback 2 1 2 0 0 1 t)
        (fun history who => cfrPayoff who history))
      (cfrDDepthAveragedProfile (model fullPrior) decisionClock cfrFallback cfrPayoff 2 1
        liveControlOracle t) :=
  cfrDDepthAveragedProfile_isNash (model fullPrior) decisionClock (perfectRecall fullPrior)
    cfrFallback cfrPayoff (cumulative_zeroSum fullPrior) 2 1 liveControlOracle 2 0 0
    (by norm_num) (le_refl _) (le_refl _) cfrPayoff_abs_le_two
    liveControl_accurate liveControl_leaf_optimal t

end GameTheory.ReBeL.Examples.HiddenTypes
