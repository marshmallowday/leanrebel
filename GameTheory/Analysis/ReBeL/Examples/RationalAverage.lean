/-
# Canonical Nash guarantees for the executed hidden-type rational solver

All concrete game and encoding obligations have been supplied by the preceding
modules. Own-reach averaging preserves every active local law, and inactive
menus have their unique legal no-op. The final guarantee covers every canonical
behavioral deviation; no primitive certificate, regret oracle or assumed solver
trace is left as a hypothesis. Zero rounds return the explicitly chosen fallback.
-/

import GameTheory.Analysis.ReBeL.Examples.RationalIteration
import GameTheory.Analysis.ReBeL.RationalAverageEquiv

noncomputable section

namespace GameTheory.ReBeL.Rational.HiddenTypes.Canonical

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Examples.HiddenTypes

/-- The full legal history space is finite independently of the solver's policies. -/
local instance averageHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Canonical local observations admit equality for proof-level policy replacement. -/
local instance averageInfoDecidableEq (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- The original local menus remain finite subtypes of optional Boolean actions. -/
local instance averageChoiceFintype (who : Player) (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- The first runtime representative has the original information-own-reach weight.
Its existence follows from the complete legal enumeration, not from positive reach. -/
theorem concrete_informationReach_correct (numeric : NumericProfile)
    (semantic : Profile (model fullPrior).behavioralSignature)
    (hreal : RowRealizes numeric semantic) (who : Player) (key : ActiveKey) :
    (table.informationReach numeric who key.1 : ℝ) =
      informationOwnReach (model fullPrior) semantic who (decodeInfo key.1) := by
  classical
  cases hfind : rows.find? (fun row => decide (information who row = key.1)) with
  | none =>
      obtain ⟨row, hrow⟩ := active_key_realized who key.1 key.2
      have hnot := List.find?_eq_none.mp hfind row (rows_complete row)
      exact False.elim (hnot (by simp [hrow]))
  | some row =>
      have hmatch : information who row = key.1 :=
        of_decide_eq_true (List.find?_eq_some_iff_append.mp hfind).1
      calc
        _ = (table.ownReach numeric who row : ℝ) := by
          unfold HistoryTable.informationReach
          rw [show table.histories = rows from rfl,
            show table.info = information from rfl, hfind]
        _ = (model fullPrior).playerReachProbability semantic who (decode row).trace :=
          ownReach_correct numeric semantic hreal who row
        _ = informationOwnReach (model fullPrior) semantic who
            ((model fullPrior).infoOf who (decode row).trace) :=
          (informationOwnReach_eq_player (model fullPrior) (perfectRecall fullPrior)
            semantic who (decode row)).symm
        _ = _ := congrArg (informationOwnReach (model fullPrior) semantic who)
          ((information_matches who row key).mpr hmatch)

/-- Averaging the actual completed numeric rounds gives precisely the canonical
own-reach average at every active legal action, including zero-mass fallbacks. -/
theorem concrete_key_average_correct (horizon rounds : ℕ) [NeZero rounds]
    (who : Player) (key : ActiveKey) (a : Choice key.1) :
    (table.average fallback horizon rounds who key.1 a : ℝ) =
      (cfrAveragedProfile (model fullPrior) decisionClock cfrFallback cfrPayoff horizon rounds
        who (decodeInfo key.1)).prob (keyChoiceEquiv who key a) := by
  let plays : Fin rounds → Profile (model fullPrior).behavioralSignature :=
    fun round => cfrPlay (model fullPrior) decisionClock cfrFallback cfrPayoff horizon round.val
  let weights : ReachWeights (Fin rounds) :=
    ⟨fun round => informationOwnReach (model fullPrior) (plays round) who (decodeInfo key.1),
      fun round => (informationOwnReach_unitInterval (model fullPrior) (plays round)
        who (decodeInfo key.1)).1⟩
  have hscale : 0 < (rounds : ℝ)⁻¹ := by
    apply inv_pos.mpr
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne rounds)
  have hscaled : ownReachWeights (model fullPrior) (cfrIterationLaw rounds) plays
      who (decodeInfo key.1) = weights.scale (rounds : ℝ)⁻¹ hscale.le := by
    simp only [weights, ownReachWeights, ReachWeights.scale,
      cfrIterationLaw, FinDist.prob_ofWeights]
  calc
    _ = (weights.average (fun round => plays round who (decodeInfo key.1))
        (FinDist.pure (keyChoiceEquiv who key (fallback who key.1)))).prob
          (keyChoiceEquiv who key a) := by
      apply cast_weightedPolicy_equiv
      · intro round
        exact concrete_informationReach_correct _ _ (concrete_play_correct horizon round.val)
          who key
      · intro round action
        exact concrete_key_play_correct horizon round.val who key action
    _ = (weights.average (fun round => plays round who (decodeInfo key.1))
        (FinDist.pure (cfrFallback who (decodeInfo key.1)))).prob
          (keyChoiceEquiv who key a) := by rw [fallback_key_correct]
    _ = ((weights.scale (rounds : ℝ)⁻¹ hscale.le).average
        (fun round => plays round who (decodeInfo key.1))
        (FinDist.pure (cfrFallback who (decodeInfo key.1)))).prob
          (keyChoiceEquiv who key a) := by
      rw [ReachWeights.average_scale weights _ _ _ hscale]
    _ = _ := by
      rw [← hscaled]
      rfl

/-- The inactive coordinate always has its unique legal probability one.
This covers empty averaging, unreachable observations and every positive round count. -/
theorem concrete_average_idle (horizon rounds : ℕ) (who : Player) :
    table.average fallback horizon rounds who .idle () = 1 := by
  have hplay (round : ℕ) : table.play fallback horizon round who .idle () = 1 :=
    concrete_profile_idle (table.state fallback horizon round) who
  unfold HistoryTable.average weightedPolicy
  simp only [hplay, mul_one]
  split
  · rename_i positive
    exact div_self positive.ne'
  · simp [pointMass, fallback]

/-- The full executable average represents the original game's canonical CFR
average on every legal history, not just on the current play's support. -/
theorem concrete_average_correct (horizon rounds : ℕ) [NeZero rounds] :
    RowRealizes (table.average fallback horizon rounds)
      (cfrAveragedProfile (model fullPrior) decisionClock cfrFallback cfrPayoff horizon rounds) := by
  intro who row a
  cases row with
  | initial =>
      cases a
      calc
        _ = (1 : ℝ) := (congrArg (fun q : ℚ => (q : ℝ))
          (concrete_average_idle horizon rounds who)).trans Rat.cast_one
        _ = _ := (idle_choice_prob
          (cfrAveragedProfile (model fullPrior) decisionClock cfrFallback cfrPayoff horizon rounds)
          who .initial rfl _).symm
  | drawn x y =>
      exact concrete_key_average_correct horizon rounds who ⟨.first (own who x y), by simp⟩ a
  | second x y firstAction secondAction =>
      exact concrete_key_average_correct horizon rounds who
        ⟨.second (own who x y) (own who firstAction secondAction)
          (firstAction == secondAction), by simp⟩ a
  | finished x y firstAction secondAction finalFirst finalSecond =>
      cases a
      calc
        _ = (1 : ℝ) := (congrArg (fun q : ℚ => (q : ℝ))
          (concrete_average_idle horizon rounds who)).trans Rat.cast_one
        _ = _ := (idle_choice_prob
          (cfrAveragedProfile (model fullPrior) decisionClock cfrFallback cfrPayoff horizon rounds)
          who (.finished x y firstAction secondAction finalFirst finalSecond) rfl _).symm

/-- No observation is silently inserted before iteration zero: the empty average
is the explicit total fallback, without a probability law on an empty sample. -/
theorem solve_zero : solve 0 = fun who site => pointMass (fallback who site) := by
  funext who site a
  simp [solve, HistoryTable.average, weightedPolicy]

/-- The actual executed rational solver has the canonical finite-time approximate
Nash guarantee against every complete behavioral deviation in the original game.
All game and encoding premises are supplied; only the positive iteration count remains. -/
theorem solve_isNash (rounds : ℕ) [NeZero rounds] :
    ∃ semantic : Profile (model fullPrior).behavioralSignature,
      RowRealizes (solve rounds) semantic ∧
      IsNash ((model fullPrior).toBehavioralGameForm 3)
        (euPreferenceWithin
          (cfrCumulativeBound (model fullPrior) decisionClock 3 0 2 rounds / rounds +
            cfrCumulativeBound (model fullPrior) decisionClock 3 1 2 rounds / rounds)
          (fun history who => cfrPayoff who history)) semantic :=
  ⟨cfrAveragedProfile (model fullPrior) decisionClock cfrFallback cfrPayoff 3 rounds,
    concrete_average_correct 3 rounds, fullGame_cfr_average_isNash rounds⟩

/-- The root value computed from the executed output is the value of the very
same canonical strategy for which the uniform deviation guarantee was proved. -/
theorem solve_value_correct (rounds : ℕ) [NeZero rounds] (who : Player) :
    (table.outputValue fallback 3 rounds who : ℝ) =
      ((model fullPrior).runBehavioral
        (cfrAveragedProfile (model fullPrior) decisionClock cfrFallback cfrPayoff 3 rounds) 3).expect
          (cfrPayoff who) :=
  root_value_correct (solve rounds) _ (concrete_average_correct 3 rounds) 3 who

end GameTheory.ReBeL.Rational.HiddenTypes.Canonical
