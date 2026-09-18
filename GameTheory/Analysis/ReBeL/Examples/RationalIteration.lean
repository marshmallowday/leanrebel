/-
# The concrete executable CFR trace refines the original game's CFR trace

The history, observation, menu, chance, payoff, reach and local-regret premises
have all been discharged for the actual raw table. Induction compares every
regret coordinate and the identical shared previous-round profile at every
iteration. No concrete table certificate or regret oracle is left as an input.
-/

import GameTheory.Analysis.ReBeL.Examples.RationalRegret

noncomputable section

namespace GameTheory.ReBeL.Rational.HiddenTypes.Canonical

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Examples.HiddenTypes

/-- The original finite history carrier includes all zero-reach decision prefixes. -/
local instance iterationHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Canonical full observations admit proof-level equality without altering the runtime. -/
local instance iterationInfoDecidableEq (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- Each canonical legal menu is a finite subtype of optional Boolean actions. -/
local instance iterationChoiceFintype (who : Player) (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- The explicit numeric fallback is exactly the existing canonical baseline policy. -/
theorem fallback_key_correct (who : Player) (key : ActiveKey) :
    keyChoiceEquiv who key (fallback who key.1) = cfrFallback who (decodeInfo key.1) := by
  rcases key with ⟨site, hactive⟩
  cases site with
  | idle => exact False.elim (hactive rfl)
  | first ownType => apply Subtype.ext; rfl
  | second ownType ownAction result => apply Subtype.ext; rfl

/-- Every represented key participates in the actual simultaneous runtime update. -/
theorem active_decision (who : Player) (key : ActiveKey) :
    table.decision who key.1 = true := by
  rcases key with ⟨site, hactive⟩
  cases site with
  | idle => exact False.elim (hactive rfl)
  | first ownType => rfl
  | second ownType ownAction result => rfl

/-- A raw inactive menu always returns its sole no-op with probability one. -/
theorem concrete_profile_idle (numeric : NumericProfile) (who : Player) :
    table.profile fallback numeric who .idle () = 1 := by
  rw [HistoryTable.profile,
    if_neg (show ¬ table.decision who .idle = true from Bool.false_ne_true)]
  rfl

/-- At every active key, the numeric matcher has the original canonical local law. -/
theorem concrete_key_profile (numeric : NumericProfile) (semantic : CFRState (model fullPrior))
    (hstate : ∀ who (key : ActiveKey) a,
      (numeric who key.1 a : ℝ) =
        (semantic who (canonicalSite who key)).ofLp (keyChoiceEquiv who key a))
    (who : Player) (key : ActiveKey) (a : Choice key.1) :
    (table.profile fallback numeric who key.1 a : ℝ) =
      (cfrProfile (model fullPrior) cfrFallback semantic who (decodeInfo key.1)).prob
        (keyChoiceEquiv who key a) := by
  rw [HistoryTable.profile, if_pos (active_decision who key)]
  have hmatch := cast_matchProb_equiv (keyChoiceEquiv who key) (fallback who key.1)
    (numeric who key.1) (semantic who (canonicalSite who key)) (hstate who key) a
  rw [fallback_key_correct] at hmatch
  exact hmatch.trans (congrArg
    (fun law : FinDist ((model fullPrior).Choice who (decodeInfo key.1)) =>
      law.prob (keyChoiceEquiv who key a))
    (cfrProfile_at_site (model fullPrior) cfrFallback semantic who (canonicalSite who key))).symm

/-- Matching regret coordinates determines the assembled policy at every actual
history, including canonical inactive singleton menus and all off-path decisions. -/
theorem concrete_profile_realizes (numeric : NumericProfile) (semantic : CFRState (model fullPrior))
    (hstate : ∀ who (key : ActiveKey) a,
      (numeric who key.1 a : ℝ) =
        (semantic who (canonicalSite who key)).ofLp (keyChoiceEquiv who key a)) :
    RowRealizes (table.profile fallback numeric)
      (cfrProfile (model fullPrior) cfrFallback semantic) := by
  intro who row a
  cases row with
  | initial =>
      cases a
      calc
        _ = (1 : ℝ) :=
          (congrArg (fun q : ℚ => (q : ℝ)) (concrete_profile_idle numeric who)).trans Rat.cast_one
        _ = _ := (idle_choice_prob (cfrProfile (model fullPrior) cfrFallback semantic)
          who .initial rfl _).symm
  | drawn x y =>
      exact concrete_key_profile numeric semantic hstate who
        ⟨.first (own who x y), by simp⟩ a
  | second x y firstAction secondAction =>
      exact concrete_key_profile numeric semantic hstate who
        ⟨.second (own who x y) (own who firstAction secondAction)
          (firstAction == secondAction), by simp⟩ a
  | finished x y firstAction secondAction finalFirst finalSecond =>
      cases a
      calc
        _ = (1 : ℝ) :=
          (congrArg (fun q : ℚ => (q : ℝ)) (concrete_profile_idle numeric who)).trans Rat.cast_one
        _ = _ := (idle_choice_prob (cfrProfile (model fullPrior) cfrFallback semantic)
          who (.finished x y firstAction secondAction finalFirst finalSecond) rfl _).symm

/-- Expose a raw update at a coordinate without rewriting a dependent profile carrier. -/
theorem concrete_state_succ (horizon round : ℕ) (who : Player) (key : ActiveKey)
    (a : Choice key.1) :
    table.state fallback horizon (round + 1) who key.1 a =
      if table.decision who key.1 then
        averageRegretUpdate round (table.state fallback horizon round who key.1 a)
          (table.instantaneousRegret (table.play fallback horizon round) who key.1 horizon a)
      else 0 := rfl

/-- Every generated numeric coordinate is exactly its canonical real CFR coordinate,
for every iteration, horizon, player, information set and legal action. -/
theorem concrete_state_correct (horizon round : ℕ) :
    ∀ who (key : ActiveKey) a,
      (table.state fallback horizon round who key.1 a : ℝ) =
        (cfrState (model fullPrior) decisionClock cfrFallback cfrPayoff horizon round who
          (canonicalSite who key)).ofLp (keyChoiceEquiv who key a) := by
  induction round with
  | zero =>
      intro who key a
      calc
        _ = (0 : ℝ) := Rat.cast_zero
        _ = _ := rfl
  | succ round ih =>
      have hprofile : RowRealizes (table.play fallback horizon round)
          (cfrPlay (model fullPrior) decisionClock cfrFallback cfrPayoff horizon round) :=
        concrete_profile_realizes (table.state fallback horizon round)
          (cfrState (model fullPrior) decisionClock cfrFallback cfrPayoff horizon round) ih
      intro who key a
      rw [concrete_state_succ, if_pos (active_decision who key), cast_averageRegretUpdate,
        instantaneousRegret_correct _ _ hprofile who key horizon a,
        ih who key a, cfrState_succ_at]
      rfl

/-- The actual executable solver and the existing canonical solver produce the same
full local laws in every round; no uninstantiated primitive certificate remains. -/
theorem concrete_play_correct (horizon round : ℕ) :
    RowRealizes (table.play fallback horizon round)
      (cfrPlay (model fullPrior) decisionClock cfrFallback cfrPayoff horizon round) :=
  concrete_profile_realizes (table.state fallback horizon round)
    (cfrState (model fullPrior) decisionClock cfrFallback cfrPayoff horizon round)
    (concrete_state_correct horizon round)

/-- The generated local probability correspondence at an arbitrary active key. -/
theorem concrete_key_play_correct (horizon round : ℕ) (who : Player)
    (key : ActiveKey) (a : Choice key.1) :
    (table.play fallback horizon round who key.1 a : ℝ) =
      (cfrPlay (model fullPrior) decisionClock cfrFallback cfrPayoff horizon round who
        (decodeInfo key.1)).prob (keyChoiceEquiv who key a) :=
  concrete_key_profile (table.state fallback horizon round)
    (cfrState (model fullPrior) decisionClock cfrFallback cfrPayoff horizon round)
    (concrete_state_correct horizon round) who key a

end GameTheory.ReBeL.Rational.HiddenTypes.Canonical
