/-
# Primitive correctness of the executable hidden-type encoding

All histories, terminal flags, legal choices and cumulative payoffs refer to
the original Protocol game. Inactive observations need not be injectively
encoded: their legal menu has exactly one no-op, whose probability is one.
No continuation value or CFR update is assumed by these primitive lemmas.
-/

import GameTheory.Analysis.ReBeL.Examples.RationalInformation
import GameTheory.ReBeL.Examples.HiddenTypesPayoff

noncomputable section

namespace GameTheory.ReBeL.Rational.HiddenTypes.Canonical

open GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.ReBeL.Examples.HiddenTypes

/-- The exact dependent shape of the runtime profile, without a hidden-history argument. -/
abbrev NumericProfile :=
  Profile (tableSignature Row (fun _ : Player => Site) (fun _ => Choice))

/-- Forget only the representation wrapper of a runtime legal choice. -/
def choiceOption : (site : Site) → Choice site → Option Bool
  | .idle, _ => none
  | .first _, a => some a
  | .second _ _ _, a => some a

/-- Every runtime menu is exactly the canonical menu at that actual history.
This includes initial and terminal singleton menus, not just the active sites. -/
def rowChoiceEquiv (who : Player) (row : Row) :
    Choice (information who row) ≃
      (model fullPrior).Choice who ((model fullPrior).infoOf who (decode row).trace) := by
  cases row with
  | initial =>
      refine {
        toFun := fun _ => ⟨none, rfl⟩
        invFun := fun _ => ()
        left_inv := ?_
        right_inv := ?_ }
      · intro a
        cases a
        rfl
      · intro a
        exact Subtype.ext a.2.symm
  | drawn x y =>
      exact activeChoiceEquiv who (.first (own who x y)) (by simp)
  | second x y a b =>
      exact activeChoiceEquiv who (.second (own who x y) (own who a b) (a == b)) (by simp)
  | finished x y a b c d =>
      refine {
        toFun := fun _ => ⟨none, rfl⟩
        invFun := fun _ => ()
        left_inv := ?_
        right_inv := ?_ }
      · intro a
        cases a
        rfl
      · intro a
        exact Subtype.ext a.2.symm

/-- The encoding neither changes an action nor substitutes a no-op at an active row. -/
theorem rowChoiceEquiv_val (who : Player) (row : Row)
    (a : Choice (information who row)) :
    (rowChoiceEquiv who row a).1 = choiceOption (information who row) a := by
  cases row <;> rfl

/-- Probability representation at every actual information occurrence.
Both sides remain information-local; the row only identifies corresponding coordinates. -/
def RowRealizes (numeric : NumericProfile)
    (semantic : Profile (model fullPrior).behavioralSignature) : Prop :=
  ∀ who row a, (numeric who (information who row) a : ℝ) =
    (semantic who ((model fullPrior).infoOf who (decode row).trace)).prob
      (rowChoiceEquiv who row a)

/-- Every law on an inactive canonical menu assigns its only legal no-op mass one. -/
theorem idle_choice_prob (semantic : Profile (model fullPrior).behavioralSignature)
    (who : Player) (row : Row) (hidle : information who row = .idle)
    (a : (model fullPrior).Choice who ((model fullPrior).infoOf who (decode row).trace)) :
    (semantic who ((model fullPrior).infoOf who (decode row).trace)).prob a = 1 := by
  let : Subsingleton (Choice (information who row)) := by rw [hidle]; infer_instance
  let : Subsingleton ((model fullPrior).Choice who
      ((model fullPrior).infoOf who (decode row).trace)) :=
    ⟨fun x y => (rowChoiceEquiv who row).symm.injective (Subsingleton.elim _ _)⟩
  rw [FinDist.eq_pure_of_subsingleton
    (semantic who ((model fullPrior).infoOf who (decode row).trace)) a,
    FinDist.prob_pure_self]

/-- Runtime terminality is exactly the canonical stopping predicate. -/
theorem terminal_correct (row : Row) :
    isTerminal row = true ↔ (protocol fullPrior).terminal (decode row).state := by
  cases row <;> simp [isTerminal, decode, finish, protocol,
    GameTheory.ReBeL.Examples.HiddenTypes.terminal, firstHistory, fullDraw, drawHistory]

/-- Active rows use the actual trace depth, without counting an iteration as a game step. -/
theorem active_depth_correct (who : Player) (row : Row)
    (hactive : information who row ≠ .idle) :
    table.depth who (information who row) = (decode row).trace.length := by
  cases row with
  | initial => exact False.elim (hactive rfl)
  | drawn x y => rfl
  | second x y a b => rfl
  | finished x y a b c d => exact False.elim (hactive rfl)

/-- The numeric payoff is the actual accumulated reward, including partial prefixes.
The statement covers every legal history code and both players. -/
theorem payoff_correct (row : Row) (who : Player) :
    (GameTheory.ReBeL.Rational.HiddenTypes.payoff row who : ℝ) =
      cumulativeUtility (reward fullPrior) (decode row) who := by
  have castWin (won : Bool) :
      (GameTheory.ReBeL.Rational.HiddenTypes.winValue won : ℝ) =
        GameTheory.ReBeL.Examples.HiddenTypes.winValue won := by
    cases won <;> norm_num [GameTheory.ReBeL.Rational.HiddenTypes.winValue,
      GameTheory.ReBeL.Examples.HiddenTypes.winValue]
  rw [cumulative_eq]
  cases row <;> fin_cases who <;>
    simp [GameTheory.ReBeL.Rational.HiddenTypes.payoff,
      potential, signed, decode, finish, firstHistory, fullDraw, drawHistory,
      ExecutionProtocol.History.extend, firstResult, finalResult, action, own, castWin]

end GameTheory.ReBeL.Rational.HiddenTypes.Canonical
