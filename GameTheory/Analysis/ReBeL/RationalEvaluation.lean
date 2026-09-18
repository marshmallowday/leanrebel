/-
# Rational continuation evaluation refines canonical Protocol execution

The table premises certify primitive observations, terminal flags, payoffs and
one fixed legal joint's chance transition only. In particular, no continuation
value, regret, iteration trace or equilibrium guarantee is assumed. The theorem
below derives equality for every fuel budget by induction on the actual runner.
-/

import GameTheory.ReBeL.Rational.FullGame
import GameTheory.Protocol.BehavioralReach

noncomputable section

namespace GameTheory.ReBeL.Rational

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

universe ui us ua up uq uk
variable {ι : Type ui} {E : ExecutionProtocol.{ui, us, ua} ι}
variable (M : InformationModel.{ui, us, ua, up, uq, uk} E)

/-- Pointwise representation of a canonical behavioral profile by exact weights. -/
def Realizes (numeric : Profile (tableSignature E.History M.InfoState M.Choice))
    (semantic : Profile M.behavioralSignature) : Prop :=
  ∀ who info choice, (numeric who info choice : ℝ) = (semantic who info).prob choice

private theorem cast_map_sum {α : Type*} (xs : List α) (f : α → ℚ) :
    ((xs.map f).sum : ℝ) = (xs.map fun x => (f x : ℝ)).sum := by
  induction xs with
  | nil => simp
  | cons head tail ih => simp only [List.map_cons, List.sum_cons, Rat.cast_add, ih]

variable (G : HistoryTable E.History M.InfoState M.Choice)

/-- A runtime draw denotes a legal canonical joint, without exposing the world
state to any player's policy or transporting a choice between private menus. -/
def decodeJoint (hinfo : G.info = fun who h => M.infoOf who h.trace)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (draw : (who : ι) → M.Choice who (G.info who history)) :
    {joint : (who : ι) → Option (E.Action who) // E.Legal history.state joint} :=
  ⟨fun who => (draw who).1, E.legal_of_legalOption hterm fun who =>
    (M.menu_adequate who history.trace _).mp (by
      rw [← congrFun (congrFun hinfo who) history]
      exact (draw who).2)⟩

/-- Canonical one-step chance continuation after a fixed selected joint. -/
def drawLaw (hinfo : G.info = fun who h => M.infoOf who h.trace)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (draw : (who : ι) → M.Choice who (G.info who history)) : FinDist E.History :=
  (E.step history.state (decodeJoint M G hinfo history hterm draw)).bindOnSupport
    fun _ realized => FinDist.pure
      (history.extend (decodeJoint M G hinfo history hterm draw).2 realized)

/-- Sparse rows need represent only one actual chance transition; this is an
encoding certificate, not a hypothesis about policy-dependent evaluation. -/
def ChanceRows (hinfo : G.info = fun who h => M.infoOf who h.trace) : Prop :=
  ∀ (history : E.History) (hterm : ¬ E.terminal history.state)
    (draw : (who : ι) → M.Choice who (G.info who history)) (observable : E.History → ℝ),
    ((G.children history draw).map fun edge =>
      (edge.2 : ℝ) * observable edge.1).sum =
        (drawLaw M G hinfo history hterm draw).expect observable

variable [Fintype ι]

/-- The runtime draw coordinates are exactly the canonical independent product. -/
theorem behavioralJoint_decode (hinfo : G.info = fun who h => M.infoOf who h.trace)
    (semantic : Profile M.behavioralSignature) (history : E.History)
    (hterm : ¬ E.terminal history.state) :
    M.behavioralJoint semantic history.trace hterm =
      (FinDist.pi fun who => semantic who (G.info who history)).map
        (decodeJoint M G hinfo history hterm) := by
  cases G with
  | mk histories initial info terminal children payoff ownPath chanceFactors decision depth =>
      dsimp only at hinfo
      subst info
      rfl

/-- One canonical behavioral step is the same draw-then-chance operation used
by the rational evaluator. Zero and early-terminal behavior remain canonical. -/
theorem run_one_eq_table (hinfo : G.info = fun who h => M.infoOf who h.trace)
    (semantic : Profile M.behavioralSignature) (history : E.History)
    (hterm : ¬ E.terminal history.state) :
    M.runBehavioralFrom semantic 1 history =
      (FinDist.pi fun who => semantic who (G.info who history)).bind
        (drawLaw M G hinfo history hterm) := by
  rw [M.runBehavioralFrom_succ_of_not_terminal semantic 0 hterm,
    behavioralJoint_decode M G hinfo semantic history hterm, FinDist.bind_map]
  apply FinDist.bind_congr
  intro draw _
  apply FinDist.bindOnSupport_congr
  intro target realized
  rfl

variable [DecidableEq ι] [∀ who info, Fintype (M.Choice who info)]

/-- Every sparse rational continuation value agrees exactly with the existing
behavioral runner. Table correctness is checked at primitive transition rows,
not postulated at continuation, counterfactual-regret or solver level. -/
theorem value_eq_runBehavioralFrom
    (hinfo : G.info = fun who h => M.infoOf who h.trace)
    (hterminal : ∀ history, G.terminal history = true ↔ E.terminal history.state)
    (hrows : ChanceRows M G hinfo)
    (payoff : ι → E.History → ℝ)
    (hpayoff : ∀ history who, (G.payoff history who : ℝ) = payoff who history)
    (numeric : Profile (tableSignature E.History M.InfoState M.Choice))
    (semantic : Profile M.behavioralSignature) (hreal : Realizes M numeric semantic) :
    ∀ fuel history who,
      (G.value numeric fuel history who : ℝ) =
        (M.runBehavioralFrom semantic fuel history).expect (payoff who) := by
  have shortcut (x y : ℚ) : (if x = 0 then 0 else x * y) = x * y := by
    by_cases h : x = 0 <;> simp [h]
  intro fuel
  induction fuel with
  | zero =>
      intro history who
      simpa only [HistoryTable.value, InformationModel.runBehavioralFrom,
        runRandomizedFor_zero, FinDist.expect_pure] using hpayoff history who
  | succ fuel ih =>
      intro history who
      by_cases hterm : E.terminal history.state
      · rw [HistoryTable.value, if_pos ((hterminal history).mpr hterm),
          M.runBehavioralFrom_of_terminal semantic (fuel + 1) hterm,
          FinDist.expect_pure]
        exact hpayoff history who
      · have hfalse : ¬ G.terminal history = true :=
          fun h => hterm ((hterminal history).mp h)
        rw [HistoryTable.value, if_neg hfalse]
        simp only [shortcut]
        rw [show fuel + 1 = 1 + fuel by omega,
          M.runBehavioralFrom_add semantic 1 fuel history,
          run_one_eq_table M G hinfo semantic history hterm,
          FinDist.expect_bind, FinDist.expect_bind, FinDist.expect_eq_sum]
        push_cast
        apply Finset.sum_congr rfl
        intro draw _
        rw [FinDist.prob_pi]
        have hjoint : (G.jointWeight numeric history draw : ℝ) =
            ∏ player, (semantic player (G.info player history)).prob (draw player) := by
          unfold HistoryTable.jointWeight
          push_cast
          exact Finset.prod_congr rfl fun player _ => hreal player _ _
        rw [hjoint]
        congr 1
        rw [← hrows history hterm draw]
        simpa only [cast_map_sum, Rat.cast_mul, ih]

end GameTheory.ReBeL.Rational
