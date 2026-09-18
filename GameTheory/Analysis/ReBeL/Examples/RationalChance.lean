/-
# Each executable transition row is the canonical chance transition

The proof fixes a legal independently selected joint action, then compares the
sparse rational successors with the original Protocol transition law. The
initial private chance draw, both simultaneous stages and stopping are kept
separate. No policy-dependent continuation identity is assumed.
-/

import GameTheory.Analysis.ReBeL.Examples.RationalPrimitives
import GameTheory.Protocol.BehavioralReach

noncomputable section

namespace GameTheory.ReBeL.Rational.HiddenTypes.Canonical

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Protocol.InformationModel GameTheory.Math.Probability
open GameTheory.ReBeL.Examples.HiddenTypes

/-- Independent draw coordinates are reindexed separately for each player. -/
def rowJointEquiv (row : Row) :
    ((who : Player) → Choice (information who row)) ≃
      ((who : Player) → (model fullPrior).Choice who
        ((model fullPrior).infoOf who (decode row).trace)) :=
  Equiv.piCongrRight fun who => rowChoiceEquiv who row

/-- The selected runtime draw denotes exactly one legal canonical joint. -/
def rowJoint (row : Row) (hterm : ¬ (protocol fullPrior).terminal (decode row).state)
    (draw : (who : Player) → Choice (information who row)) :
    {joint : Player → Option Bool // (protocol fullPrior).Legal (decode row).state joint} :=
  ⟨fun who => (rowChoiceEquiv who row (draw who)).1,
    (protocol fullPrior).legal_of_legalOption hterm fun who =>
      ((model fullPrior).menu_adequate who (decode row).trace _).mp
        (rowChoiceEquiv who row (draw who)).2⟩

private def chosenContinuation (history : (protocol fullPrior).History)
    (joint : {joint : Player → Option Bool // (protocol fullPrior).Legal history.state joint}) :
    FinDist (protocol fullPrior).History :=
  ((protocol fullPrior).step history.state joint).bindOnSupport
    fun _ realized => FinDist.pure (history.extend joint.2 realized)

/-- The actual one-step continuation law after fixing that legal joint. -/
def rowDrawLaw (row : Row) (hterm : ¬ (protocol fullPrior).terminal (decode row).state)
    (draw : (who : Player) → Choice (information who row)) :
    FinDist (protocol fullPrior).History :=
  ((protocol fullPrior).step (decode row).state (rowJoint row hterm draw)).bindOnSupport
    fun _ realized => FinDist.pure ((decode row).extend (rowJoint row hterm draw).2 realized)

/-- The first step is the original full-support prior, not a policy-selected sample. -/
theorem rowDrawLaw_initial
    (hterm : ¬ (protocol fullPrior).terminal (decode .initial).state)
    (draw : (who : Player) → Choice (information who .initial)) :
    rowDrawLaw .initial hterm draw =
      fullPrior.map (fun types => decode (.drawn types.1 types.2)) := by
  let total : State → FinDist (protocol fullPrior).History
    | .first (x, y) => FinDist.pure (decode (.drawn x y))
    | _ => FinDist.pure (decode .initial)
  calc
    _ = (fullPrior.map State.first).bind total := by
      apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
      intro target realized
      have htarget : target ∈ (fullPrior.map State.first).support := realized
      rw [FinDist.support_map] at htarget
      obtain ⟨⟨x, y⟩, _, rfl⟩ := htarget
      rfl
    _ = _ := by
      rw [FinDist.bind_map]
      rfl

/-- The first strategic step preserves both selected actions in the history. -/
theorem rowDrawLaw_drawn (x y : Bool)
    (hterm : ¬ (protocol fullPrior).terminal (decode (.drawn x y)).state)
    (draw : (who : Player) → Choice (information who (.drawn x y))) :
    rowDrawLaw (.drawn x y) hterm draw =
      FinDist.pure (decode (.second x y (draw 0) (draw 1))) := by
  have hjoint : rowJoint (.drawn x y) hterm draw =
      ⟨fun who => some (own who (draw 0) (draw 1)),
        ⟨hterm, by intro who; trivial⟩⟩ := by
    apply Subtype.ext
    funext who
    fin_cases who <;> rfl
  calc
    _ = chosenContinuation (decode (.drawn x y))
        ⟨fun who => some (own who (draw 0) (draw 1)),
          ⟨hterm, by intro who; trivial⟩⟩ :=
      congrArg (chosenContinuation (decode (.drawn x y))) hjoint
    _ = _ := by
      simp only [chosenContinuation, decode, firstHistory, fullDraw, drawHistory,
        History.extend, protocol, transition, FinDist.pure_bindOnSupport]

/-- The second strategic step retains the complete action tuple despite state merging. -/
theorem rowDrawLaw_second (x y a b : Bool)
    (hterm : ¬ (protocol fullPrior).terminal (decode (.second x y a b)).state)
    (draw : (who : Player) → Choice (information who (.second x y a b))) :
    rowDrawLaw (.second x y a b) hterm draw =
      FinDist.pure (decode (.finished x y a b (draw 0) (draw 1))) := by
  have hjoint : rowJoint (.second x y a b) hterm draw =
      ⟨fun who => some (own who (draw 0) (draw 1)),
        ⟨hterm, by intro who; trivial⟩⟩ := by
    apply Subtype.ext
    funext who
    fin_cases who <;> rfl
  calc
    _ = chosenContinuation (decode (.second x y a b))
        ⟨fun who => some (own who (draw 0) (draw 1)),
          ⟨hterm, by intro who; trivial⟩⟩ :=
      congrArg (chosenContinuation (decode (.second x y a b))) hjoint
    _ = _ := by
      simp only [chosenContinuation, decode, finish, firstHistory, fullDraw, drawHistory,
        History.extend, protocol, transition, FinDist.pure_bindOnSupport]

/-- Sparse numeric successor rows have exactly the expected value of the
canonical chance transition for every real observable on complete histories. -/
theorem children_expect (row : Row)
    (hterm : ¬ (protocol fullPrior).terminal (decode row).state)
    (draw : (who : Player) → Choice (information who row))
    (observable : (protocol fullPrior).History → ℝ) :
    ((children row draw).map fun edge => (edge.2 : ℝ) * observable (decode edge.1)).sum =
      (rowDrawLaw row hterm draw).expect observable := by
  cases row with
  | initial =>
      rw [rowDrawLaw_initial, FinDist.expect_map, FinDist.expect_eq_sum]
      simp [children, pairs, bits, fullPrior, Fintype.sum_prod_type,
        FinDist.prob_uniformOfFintype]
      ring
  | drawn x y => simp [children, rowDrawLaw_drawn]
  | second x y a b => simp [children, rowDrawLaw_second]
  | finished x y a b c d => exact False.elim (hterm trivial)

/-- Reindexing the independent menu product changes only its representation.
There is still one independent draw per player, not a joint shared random seed. -/
theorem behavioralJoint_reindexed
    (semantic : Profile (model fullPrior).behavioralSignature) (row : Row)
    (hterm : ¬ (protocol fullPrior).terminal (decode row).state) :
    (model fullPrior).behavioralJoint semantic (decode row).trace hterm =
      (FinDist.pi fun who => semantic who ((model fullPrior).infoOf who (decode row).trace)).map
        (fun draw => rowJoint row hterm ((rowJointEquiv row).symm draw)) := by
  unfold InformationModel.behavioralJoint
  congr 1
  funext draw
  apply Subtype.ext
  funext who
  simp [rowJoint, rowJointEquiv]

/-- A canonical behavioral step factors through the runtime joint-coordinate
bijection followed by the already certified chance law. -/
theorem run_one_reindexed (semantic : Profile (model fullPrior).behavioralSignature)
    (row : Row) (hterm : ¬ (protocol fullPrior).terminal (decode row).state) :
    (model fullPrior).runBehavioralFrom semantic 1 (decode row) =
      (FinDist.pi fun who => semantic who ((model fullPrior).infoOf who (decode row).trace)).bind
        (fun draw => rowDrawLaw row hterm ((rowJointEquiv row).symm draw)) := by
  rw [(model fullPrior).runBehavioralFrom_succ_of_not_terminal semantic 0 hterm,
    behavioralJoint_reindexed semantic row hterm, FinDist.bind_map]
  apply FinDist.bind_congr
  intro draw _
  apply FinDist.bindOnSupport_congr
  intro target realized
  rfl

end GameTheory.ReBeL.Rational.HiddenTypes.Canonical
