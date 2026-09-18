/-
# Runtime history codes are exactly the canonical hidden-type histories

The runtime code retains all selected actions, even after physical-state merges.
The decoder constructs actual legal Protocol traces. A proved inverse and
surjectivity certify that the 85-row runtime enumeration neither duplicates nor
omits a canonical history. Information-key and full-solver transport remain
separate obligations; this module does not claim them from an enumeration test.
-/

import GameTheory.ReBeL.Rational.HiddenTypes
import GameTheory.ReBeL.Examples.HiddenTypesHistories
import Mathlib.Tactic.FinCases

noncomputable section

namespace GameTheory.ReBeL.Rational.HiddenTypes

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

namespace Canonical

open GameTheory.ReBeL.Examples.HiddenTypes

/-- Preserve both final actions in a legal canonical history, not only its result. -/
def finish (x y a b c d : Bool) : (protocol fullPrior).History :=
  (firstHistory (x, y) (fun who => own who a b)).extend
    (joint := fun who => some (own who c d))
    (show (protocol fullPrior).Legal
      (.second (x, y) (firstResult (fun who => some (own who a b))))
      (fun who => some (own who c d)) from
        ⟨by simp [terminal], by intro who; trivial⟩)
    (target := .finished (firstResult (fun who => some (own who a b)))
      (finalResult (x, y) (fun who => some (own who c d))))
    (by exact FinDist.mem_support_pure.mpr rfl)

/-- Every runtime row denotes a genuine legal history of the existing game. -/
def decode : Row → (protocol fullPrior).History
  | .initial => (protocol fullPrior).initHistory
  | .drawn x y => fullDraw (x, y)
  | .second x y a b => firstHistory (x, y) (fun who => own who a b)
  | .finished x y a b c d => finish x y a b c d

/-- Read the chance draw and all strategic choices from a canonical trace.
Fallback cases in this total reader cannot occur in a decoded legal history. -/
def readTrace : {state : (protocol fullPrior).State} →
    (protocol fullPrior).Trace state → Row
  | _, .start => .initial
  | target, .extend prior joint _ _ =>
      match readTrace prior with
      | .initial => match target with
        | .first (x, y) => .drawn x y
        | _ => .initial
      | .drawn x y => .second x y (action joint 0) (action joint 1)
      | .second x y a b => .finished x y a b (action joint 0) (action joint 1)
      | .finished _ _ _ _ _ _ => .initial

/-- The runtime code of a complete canonical history. -/
def encode (history : (protocol fullPrior).History) : Row := readTrace history.trace

/-- Decoding retains every history field exactly, including both hidden types
and both simultaneous action tuples. -/
theorem encode_decode (row : Row) : encode (decode row) = row := by
  cases row <;> rfl

/-- Distinct runtime rows do not collapse when physical states merge. -/
theorem decode_injective : Function.Injective decode :=
  Function.LeftInverse.injective encode_decode

private theorem joint_of_active {state : (protocol fullPrior).State}
    (joint : Player → Option Bool) (legal : (protocol fullPrior).Legal state joint)
    (hactive : ∀ who, (protocol fullPrior).active state who) :
    ∃ a b, joint = fun who => some (own who a b) := by
  have hsome (who : Player) : joint who = some (action joint who) := by
    cases heq : joint who with
    | none =>
        have h := legal.2 who
        rw [heq] at h
        exact False.elim (h (hactive who))
    | some a => simp [action, heq]
  refine ⟨action joint 0, action joint 1, ?_⟩
  funext who
  fin_cases who <;> simpa [own] using hsome _

/-- The decoder image is closed under every legal chance-supported extension,
not just the transitions selected by the current solver policy. -/
theorem decode_closed (row : Row) (joint : Player → Option Bool)
    (legal : (protocol fullPrior).Legal (decode row).state joint)
    (target : (protocol fullPrior).State)
    (realized : target ∈ ((protocol fullPrior).step (decode row).state ⟨joint, legal⟩).support) :
    ∃ next, decode next = (decode row).extend legal realized := by
  cases row with
  | initial =>
      have hnoop : joint = fun _ => none :=
        (protocol fullPrior).eq_noop_of_legal_of_inactive legal (fun _ => not_false)
      subst joint
      have htarget : target ∈ (FinDist.map State.first fullPrior).support := realized
      rw [FinDist.support_map] at htarget
      obtain ⟨⟨x, y⟩, _, rfl⟩ := htarget
      exact ⟨.drawn x y, rfl⟩
  | drawn x y =>
      obtain ⟨a, b, rfl⟩ := joint_of_active joint legal (fun _ => trivial)
      have htarget : target ∈ (FinDist.pure
        (State.second (x, y) (firstResult (fun who => some (own who a b))))).support := realized
      rw [FinDist.mem_support_pure] at htarget
      subst target
      exact ⟨.second x y a b, rfl⟩
  | second x y a b =>
      obtain ⟨c, d, rfl⟩ := joint_of_active joint legal (fun _ => trivial)
      have htarget : target ∈ (FinDist.pure
        (State.finished (firstResult (fun who => some (own who a b)))
          (finalResult (x, y) (fun who => some (own who c d))))).support := realized
      rw [FinDist.mem_support_pure] at htarget
      subst target
      exact ⟨.finished x y a b c d, rfl⟩
  | finished x y a b c d => exact False.elim (legal.1 trivial)

/-- Every canonical legal history has a runtime row, regardless of its reach
probability under any particular profile. -/
theorem decode_surjective : Function.Surjective decode := by
  have closure (history : (protocol fullPrior).History) (hh : ∃ row, decode row = history)
      (joint : Player → Option Bool) (legal : (protocol fullPrior).Legal history.state joint)
      (target : (protocol fullPrior).State)
      (realized : target ∈ ((protocol fullPrior).step history.state ⟨joint, legal⟩).support) :
      ∃ row, decode row = history.extend legal realized := by
    obtain ⟨row, rfl⟩ := hh
    exact decode_closed row joint legal target realized
  intro history
  rcases history with ⟨state, trace⟩
  induction trace with
  | start => exact ⟨.initial, rfl⟩
  | extend prior joint legal realized ih =>
      exact closure ⟨_, prior⟩ ih joint legal _ realized

/-- Encoding and decoding also preserve every canonical history. -/
theorem decode_encode (history : (protocol fullPrior).History) :
    decode (encode history) = history := by
  obtain ⟨row, rfl⟩ := decode_surjective history
  rw [encode_decode]

/-- A genuine history equivalence; the runtime carrier is an encoding, not
an assumed tree-shaped physical state space or a parallel execution semantics. -/
def historyEquiv : Row ≃ (protocol fullPrior).History where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode

/-- Runtime enumeration contains each history code once. -/
theorem rows_nodup : rows.Nodup := by decide

/-- Runtime enumeration includes every supported legal history code. -/
theorem rows_complete (row : Row) : row ∈ rows := by
  cases row with
  | initial => decide
  | drawn x y => cases x <;> cases y <;> decide
  | second x y a b => cases x <;> cases y <;> cases a <;> cases b <;> decide
  | finished x y a b c d =>
      cases x <;> cases y <;> cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- The decoded list is a duplicate-free canonical-history enumeration. -/
theorem decoded_rows_nodup : (rows.map decode).Nodup :=
  rows_nodup.map decode_injective

/-- No off-policy or state-merging history is missing from the actual enumeration. -/
theorem decoded_rows_complete (history : (protocol fullPrior).History) :
    history ∈ rows.map decode := by
  obtain ⟨row, rfl⟩ := decode_surjective history
  exact List.mem_map.mpr ⟨row, rows_complete row, rfl⟩

end Canonical

end GameTheory.ReBeL.Rational.HiddenTypes
