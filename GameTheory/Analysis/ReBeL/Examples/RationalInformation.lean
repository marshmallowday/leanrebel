/-
# Runtime decision keys preserve complete local information

At an active history the runtime key is an exact encoding of the canonical
full action-observation history, including one's own first action. The idle key
is deliberately not claimed to encode terminal observations injectively.
Both Boolean actions are in bijection with the actual canonical legal menu.
These are encoding lemmas, not an assumed solver or regret correspondence.
-/

import GameTheory.Analysis.ReBeL.Examples.RationalCodec

noncomputable section

namespace GameTheory.ReBeL.Rational.HiddenTypes.Canonical

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.ReBeL.Examples.HiddenTypes

/-- The concrete local observation carrier contains no opponent type or world state. -/
abbrev LocalInfo := AOH Bool (Option Bool) Phase

/-- Reconstruct the full observation history at each runtime decision key. -/
def decodeInfo : Site → LocalInfo
  | .idle => .initial none .initial
  | .first ownType =>
      .step (.initial none .initial) none (some ownType) .first
  | .second ownType ownAction result =>
      .step (.step (.initial none .initial) none (some ownType) .first)
        (some ownAction) none (.second result)

/-- Read a decision key from local observations alone. Other observations have
no active runtime decision; this includes genuine terminal observations. -/
def encodeInfo : LocalInfo → Site
  | .step (.initial none .initial) none (some ownType) .first => .first ownType
  | .step (.step (.initial none .initial) none (some ownType) .first)
      (some ownAction) none (.second result) => .second ownType ownAction result
  | _ => .idle

/-- No field of an active key is lost in reconstructing its full observations. -/
theorem encode_decodeInfo (site : Site) : encodeInfo (decodeInfo site) = site := by
  cases site <;> rfl

/-- Distinct keys are distinct full local histories, including own-action memory. -/
theorem decodeInfo_injective : Function.Injective decodeInfo :=
  Function.LeftInverse.injective encode_decodeInfo

/-- Every runtime observation is read from the actual canonical trace.
Even inactive rows use the same local projection, not the physical state. -/
theorem encodeInfo_actual (who : Player) (row : Row) :
    encodeInfo ((model fullPrior).infoOf who (decode row).trace) = information who row := by
  cases row <;> rfl

/-- At active rows the correspondence is invertible; there is no compressed
memory or extra disclosure hidden in the runtime decision interface. -/
theorem info_decode_active (who : Player) (row : Row)
    (hactive : information who row ≠ .idle) :
    (model fullPrior).infoOf who (decode row).trace = decodeInfo (information who row) := by
  cases row with
  | initial => exact False.elim (hactive rfl)
  | drawn x y => rfl
  | second x y a b => rfl
  | finished x y a b c d => exact False.elim (hactive rfl)

/-- Exactly the same active histories are indistinguishable in both representations. -/
theorem active_information_eq_iff (who : Player) (first second : Row)
    (hfirst : information who first ≠ .idle) (hsecond : information who second ≠ .idle) :
    (model fullPrior).infoOf who (decode first).trace =
        (model fullPrior).infoOf who (decode second).trace ↔
      information who first = information who second := by
  constructor
  · intro h
    exact (encodeInfo_actual who first).symm.trans
      ((congrArg encodeInfo h).trans (encodeInfo_actual who second))
  · intro h
    rw [info_decode_active who first hfirst, info_decode_active who second hsecond, h]

/-- The key space covers all canonical active histories, not just solver support. -/
theorem active_information_reconstructed (who : Player)
    (history : (protocol fullPrior).History)
    (hactive : (protocol fullPrior).active history.state who) :
    ∃ site : Site, site ≠ .idle ∧ (model fullPrior).infoOf who history.trace = decodeInfo site := by
  obtain ⟨row, rfl⟩ := decode_surjective history
  cases row with
  | initial => exact False.elim hactive
  | drawn x y =>
      exact ⟨information who (.drawn x y), by simp [information], rfl⟩
  | second x y a b =>
      exact ⟨information who (.second x y a b), by simp [information], rfl⟩
  | finished x y a b c d => exact False.elim hactive

/-- Conversely every active key has a legal canonical history, including
first-action/result combinations that the fallback never reaches. -/
theorem active_key_realized (who : Player) (site : Site) (hactive : site ≠ .idle) :
    ∃ row : Row, information who row = site := by
  cases site with
  | idle => exact False.elim (hactive rfl)
  | first ownType =>
      exact ⟨.drawn ownType ownType, by simp [information, own]⟩
  | second ownType ownAction result =>
      fin_cases who
      · refine ⟨.second ownType ownType ownAction (if result then ownAction else !ownAction), ?_⟩
        cases result <;> cases ownAction <;> rfl
      · refine ⟨.second ownType ownType (if result then ownAction else !ownAction) ownAction, ?_⟩
        cases result <;> cases ownAction <;> rfl

/-- No legal Boolean action is removed at a represented active observation. -/
theorem action_mem_menu (who : Player) (site : Site) (hactive : site ≠ .idle) (a : Bool) :
    some a ∈ (model fullPrior).menu who (decodeInfo site) := by
  cases site with
  | idle => exact False.elim (hactive rfl)
  | first ownType => exact ⟨a, rfl⟩
  | second ownType ownAction result => exact ⟨a, rfl⟩

/-- Every canonical active choice is a Boolean action; no no-op is inserted. -/
theorem choice_eq_some (who : Player) (site : Site) (hactive : site ≠ .idle)
    (choice : (model fullPrior).Choice who (decodeInfo site)) :
    ∃ a : Bool, choice.1 = some a := by
  cases site with
  | idle => exact False.elim (hactive rfl)
  | first ownType => exact choice.2
  | second ownType ownAction result => exact choice.2

/-- Exact legal-menu equivalence at every active decision key. Together with
the full-information equivalence this rules out a restricted Plan-only interface. -/
def activeChoiceEquiv (who : Player) (site : Site) (hactive : site ≠ .idle) :
    Bool ≃ (model fullPrior).Choice who (decodeInfo site) where
  toFun a := ⟨some a, action_mem_menu who site hactive a⟩
  invFun choice := choice.1.getD false
  left_inv a := rfl
  right_inv choice := by
    apply Subtype.ext
    obtain ⟨a, ha⟩ := choice_eq_some who site hactive choice
    simp [ha]

end GameTheory.ReBeL.Rational.HiddenTypes.Canonical
