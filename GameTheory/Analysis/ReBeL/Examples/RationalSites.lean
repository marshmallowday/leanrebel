/-
# The runtime decision keys cover every canonical information set

The correspondence is a bijection on genuine decisions, not a restriction to
on-policy or simplified Plan observations. Inert terminal observations remain
outside this decision index. Both legal choices and the absolute game clock
are preserved by the correspondence.
-/

import GameTheory.Analysis.ReBeL.Examples.RationalInformation
import GameTheory.ReBeL.Examples.Schedule

noncomputable section

namespace GameTheory.ReBeL.Rational.HiddenTypes.Canonical

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.ReBeL.Examples.HiddenTypes

/-- The ten genuine decision keys; the singleton inactive menu is not a decision. -/
abbrev ActiveKey := {site : Site // site ≠ .idle}

/-- At an actual row, the runtime marks exactly the canonical active player. -/
theorem row_active_iff (who : Player) (row : Row) :
    (protocol fullPrior).active (decode row).state who ↔ information who row ≠ .idle := by
  cases row <;> simp [decode, finish, firstHistory, fullDraw, drawHistory,
    ExecutionProtocol.History.extend, protocol, GameTheory.ReBeL.Examples.HiddenTypes.active,
    information]

/-- A runtime decision cannot denote an initial or terminated history. -/
theorem active_row_nonterminal (who : Player) (row : Row)
    (hactive : information who row ≠ .idle) :
    ¬ (protocol fullPrior).terminal (decode row).state := by
  cases row with
  | initial => exact False.elim (hactive rfl)
  | drawn x y => exact not_false
  | second x y a b => exact not_false
  | finished x y a b c d => exact False.elim (hactive rfl)

/-- Every active key denotes a canonical information site with a real legal witness. -/
def canonicalSite (who : Player) (key : ActiveKey) : (model fullPrior).InformationSite who :=
  ⟨decodeInfo key.1, by
    obtain ⟨row, hrow⟩ := active_key_realized who key.1 key.2
    have hactive : information who row ≠ .idle := by rw [hrow]; exact key.2
    refine ⟨⟨decode row, ?_⟩, active_row_nonterminal who row hactive,
      false, action_mem_menu who key.1 key.2 false⟩
    exact (info_decode_active who row hactive).trans (congrArg decodeInfo hrow)⟩

/-- The actual information value of this site is the full observation history. -/
@[simp]
theorem canonicalSite_val (who : Player) (key : ActiveKey) :
    (canonicalSite who key).1 = decodeInfo key.1 := rfl

/-- Distinct active keys never collapse canonical information sets. -/
theorem canonicalSite_injective (who : Player) : Function.Injective (canonicalSite who) := by
  intro first second h
  apply Subtype.ext
  exact decodeInfo_injective
    (congrArg (fun site : (model fullPrior).InformationSite who => site.1) h)

/-- Every genuine canonical decision is retained by the runtime index. -/
theorem canonicalSite_surjective (who : Player) : Function.Surjective (canonicalSite who) := by
  intro site
  obtain ⟨history, _, _, _⟩ := site.2
  obtain ⟨key, hactive, hkey⟩ := active_information_reconstructed who history.1
    (InformationSite.active (model fullPrior) site history)
  refine ⟨⟨key, hactive⟩, Subtype.ext ?_⟩
  rw [canonicalSite_val]
  exact hkey.symm.trans history.2

/-- A bijection of all actual information sets, including all off-path decisions. -/
def siteEquiv (who : Player) : ActiveKey ≃ (model fullPrior).InformationSite who :=
  Equiv.ofBijective (canonicalSite who) ⟨canonicalSite_injective who, canonicalSite_surjective who⟩

/-- Equality with a decision AOH is exactly equality with its raw key, for all rows. -/
theorem information_matches (who : Player) (row : Row) (key : ActiveKey) :
    (model fullPrior).infoOf who (decode row).trace = decodeInfo key.1 ↔
      information who row = key.1 := by
  constructor
  · intro h
    exact (encodeInfo_actual who row).symm.trans
      ((congrArg encodeInfo h).trans (encode_decodeInfo key.1))
  · intro h
    have hactive : information who row ≠ .idle := by rw [h]; exact key.2
    exact (info_decode_active who row hactive).trans (congrArg decodeInfo h)

/-- Runtime and canonical counterfactual continuations use the same absolute cut. -/
theorem canonicalSite_depth (who : Player) (key : ActiveKey) :
    decisionClock.depth who (canonicalSite who key).1 = table.depth who key.1 := by
  rw [canonicalSite_val]
  rcases key with ⟨site, hactive⟩
  cases site with
  | idle => exact False.elim (hactive rfl)
  | first ownType => rfl
  | second ownType ownAction result => rfl

/-- Each raw action is exactly one canonical legal action at the complete AOH. -/
def keyChoiceEquiv (who : Player) (key : ActiveKey) :
    Choice key.1 ≃ (model fullPrior).Choice who (decodeInfo key.1) := by
  rcases key with ⟨site, hactive⟩
  cases site with
  | idle => exact False.elim (hactive rfl)
  | first ownType => exact activeChoiceEquiv who (.first ownType) hactive
  | second ownType ownAction result =>
      exact activeChoiceEquiv who (.second ownType ownAction result) hactive

end GameTheory.ReBeL.Rational.HiddenTypes.Canonical
