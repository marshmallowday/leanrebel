/-
# Public-state splicing controls with live hidden-type continuations

Different public cut results select different actual second-round actions.
Private types do not change the table selector. Later public signals must not
replace the cut prefix: the deliberately wrong latest-state selector disagrees.
-/

import GameTheory.Analysis.ReBeL.CFRDPublicSplice
import GameTheory.Analysis.ReBeL.Examples.CFRDLiveControl

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- A public table chooses a bit from the first strategic round's public result. -/
def publicSpliceBit : List Phase → Bool
  | .second won :: _ => won
  | _ => false

/-- Each child is a complete legal policy, not a hidden-history action lookup. -/
def publicSpliceTable (observations : List Phase) :
    Profile (model fullPrior).behavioralSignature :=
  carriedBitProfile (publicSpliceBit observations)

/-- The actual public-splice constructor runs at the live depth-two cut. -/
def publicSpliceProfile : Profile (model fullPrior).behavioralSignature :=
  cfrDPublicContinuation (reducedModel fullPrior) 2 publicSpliceTable

/-- The first-round public result selects the real second-round legal draw;
all private type pairs and both players are quantified independently. -/
theorem publicSplice_second_law (x y a b : Bool) (who : Player) :
    liveSecondLaw publicSpliceProfile x y a b who = FinDist.pure (a == b) := by
  have selected : publicSpliceProfile who
      ((model fullPrior).infoOf who (decode (.second x y a b)).trace) =
      carriedBitProfile (a == b) who
        ((model fullPrior).infoOf who (decode (.second x y a b)).trace) := by
    exact cfrDPublicContinuation_eq_of_reaches (reducedModel fullPrior) 2 publicSpliceTable
      who (decode (.second x y a b)) (decode (.second x y a b)) rfl
      (.refl 0 (decode (.second x y a b)))
  unfold liveSecondLaw
  rw [selected]
  exact carriedBit_second_law (a == b) x y a b who

/-- Two different public roots actually cause different legal actions. -/
theorem publicSplice_two_roots :
    liveSecondLaw publicSpliceProfile false false false false 0 ≠
      liveSecondLaw publicSpliceProfile false false false true 0 := by
  rw [publicSplice_second_law, publicSplice_second_law]
  intro same
  have observed := congrArg
    (fun law : FinDist Bool => law.expect (fun b => if b then 1 else 0)) same
  norm_num [FinDist.expect_pure] at observed

/-- Full local information after one new public signal beyond the live cut. -/
def publicSpliceTerminalInfo : (model fullPrior).InfoState 0 :=
  (model fullPrior).infoOf 0 (decode (.finished false false false false true false)).trace

/-- Keeping only the latest public phase selects the wrong response after a
new signal. The remembered cut prefix still selects true; the latest phase does not. -/
theorem publicSplice_latest_selector_wrong :
    publicSpliceBit (publicSpliceTerminalInfo.prefixAt 2).publicHistory ≠
      publicSpliceBit publicSpliceTerminalInfo.publicHistory := by
  decide

/-- At the next public signal, the stored cut selector still equals the
original public result for every private history and every final action pair. -/
theorem publicSplice_retains_root (x y a b c d : Bool) (who : Player) :
    publicSpliceBit
        ((((model fullPrior).infoOf who
          (decode (.finished x y a b c d)).trace).prefixAt 2).publicHistory) = (a == b) := by
  rfl

/-- From each live cut, all unknown opposing policies see exactly the selected
child's complete continuation law, not just the same expected score. -/
theorem publicSplice_unknown_opponent
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (x y a b : Bool) (fuel : Nat) :
    (model fullPrior).runBehavioralFrom
        (Profile.update unknown who (publicSpliceProfile who)) fuel
        (decode (.second x y a b)) =
      (model fullPrior).runBehavioralFrom
        (Profile.update unknown who (carriedBitProfile (a == b) who)) fuel
        (decode (.second x y a b)) := by
  exact cfrDPublicContinuation_unilateral_runFrom (reducedModel fullPrior) 2
    publicSpliceTable unknown who (decode (.second x y a b)) rfl fuel

end GameTheory.ReBeL.Examples.HiddenTypes
