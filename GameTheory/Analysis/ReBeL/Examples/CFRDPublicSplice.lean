/-
# Public-state splicing controls with live hidden-type continuations

Different public cut results select different actual second-round actions.
Private types do not change the table selector. Later public signals must not
replace the cut prefix: the deliberately wrong latest-state selector disagrees.
-/

import GameTheory.Analysis.ReBeL.CFRDReferenceSlice
import GameTheory.Analysis.ReBeL.Examples.CFRDZeroReachControl

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

/-- An entire public state, not just a private type, can be absent from factual
play while a unilateral reference legitimately queries it. -/
theorem publicSplice_unvisited_public :
    publicTrace (model fullPrior).toInfoSignals zeroControlHistory.trace ∉
      (((model fullPrior).runBehavioral (carriedBitProfile false) 2).map
        (fun h => publicTrace (model fullPrior).toInfoSignals h.trace)).support := by
  intro sampled
  rw [FinDist.support_map] at sampled
  obtain ⟨history, reached, same⟩ := sampled
  obtain ⟨row, rfl⟩ := decode_surjective history
  have first := cfrD_run_support_ownReach (model fullPrior) (carriedBitProfile false)
    2 (decode row) reached 0
  have second := cfrD_run_support_ownReach (model fullPrior) (carriedBitProfile false)
    2 (decode row) reached 1
  cases row with
  | initial => cases same
  | drawn x y => cases same
  | second x y a b =>
      by_cases ha : a = false
      · subst a
        by_cases hb : b = false
        · subst b
          cases same
        · exact second (by simp [zeroControl_own_reach,
            GameTheory.ReBeL.Rational.HiddenTypes.own, hb])
      · exact first (by simp [zeroControl_own_reach,
          GameTheory.ReBeL.Rational.HiddenTypes.own, ha])
  | finished x y a b c d => cases same

/-- Finite legal menus for the unilateral-reference boundary control. -/
local instance publicSpliceChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- The same unvisited public state has an actual reference-supported history;
requiring a factual posterior at every reference query would lose this case. -/
theorem publicSplice_unvisited_reference :
    publicTrace (model fullPrior).toInfoSignals zeroControlHistory.trace ∈
      ((unilateralReferenceLaw (model fullPrior) (carriedBitProfile false)
          cfrFallback 0 2).map
        (fun h => publicTrace (model fullPrior).toInfoSignals h.trace)).support := by
  rw [FinDist.support_map]
  exact ⟨zeroControlHistory, zeroControl_reference_supported, rfl⟩

/-- Finite canonical histories for construction of the actual typed query table. -/
local instance publicSpliceHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- The unvisited public-state reference query obtains an actual typed table
entry and exactly its original joint conditional, without any kernel certificate. -/
theorem publicSplice_constructed_reference_query :
    ∃ (observations : List Phase)
      (root type : PublicRootType (reducedModel fullPrior) observations 0),
      cfrDReferenceTable (reducedModel fullPrior) (carriedBitProfile false) cfrFallback 2 1
          observations 0 =
        some ⟨PublicRootType (reducedModel fullPrior) observations 0,
          cfrDReferenceSlice (reducedModel fullPrior) (carriedBitProfile false)
            cfrFallback 2 1 root⟩ ∧
      type.val = (model fullPrior).infoOf 0 zeroControlHistory.trace ∧
      ((cfrDReferenceSlice (reducedModel fullPrior) (carriedBitProfile false)
          cfrFallback 2 1 root).kernel type).law =
        (unilateralReferenceLaw (model fullPrior) (carriedBitProfile false)
          cfrFallback 0 2).condOnFibre
          (fun h => ((model fullPrior).infoOf 0 h.trace, cfrDCutLive 1 h))
          ((model fullPrior).infoOf 0 zeroControlHistory.trace, true) := by
  apply cfrDReferenceTable_query (reducedModel fullPrior)
  rw [FinDist.support_map]
  refine ⟨zeroControlHistory, zeroControl_reference_supported, ?_⟩
  apply Prod.ext
  · rfl
  · rw [cfrDCutLive, decide_eq_true_eq]
    exact ⟨by decide, fun impossible => impossible⟩

end GameTheory.ReBeL.Examples.HiddenTypes
