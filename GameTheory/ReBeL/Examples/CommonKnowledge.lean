/-
# Public observations versus common knowledge (Section 3, footnote 4)

This positive/negative control uses the same actual chance histories as the
paper's dice example. Every player privately receives the same complete roll,
while the public signal is constant. The observation maps are fixed and known.
The common-knowledge indistinguishability component is then a singleton, but
the public-history fiber is not. No converse to publicTrace_eq_of_knowledge_chain
is assumed.
-/

import GameTheory.ReBeL.Examples.ObservedDice

noncomputable section

namespace GameTheory.ReBeL.Examples.CommonKnowledge

open GameTheory.Protocol ExecutionProtocol ObservedDice

/-- Everyone privately receives the complete roll; no roll is publicly emitted. -/
@[reducible]
def signals : InfoSignals protocol where
  PublicSignal := Unit
  PrivateSignal _ := Option Dice
  initialPublic := ()
  initialPrivate _ := none
  publicSignal _ := ()
  privateSignal _ event := match event.target with
    | .initial => none
    | .rolled dice => some dice
  InfoState _ := Unit
  initInfo _ _ _ := ()
  pushInfo _ _ _ _ _ := ()

/-- Each player identifies the actual complete history in this control game. -/
theorem info_injective (i : Player) :
    Function.Injective
      (fun history : protocol.History => (fullSignals signals).infoOf i history.trace) := by
  intro first second equal
  rcases history_cases first with rfl | ⟨firstDice, rfl⟩ <;>
    rcases history_cases second with rfl | ⟨secondDice, rfl⟩
  · rfl
  · cases equal
  · cases equal
  · change AOH.step (AOH.initial (none : Option Dice) ()) (none : Option Unit)
        (some firstDice) () =
      AOH.step (.initial none ()) none (some secondDice) () at equal
    exact congrArg draw (Option.some.inj (AOH.step.inj equal).2.2.1)

/-- The standard finite-chain characterization cannot connect different histories. -/
theorem knowledge_chain_eq (first second : protocol.History)
    (chain : Relation.ReflTransGen
      (fun h k : protocol.History => ∃ i, (fullSignals signals).infoOf i h.trace =
        (fullSignals signals).infoOf i k.trace) first second) : first = second := by
  induction chain with
  | refl => rfl
  | tail _ related ih =>
      obtain ⟨i, equal⟩ := related
      exact ih.trans (info_injective i equal)

/-- Two different rolls still emit the same public observation history. -/
theorem same_public :
    publicTrace signals (draw ((0, 3), (4, 5))).trace =
      publicTrace signals (draw ((1, 3), (4, 5))).trace := rfl

/-- Thus the public fiber is strictly coarser than the common-knowledge partition. -/
theorem not_same_knowledge_component :
    ¬ Relation.ReflTransGen
      (fun h k : protocol.History => ∃ i, (fullSignals signals).infoOf i h.trace =
        (fullSignals signals).infoOf i k.trace)
      (draw ((0, 3), (4, 5))) (draw ((1, 3), (4, 5))) := by
  intro chain
  have equal := knowledge_chain_eq _ _ chain
  have impossible : (0 : Face) = 1 :=
    congrArg (fun history : protocol.History => (hiddenParts history.state).1) equal
  exact (by decide : (0 : Face) ≠ 1) impossible

end GameTheory.ReBeL.Examples.CommonKnowledge
