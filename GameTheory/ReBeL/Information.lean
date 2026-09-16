/-
# Full action-observation histories for ReBeL

ReBeL, Section 3 (published p. 3), uses full AOHs, not arbitrary compressed
`InfoState`s. This module refines the existing information boundary without
introducing another execution or policy semantics. AOHs contain only initial
observations, the player's own actions, and subsequent private/public signals.
The newest observation is at the outermost constructor; public lists use the
same newest-first convention. Neither representation contains a world state.
-/

import GameTheory.Protocol.Information

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

/-- A full local action-observation history, with no hidden-state argument. -/
inductive AOH (Action : Type ua) (Private : Type uq) (Public : Type up)
  | initial (privateObservation : Private) (publicObservation : Public)
  | step (prior : AOH Action Private Public) (ownAction : Option Action)
      (privateObservation : Private) (publicObservation : Public)

namespace AOH

variable {Action : Type ua} {Private : Type uq} {Public : Type up}

/-- The entire public observation sequence, including the initial observation.
Lists are newest first, so a transition adds exactly one observation. -/
def publicHistory : AOH Action Private Public → List Public
  | .initial _ observation => [observation]
  | .step prior _ _ observation => observation :: prior.publicHistory

/-- The number of realized transitions, not the number of active choices. -/
def length : AOH Action Private Public → Nat
  | .initial _ _ => 0
  | .step prior _ _ _ => prior.length + 1

/-- Reconstruct the canonical own-play record from a full AOH. -/
def ownPlay : AOH Action Private Public → List (AOH Action Private Public × Action)
  | .initial _ _ => []
  | .step prior none _ _ => prior.ownPlay
  | .step prior (some action) _ _ => (prior, action) :: prior.ownPlay

@[simp]
theorem publicHistory_length (aoh : AOH Action Private Public) :
    aoh.publicHistory.length = aoh.length + 1 := by
  induction aoh with
  | initial => rfl
  | step prior _ _ _ ih => simpa [publicHistory, length] using congrArg Nat.succ ih

end AOH

variable (S : InfoSignals E)

/-- Replay observations through an existing (possibly compressed) information
state update. This is a function of local observations alone. -/
def reduceAOH (i : ι) :
    AOH (E.Action i) (S.PrivateSignal i) S.PublicSignal → S.InfoState i
  | .initial privateObservation publicObservation =>
      S.initInfo i privateObservation publicObservation
  | .step prior action privateObservation publicObservation =>
      S.pushInfo i (reduceAOH S i prior) action privateObservation publicObservation

/-- Retain all observations and own actions rather than compressing them. -/
@[reducible]
def fullSignals : InfoSignals E where
  PublicSignal := S.PublicSignal
  PrivateSignal := S.PrivateSignal
  initialPublic := S.initialPublic
  initialPrivate := S.initialPrivate
  publicSignal := S.publicSignal
  privateSignal := S.privateSignal
  InfoState i := AOH (E.Action i) (S.PrivateSignal i) S.PublicSignal
  initInfo _ := AOH.initial
  pushInfo _ := AOH.step

/-- Public observations accumulated over the actual Protocol trace. -/
def publicTrace : {state : E.State} → E.Trace state → List S.PublicSignal
  | _, .start => [S.initialPublic]
  | _, .extend prior joint legal realized =>
      S.publicSignal ⟨_, joint, legal, _, realized⟩ :: publicTrace S prior

/-- Full histories refine, rather than identify themselves with, the original
compressed information state. -/
@[simp]
theorem reduceAOH_infoOf (i : ι) {state : E.State} (trace : E.Trace state) :
    reduceAOH S i ((fullSignals S).infoOf i trace) = S.infoOf i trace := by
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih =>
      simpa only [InfoSignals.infoOf, fullSignals, reduceAOH] using
        congrArg (fun info => S.pushInfo i info (joint i)
          (S.privateSignal i ⟨_, joint, legal, _, realized⟩)
          (S.publicSignal ⟨_, joint, legal, _, realized⟩)) ih

/-- Every player reconstructs exactly the same public trace from its AOH. -/
@[simp]
theorem publicHistory_infoOf (i : ι) {state : E.State} (trace : E.Trace state) :
    ((fullSignals S).infoOf i trace).publicHistory = publicTrace S trace := by
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih =>
      simp only [InfoSignals.infoOf, fullSignals, AOH.publicHistory, publicTrace, ih]

@[simp]
theorem length_infoOf (i : ι) {state : E.State} (trace : E.Trace state) :
    ((fullSignals S).infoOf i trace).length = trace.length := by
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih =>
      simp only [InfoSignals.infoOf, fullSignals, AOH.length, Trace.length, ih]

/-- The full AOH remembers the actual canonical own-play record. -/
theorem ownPlay_infoOf (i : ι) {state : E.State} (trace : E.Trace state) :
    ((fullSignals S).infoOf i trace).ownPlay = (fullSignals S).ownPlay i trace := by
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih =>
      change (AOH.step ((fullSignals S).infoOf i prior) (joint i) _ _).ownPlay = _
      cases ha : joint i <;>
        simp only [AOH.ownPlay, InfoSignals.ownPlay, ha, ih]

/-- Perfect recall is proved, not supplied as an axiom or a data field. -/
theorem fullSignals_perfectRecall : (fullSignals S).PerfectRecall := by
  intro i first second traceFirst traceSecond hinfo
  rw [← ownPlay_infoOf S i traceFirst, ← ownPlay_infoOf S i traceSecond]
  exact congrArg AOH.ownPlay hinfo

/-- Equality of local AOHs implies equality of public histories. -/
theorem publicTrace_eq_of_infoOf_eq (i : ι) {first second : E.State}
    (traceFirst : E.Trace first) (traceSecond : E.Trace second)
    (hinfo : (fullSignals S).infoOf i traceFirst =
      (fullSignals S).infoOf i traceSecond) :
    publicTrace S traceFirst = publicTrace S traceSecond := by
  rw [← publicHistory_infoOf S i traceFirst, ← publicHistory_infoOf S i traceSecond]
  exact congrArg AOH.publicHistory hinfo

/-- A public state is an observation sequence; it is not the physical state. -/
def PublicFiber (observations : List S.PublicSignal) :=
  {history : E.History // publicTrace S history.trace = observations}

/-- The individual information fiber is generally smaller than the public
fiber and does not by itself carry any posterior probability. -/
def InformationFiber (i : ι)
    (info : AOH (E.Action i) (S.PrivateSignal i) S.PublicSignal) :=
  {history : E.History // (fullSignals S).infoOf i history.trace = info}

/-- Forgetting the private information embeds an individual fiber into its
public fiber; it does not identify the two. -/
def informationFiberToPublic (i : ι)
    (info : AOH (E.Action i) (S.PrivateSignal i) S.PublicSignal)
    (history : InformationFiber S i info) : PublicFiber S info.publicHistory :=
  ⟨history.1, by rw [← publicHistory_infoOf S i history.1.trace, history.2]⟩

/-- Reuse an adequate information-local menu on the refined AOH carrier. -/
@[reducible]
def fullInformation (M : InformationModel E) : InformationModel E where
  toInfoSignals := fullSignals M.toInfoSignals
  menu i info := M.menu i (reduceAOH M.toInfoSignals i info)
  menu_adequate := by
    intro i state trace choice
    change choice ∈ M.menu i
      (reduceAOH M.toInfoSignals i ((fullSignals M.toInfoSignals).infoOf i trace)) ↔ _
    rw [reduceAOH_infoOf]
    exact M.menu_adequate i trace choice

/-- Refining the memory keeps every legal action, including off-path choices. -/
theorem fullInformation_legalOptions (M : InformationModel E) (i : ι)
    {state : E.State} (trace : E.Trace state) (choice : Option (E.Action i)) :
    choice ∈ (fullInformation M).menu i ((fullInformation M).infoOf i trace) ↔
      LegalOption E state i choice :=
  (fullInformation M).menu_adequate i trace choice

/-- Public information remains fixed along any finite chain of individual
indistinguishability. This is the common-knowledge reachability criterion;
no converse claiming that public observations exhaust common knowledge is used. -/
theorem publicTrace_eq_of_knowledge_chain
    (history other : E.History)
    (chain : Relation.ReflTransGen
      (fun h k : E.History => ∃ i, (fullSignals S).infoOf i h.trace =
        (fullSignals S).infoOf i k.trace) history other) :
    publicTrace S history.trace = publicTrace S other.trace := by
  induction chain with
  | refl => rfl
  | tail _ related ih =>
      obtain ⟨i, hi⟩ := related
      exact ih.trans (publicTrace_eq_of_infoOf_eq S i _ _ hi)

end GameTheory.ReBeL
