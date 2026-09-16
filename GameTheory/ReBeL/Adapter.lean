/-
# Observation-preserving adapters

Full AOH policies can implement an existing observation-local policy without
changing the law of play. The finite decision domain is the *reachable image*
of the history space: the unrestricted syntactic AOH carrier need not be finite.
-/

import GameTheory.ReBeL.Information
import GameTheory.ReBeL.Finite

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol

universe uι us ua

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

/-- A state view is an optional proven characterization of the observations.
It is not an extra argument available to a policy. -/
theorem infoOf_eq_view (S : InfoSignals E) (view : (i : ι) → E.State → S.InfoState i)
    (initial : ∀ i, S.initInfo i (S.initialPrivate i) S.initialPublic = view i E.init)
    (update : ∀ (event : E.StepEvent) (i : ι),
      S.pushInfo i (view i event.source) (event.joint i)
        (S.privateSignal i event) (S.publicSignal event) = view i event.target)
    (i : ι) {state : E.State} (trace : E.Trace state) :
    S.infoOf i trace = view i state := by
  induction trace with
  | start => exact initial i
  | extend prior joint legal realized ih =>
      change S.pushInfo i (S.infoOf i prior) (joint i)
        (S.privateSignal i ⟨_, joint, legal, _, realized⟩)
        (S.publicSignal ⟨_, joint, legal, _, realized⟩) = _
      rw [ih]
      exact update ⟨_, joint, legal, _, realized⟩ i

/-- Implement a compressed observation-local policy on the full AOH carrier.
No information is invented by this map. -/
def liftPolicy (M : InformationModel E) (i : ι) (policy : M.Policy i) :
    (fullInformation M).Policy i :=
  fun info => policy (reduceAOH M.toInfoSignals i info)

/-- The full-history adapter preserves the action at every realized history,
including histories with zero probability under a selected policy profile. -/
@[simp]
theorem liftPolicy_act_infoOf (M : InformationModel E) (i : ι) (policy : M.Policy i)
    {state : E.State} (trace : E.Trace state) :
    (liftPolicy M i policy).act ((fullInformation M).infoOf i trace) =
      policy.act (M.infoOf i trace) := by
  change (policy (reduceAOH M.toInfoSignals i
    ((fullSignals M.toInfoSignals).infoOf i trace))).1 = _
  rw [reduceAOH_infoOf]
  rfl

/-- The chooser, including its legality certificate, is unchanged. -/
theorem liftPolicy_historyChooser (M : InformationModel E)
    (profile : (i : ι) → M.Policy i) (history : E.History)
    (nonterminal : ¬ E.terminal history.state) :
    (fullInformation M).historyChooser (fun i => liftPolicy M i (profile i)) history nonterminal =
      M.historyChooser profile history nonterminal := by
  apply Subtype.ext
  funext i
  exact liftPolicy_act_infoOf M i (profile i) history.trace

/-- Full histories refine memory without defining a second runner. -/
theorem liftPolicy_runFrom (M : InformationModel E) (profile : (i : ι) → M.Policy i)
    (fuel : Nat) (history : E.History) :
    (fullInformation M).runFrom (fun i => liftPolicy M i (profile i)) fuel history =
      M.runFrom profile fuel history := by
  apply ExecutionProtocol.runHistoryFor_congr
  intro h hterm
  exact liftPolicy_historyChooser M profile h hterm

/-- In particular, the initial law is preserved exactly, not merely up to its
expected payoff under one selected utility function. -/
theorem liftPolicy_run (M : InformationModel E) (profile : (i : ι) → M.Policy i)
    (fuel : Nat) :
    (fullInformation M).run (fun i => liftPolicy M i (profile i)) fuel = M.run profile fuel :=
  liftPolicy_runFrom M profile fuel E.initHistory

/-- The actual information domain is the image of all legal realized histories.
This includes off-policy histories; it is not the support of one profile's run. -/
def ObservedInfo (S : InfoSignals E) (i : ι) :=
  {info : S.InfoState i // ∃ history : E.History, S.infoOf i history.trace = info}

/-- History enumeration induces an explicit enumeration of the reachable
information domain, without asserting that arbitrary synthetic AOHs are finite. -/
@[reducible]
def observedInfoFintype [Fintype E.History] (S : InfoSignals E) (i : ι) :
    Fintype (ObservedInfo S i) := by
  classical
  exact Fintype.ofSurjective
    (fun history : E.History =>
      (⟨S.infoOf i history.trace, ⟨history, rfl⟩⟩ : ObservedInfo S i))
    (by
      intro info
      obtain ⟨history, hinfo⟩ := info.2
      exact ⟨history, Subtype.ext hinfo⟩)

/-- Public fibers inherit finite enumeration from histories. -/
@[reducible]
def publicFiberFintype [Fintype E.History] (S : InfoSignals E)
    (observations : List S.PublicSignal) : Fintype (PublicFiber S observations) := by
  classical
  exact Subtype.fintype _

/-- Individual information fibers are finite for the same reason, not because
a state's predecessor is unique. -/
@[reducible]
def informationFiberFintype [Fintype E.History] (S : InfoSignals E) (i : ι)
    (info : AOH (E.Action i) (S.PrivateSignal i) S.PublicSignal) :
    Fintype (InformationFiber S i info) := by
  classical
  exact Subtype.fintype _

end GameTheory.ReBeL
