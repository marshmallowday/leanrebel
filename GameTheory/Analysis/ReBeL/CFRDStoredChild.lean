/-
# The stored model posterior and the parent's factual child

Public conditioning agrees with live-public conditioning when every supported
history on the observed fiber is live. This condition is derived from publicly
observable termination, rather than inferred from a single actual history.
The actual composed CFR-D round supplies the required model prefix law.
-/

import GameTheory.Analysis.ReBeL.PBSComposedDepth
import GameTheory.Analysis.ReBeL.CFRDResolveBelief
import GameTheory.Math.Probability.FinDistConditioning

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)

/-- Termination is observable from the entire public history. This is a
property to prove for a game, not an extra observation supplied to its solver. -/
def PubliclyObservableTermination : Prop :=
  ∀ first second : E.History,
    publicTrace M.toInfoSignals first.trace = publicTrace M.toInfoSignals second.trace →
      (E.terminal first.state ↔ E.terminal second.state)

-- The information-state universe changes under full AOH refinement, even
-- though its public observations do not. Relate the two traces explicitly.
private theorem storedChild_publicTrace_full {state : E.State} (trace : E.Trace state) :
    publicTrace (fullInformation M).toInfoSignals trace = publicTrace M.toInfoSignals trace := by
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih =>
      exact congrArg
        (fun observations => M.publicSignal ⟨_, joint, legal, _, realized⟩ :: observations) ih

private theorem storedChild_belief_ext {obs : List M.PublicSignal}
    (first second : PublicBelief (fullInformation M).toInfoSignals obs)
    (same : first.law = second.law) : first = second := by
  cases first
  cases second
  cases same
  rfl

/-- A possible live child gives public positivity, with the SAME law. -/
theorem cfrDFactualChildPossible_public
    (trunk : Profile (fullInformation M).behavioralSignature) (cut remaining : Nat)
    (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs) :
    PublicBelief.Possible (S := (fullInformation M).toInfoSignals)
      ((fullInformation M).runBehavioral trunk cut) obs := by
  obtain ⟨history, member, reached⟩ := possible
  exact ⟨history, member.1, reached⟩

/-- Public and live-public posterior equality is proved on the model support.
A terminal atom sharing the same observation would invalidate this premise. -/
theorem cfrDFactualChildBelief_eq_public
    (trunk : Profile (fullInformation M).behavioralSignature) (cut remaining : Nat)
    (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs)
    (liveFiber : ∀ h ∈ ((fullInformation M).runBehavioral trunk cut).support,
      publicTrace (fullInformation M).toInfoSignals h.trace = obs →
        cfrDCutLive remaining h = true) :
    PublicBelief.condition? (S := (fullInformation M).toInfoSignals)
      ((fullInformation M).runBehavioral trunk cut) obs =
      some (cfrDFactualChildBelief M trunk cut remaining obs possible) := by
  classical
  have publicPossible := cfrDFactualChildPossible_public M trunk cut remaining obs possible
  rw [PublicBelief.condition?, dif_pos publicPossible]
  apply congrArg some
  apply storedChild_belief_ext M
  dsimp only [PublicBelief.condition, cfrDFactualChildBelief]
  apply FinDist.condOn_eq_of_support_iff
  intro history reached
  exact ⟨fun equal => ⟨equal, liveFiber history reached equal⟩, fun both => both.1⟩

/-- Public termination makes liveness constant on a possible live child's
public fiber; zero remaining fuel has already been excluded by possibility. -/
theorem cfrDFactualChild_liveFiber
    (observable : PubliclyObservableTermination M)
    (trunk : Profile (fullInformation M).behavioralSignature) (cut remaining : Nat)
    (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs) :
    ∀ h ∈ ((fullInformation M).runBehavioral trunk cut).support,
      publicTrace (fullInformation M).toInfoSignals h.trace = obs →
        cfrDCutLive remaining h = true := by
  obtain ⟨first, member, _⟩ := possible
  have firstLive : remaining ≠ 0 ∧ ¬ E.terminal first.state := by
    simpa only [cfrDCutLive, decide_eq_true_eq] using member.2
  intro history _ same
  simp only [cfrDCutLive, decide_eq_true_eq]
  have original : publicTrace M.toInfoSignals history.trace =
      publicTrace M.toInfoSignals first.trace := by
    simpa only [storedChild_publicTrace_full] using same.trans member.1.symm
  exact ⟨firstLive.1, fun terminal =>
    firstLive.2 ((observable history first original).mp terminal)⟩

/-- Start from an actual stored initial law and propagate the chosen model.
Only a proved prefix-law equality is used; the actual opponent is irrelevant
to the Bayesian model update and is not substituted into it. -/
theorem carriedBeliefUpdate_eq_factualChild
    {past : List M.PublicSignal}
    (prior : PublicBelief (fullInformation M).toInfoSignals past)
    (initial : prior.law = FinDist.pure E.initHistory)
    (chosen trunk : Profile (fullInformation M).behavioralSignature)
    (cut remaining : Nat) (obs : List M.PublicSignal)
    (prefixLaw : (fullInformation M).runBehavioral chosen cut =
      (fullInformation M).runBehavioral trunk cut)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs)
    (liveFiber : ∀ h ∈ ((fullInformation M).runBehavioral trunk cut).support,
      publicTrace (fullInformation M).toInfoSignals h.trace = obs →
        cfrDCutLive remaining h = true) :
    carriedBeliefUpdate (fullInformation M) (some prior) chosen cut obs =
      some (cfrDFactualChildBelief M trunk cut remaining obs possible) := by
  have law : PublicBelief.continuationLaw (fullInformation M) chosen cut prior =
      (fullInformation M).runBehavioral trunk cut := by
    dsimp only [PublicBelief.continuationLaw]
    rw [initial, FinDist.pure_bind]
    exact prefixLaw
  dsimp only [carriedBeliefUpdate, Option.bind]
  rw [law]
  exact cfrDFactualChildBelief_eq_public M trunk cut remaining obs possible liveFiber

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]
variable [∀ who, DecidableEq ((fullInformation M).InfoState who)]

/-- The exact trunk state used to construct a composed oracle's child queries.
Round, numerical perturbation, child function and budget all remain fixed. -/
def cfrDComposedTrunk (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve M) (noise : CFRDPredictionNoise M) (round : Nat) :
    Profile (fullInformation M).behavioralSignature :=
  cfrProfile (fullInformation M) (cfrDInformationFallback M fallback)
    (cfrDState (fullInformation M)
      (cfrDDepthTrunk (fullInformation M) (fullObservationClock M) cut)
      (cfrDInformationFallback M fallback)
      (cfrDDepthOracle (fullInformation M) (fullObservationClock M)
        (cfrDInformationFallback M fallback) payoff cut remaining
        (cfrDComposedOracle M fallback payoff cut remaining loss solve noise)) round)

/-- The actual played round has the same model prefix as its own child-query
trunk. This does not replace the selected round by an average policy. -/
theorem cfrDComposedRound_prefixLaw (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve M) (noise : CFRDPredictionNoise M) (round : Nat) :
    (fullInformation M).runBehavioral
      (cfrDDepthPlay (fullInformation M) (fullObservationClock M)
        (cfrDInformationFallback M fallback) payoff cut remaining
        (cfrDComposedOracle M fallback payoff cut remaining loss solve noise) round) cut =
    (fullInformation M).runBehavioral
      (cfrDComposedTrunk M fallback payoff cut remaining loss solve noise round) cut := by
  apply runBehavioral_eq_of_before_depth (fullInformation M) (fullObservationClock M)
  intro who info before
  simp only [cfrDDepthPlay_eq, cfrDDepthProfile, cfrDDepthTrunk, decide_eq_true_eq,
    if_pos before, cfrDComposedTrunk]

/-- Native post-round state: the selected round profile and its model PBS are
kept together. This abbreviates the existing execution update without changing it. -/
def cfrDComposedNextState {K : Type*}
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (loss : ℝ) (solve : PBSChildSolve M)
    (noise : CFRDPredictionNoise M) (round : Nat)
    (state : PrivateIterationState (fullInformation M) K) (history : E.History) :
    PrivateIterationState (fullInformation M)
      (K × Profile (fullInformation M).behavioralSignature) :=
  resolvedNextState (fullInformation M) state
    (cfrDDepthPlay (fullInformation M) (fullObservationClock M)
      (cfrDInformationFallback M fallback) payoff cut remaining
      (cfrDComposedOracle M fallback payoff cut remaining loss solve noise) round) cut history

/-- The native saved posterior of a played composed round is exactly its
factual child, under publicly observable termination. The initial PBS premise
is valid for this protocol's own initial/rooted run, not an arbitrary reset. -/
theorem cfrDComposedRound_storedChild {K : Type*}
    (observable : PubliclyObservableTermination M)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (loss : ℝ) (solve : PBSChildSolve M)
    (noise : CFRDPredictionNoise M) (round : Nat)
    (state : PrivateIterationState (fullInformation M) K)
    (prior : PublicBelief (fullInformation M).toInfoSignals
      (publicTrace (fullInformation M).toInfoSignals state.history.trace))
    (stored : state.belief = some prior) (initial : prior.law = FinDist.pure E.initHistory)
    (history : E.History)
    (possible : CFRDFactualChildPossible M
      (cfrDComposedTrunk M fallback payoff cut remaining loss solve noise round)
      cut remaining (publicTrace (fullInformation M).toInfoSignals history.trace)) :
    (resolvedNextState (fullInformation M) state
      (cfrDDepthPlay (fullInformation M) (fullObservationClock M)
        (cfrDInformationFallback M fallback) payoff cut remaining
        (cfrDComposedOracle M fallback payoff cut remaining loss solve noise) round)
      cut history).belief =
    some (cfrDFactualChildBelief M
      (cfrDComposedTrunk M fallback payoff cut remaining loss solve noise round)
      cut remaining (publicTrace (fullInformation M).toInfoSignals history.trace) possible) := by
  simp only [resolvedNextState, stored]
  exact carriedBeliefUpdate_eq_factualChild M prior initial _ _ cut remaining _
    (cfrDComposedRound_prefixLaw M fallback payoff cut remaining loss solve noise round)
    possible (cfrDFactualChild_liveFiber M observable _ cut remaining _ possible)

end GameTheory.ReBeL
