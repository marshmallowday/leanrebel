/-
# The mass discarded between a saved public PBS and a live child

The actual saved MODEL posterior remains public-only even when terminal status
is not observable. A factual child discards the stopped part of that same law.
This file accounts for the difference without altering either solver input.
-/

import GameTheory.Analysis.ReBeL.CFRDStoredChild
import GameTheory.Math.Probability.FinDistConditioningError

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)

/-- Propagating the actual stored initial law produces the public posterior,
without assuming that termination is visible or that the public fiber is live. -/
theorem carriedBeliefUpdate_eq_publicCut
    {past : List M.PublicSignal}
    (prior : PublicBelief (fullInformation M).toInfoSignals past)
    (initial : prior.law = FinDist.pure E.initHistory)
    (chosen trunk : Profile (fullInformation M).behavioralSignature)
    (cut : Nat) (obs : List M.PublicSignal)
    (prefixLaw : (fullInformation M).runBehavioral chosen cut =
      (fullInformation M).runBehavioral trunk cut)
    (possible : PublicBelief.Possible (S := (fullInformation M).toInfoSignals)
      ((fullInformation M).runBehavioral trunk cut) obs) :
    carriedBeliefUpdate (fullInformation M) (some prior) chosen cut obs =
      some (PublicBelief.condition (S := (fullInformation M).toInfoSignals)
        ((fullInformation M).runBehavioral trunk cut) obs
        possible) := by
  classical
  have law : PublicBelief.continuationLaw (fullInformation M) chosen cut prior =
      (fullInformation M).runBehavioral trunk cut := by
    dsimp only [PublicBelief.continuationLaw]
    rw [initial, FinDist.pure_bind]
    exact prefixLaw
  dsimp only [carriedBeliefUpdate, Option.bind]
  rw [law, PublicBelief.condition?, dif_pos possible]

/-- The explicit error is the stopped mass on this observation divided by
its public reach. Public positivity alone does not make that ratio small. -/
theorem cfrDFactualChild_public_error
    (trunk : Profile (fullInformation M).behavioralSignature) (cut remaining : Nat)
    (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs)
    (value : E.History → ℝ) (bound : ℝ) (bounded : ∀ h, |value h| ≤ bound) :
    |(PublicBelief.condition (S := (fullInformation M).toInfoSignals)
      ((fullInformation M).runBehavioral trunk cut) obs
        (cfrDFactualChildPossible_public M trunk cut remaining obs possible)).law.expect value -
      (cfrDFactualChildBelief M trunk cut remaining obs possible).law.expect value| ≤
      2 * bound *
        (((fullInformation M).runBehavioral trunk cut).probOf
          {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs ∧
            cfrDCutLive remaining h ≠ true} /
          ((fullInformation M).runBehavioral trunk cut).probOf
            {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs}) := by
  classical
  have publicPossible := cfrDFactualChildPossible_public M trunk cut remaining obs possible
  have estimate := FinDist.abs_condOn_expect_sub_le_discarded
    ((fullInformation M).runBehavioral trunk cut)
    {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs}
    {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs ∧
      cfrDCutLive remaining h = true}
    publicPossible possible (fun _ member => member.1.1) value bound (fun h _ => bounded h)
  have discarded :
      {h : E.History | publicTrace (fullInformation M).toInfoSignals h.trace = obs} ∩
        {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs ∧
          cfrDCutLive remaining h = true}ᶜ =
      {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs ∧
        cfrDCutLive remaining h ≠ true} := by
    ext h
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff]
    tauto
  rw [discarded] at estimate
  exact estimate

/-- Publicly observable termination recovers the exact earlier result:
a possible live query has zero discarded stopped mass. -/
theorem cfrDFactualChild_stoppedMass_eq_zero
    (observable : PubliclyObservableTermination M)
    (trunk : Profile (fullInformation M).behavioralSignature) (cut remaining : Nat)
    (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs) :
    ((fullInformation M).runBehavioral trunk cut).probOf
      {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs ∧
        cfrDCutLive remaining h ≠ true} = 0 := by
  classical
  rw [← FinDist.expect_indicator_eq_probOf]
  calc
    _ = ((fullInformation M).runBehavioral trunk cut).expect (fun _ => (0 : ℝ)) := by
      apply FinDist.expect_congr
      intro h reached
      apply if_neg
      intro stopped
      exact stopped.2
        (cfrDFactualChild_liveFiber M observable trunk cut remaining obs possible h
          reached stopped.1)
    _ = 0 := FinDist.expect_const _ _

/-- The factual child removes exactly the stopped atoms of the saved public
law. Actual hidden-history support is still required; public reach is not enough. -/
theorem cfrDFactualChild_public_support
    (trunk : Profile (fullInformation M).behavioralSignature) (cut remaining : Nat)
    (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs) (history : E.History) :
    history ∈ (cfrDFactualChildBelief M trunk cut remaining obs possible).law.support ↔
      history ∈ (PublicBelief.condition (S := (fullInformation M).toInfoSignals)
        ((fullInformation M).runBehavioral trunk cut) obs
        (cfrDFactualChildPossible_public M trunk cut remaining obs possible)).law.support ∧
      cfrDCutLive remaining history = true := by
  constructor
  · intro reached
    have member := FinDist.support_condOn
      ((fullInformation M).runBehavioral trunk cut)
      {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs ∧
        cfrDCutLive remaining h = true} possible reached
    exact ⟨FinDist.mem_support_condOn ((fullInformation M).runBehavioral trunk cut)
      {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs}
      (cfrDFactualChildPossible_public M trunk cut remaining obs possible)
      member.1.1 member.2, member.1.2⟩
  · rintro ⟨reached, live⟩
    have member := FinDist.support_condOn ((fullInformation M).runBehavioral trunk cut)
      {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs}
      (cfrDFactualChildPossible_public M trunk cut remaining obs possible) reached
    exact FinDist.mem_support_condOn ((fullInformation M).runBehavioral trunk cut)
      {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs ∧
        cfrDCutLive remaining h = true} possible ⟨member.1, live⟩ member.2

/-- Once the exact same continuation kernel is fixed, discarded mass controls
its full future value. This does not compare policies solved on different PBSs. -/
theorem cfrDFactualChild_public_continuation_error {Outcome : Type*}
    (trunk : Profile (fullInformation M).behavioralSignature) (cut remaining : Nat)
    (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs)
    (continuation : E.History → FinDist Outcome) (value : Outcome → ℝ)
    (bound : ℝ) (bounded : ∀ outcome, |value outcome| ≤ bound) :
    |((PublicBelief.condition (S := (fullInformation M).toInfoSignals)
      ((fullInformation M).runBehavioral trunk cut) obs
        (cfrDFactualChildPossible_public M trunk cut remaining obs possible)).law.bind
          continuation).expect value -
      ((cfrDFactualChildBelief M trunk cut remaining obs possible).law.bind
        continuation).expect value| ≤
      2 * bound *
        (((fullInformation M).runBehavioral trunk cut).probOf
          {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs ∧
            cfrDCutLive remaining h ≠ true} /
          ((fullInformation M).runBehavioral trunk cut).probOf
            {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs}) := by
  rw [FinDist.expect_bind, FinDist.expect_bind]
  exact cfrDFactualChild_public_error M trunk cut remaining obs possible
    (fun h => (continuation h).expect value) bound
    (fun h => FinDist.abs_expect_le_of_abs_bound _ value (fun x _ => bounded x))

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]
variable [∀ who, DecidableEq ((fullInformation M).InfoState who)]

/-- The actual composed parent saves the unfiltered public posterior.
This remains valid at publicly mixed live/terminal frontiers. -/
theorem cfrDComposedRound_storedPublic {K : Type*}
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (loss : ℝ) (solve : PBSChildSolve M)
    (noise : CFRDPredictionNoise M) (round : Nat)
    (state : PrivateIterationState (fullInformation M) K)
    (prior : PublicBelief (fullInformation M).toInfoSignals
      (publicTrace (fullInformation M).toInfoSignals state.history.trace))
    (stored : state.belief = some prior) (initial : prior.law = FinDist.pure E.initHistory)
    (history : E.History)
    (possible : PublicBelief.Possible (S := (fullInformation M).toInfoSignals)
      ((fullInformation M).runBehavioral
        (cfrDComposedTrunk M fallback payoff cut remaining loss solve noise round) cut)
      (publicTrace (fullInformation M).toInfoSignals history.trace)) :
    (cfrDComposedNextState M fallback payoff cut remaining loss solve noise round
      state history).belief =
    some (PublicBelief.condition (S := (fullInformation M).toInfoSignals)
      ((fullInformation M).runBehavioral
        (cfrDComposedTrunk M fallback payoff cut remaining loss solve noise round) cut)
      (publicTrace (fullInformation M).toInfoSignals history.trace) possible) := by
  simp only [cfrDComposedNextState, resolvedNextState, stored]
  exact carriedBeliefUpdate_eq_publicCut M prior initial _ _ cut _
    (cfrDComposedRound_prefixLaw M fallback payoff cut remaining loss solve noise round) possible

/-- The same played parent supplies both the saved PBS and the quantitative
live-child comparison. The continuation may include stage plus late fuel and
a private draw retained for that entire horizon. -/
theorem cfrDComposedRound_storedPublic_continuation_error {K Outcome : Type*}
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
      cut remaining (publicTrace (fullInformation M).toInfoSignals history.trace))
    (continuation : E.History → FinDist Outcome) (value : Outcome → ℝ)
    (bound : ℝ) (bounded : ∀ outcome, |value outcome| ≤ bound) :
    let trunk : Profile (fullInformation M).behavioralSignature :=
      cfrDComposedTrunk M fallback payoff cut remaining loss solve noise round
    let obs := publicTrace (fullInformation M).toInfoSignals history.trace
    let posterior := PublicBelief.condition (S := (fullInformation M).toInfoSignals)
      ((fullInformation M).runBehavioral trunk cut) obs
      (cfrDFactualChildPossible_public M trunk cut remaining obs possible)
    let child := cfrDFactualChildBelief M trunk cut remaining obs possible
    (cfrDComposedNextState M fallback payoff cut remaining loss solve noise round
      state history).belief = some posterior ∧
      |(posterior.law.bind continuation).expect value -
        (child.law.bind continuation).expect value| ≤
      2 * bound * (((fullInformation M).runBehavioral trunk cut).probOf
        {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs ∧
          cfrDCutLive remaining h ≠ true} /
        ((fullInformation M).runBehavioral trunk cut).probOf
          {h | publicTrace (fullInformation M).toInfoSignals h.trace = obs}) := by
  intro trunk obs posterior child
  constructor
  · exact cfrDComposedRound_storedPublic M fallback payoff cut remaining loss solve noise round
      state prior stored initial history
      (cfrDFactualChildPossible_public M trunk cut remaining obs possible)
  · exact cfrDFactualChild_public_continuation_error M trunk cut remaining obs possible
      continuation value bound bounded

end GameTheory.ReBeL
