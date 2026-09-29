/-
# Decoding a child posterior inside an existing PBS-rooted protocol

A noninitial rooted public observation carries the complete original public
history. Decode that actual joint posterior without resetting it to the outer
root law. Continuation fuel starts after the administrative draw, so no extra
step is inserted. Every behavioral deviation is preserved.
-/

import GameTheory.Analysis.ReBeL.PBSInformationSampling

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable (roots : FinDist E.History)

/-- Total analyst readout; the administrative fallback is unreachable in
the supported noninitial child beliefs used below. Policies never read it. -/
def pbsRootChildRead (history : (pbsRootProtocol roots).History) : E.History :=
  history.state.getD E.initHistory

/-- The current public snapshot certifies an original history and its public
index. No hidden-history support or independence premise is inferred. -/
theorem pbsRootChildRead_public
    (observations : List M.PublicSignal)
    (past : List (Option (List M.PublicSignal)))
    (history : (pbsRootProtocol roots).History)
    (observed : publicTrace (pbsRootFullInformation M roots).toInfoSignals
      history.trace = some observations :: past) :
    history.state = some (pbsRootChildRead roots history) ∧
      publicTrace (fullInformation.{0, u, u, u, u, u} M).toInfoSignals
        (pbsRootChildRead roots history).trace = observations := by
  rcases history with ⟨state, trace⟩
  cases trace with
  | start =>
      have impossible : (none : Option (List M.PublicSignal)) = some observations :=
        (List.cons.inj observed).1
      cases impossible
  | @extend source _ prior joint legal realized =>
      cases state with
      | none =>
          have impossible : (none : Option (List M.PublicSignal)) = some observations :=
            (List.cons.inj observed).1
          cases impossible
      | some original =>
          exact ⟨rfl, Option.some.inj (List.cons.inj observed).1⟩

/-- Push forward the actual child joint law. Its saved posterior is not
replaced by the outer roots or by an unknown opponent's factual posterior. -/
def pbsRootChildBelief
    {observations : List M.PublicSignal} {past : List (Option (List M.PublicSignal))}
    (child : PublicBelief (pbsRootFullInformation M roots).toInfoSignals
      (some observations :: past)) :
    PublicBelief (fullInformation.{0, u, u, u, u, u} M).toInfoSignals observations where
  law := child.law.map (pbsRootChildRead roots)
  supported history reached := by
    rw [FinDist.support_map] at reached
    obtain ⟨source, supported, rfl⟩ := reached
    exact (pbsRootChildRead_public M roots observations past source
      (child.supported source supported)).2

/-- Decode an arbitrary newly computed rooted profile from an already
sampled history. The administrative chance step is not repeated. -/
theorem pbsRootDecodeProfile_from_some
    (cut : Nat) (rootDepth : ∀ history ∈ roots.support, history.trace.length = cut)
    (profile : Profile (pbsRootFullInformation M roots).behavioralSignature)
    (fuel : Nat) (original : E.History)
    (trace : (pbsRootProtocol roots).Trace (some original)) :
    ((pbsRootFullInformation M roots).runBehavioralFrom profile fuel
      ⟨some original, trace⟩).map History.state =
      ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom
        (pbsRootDecodeProfile M roots cut profile) fuel original).map some := by
  have same : (pbsRootFullInformation M roots).runBehavioralFrom profile fuel
      ⟨some original, trace⟩ =
      (pbsRootFullInformation M roots).runBehavioralFrom
        (pbsRootBehavioralFullProfile M roots (pbsRootDecodeProfile M roots cut profile))
        fuel ⟨some original, trace⟩ := by
    apply (pbsRootFullInformation M roots).runBehavioralFrom_congr
    intro later _ _ who
    exact (pbsRootDecodePolicy_agrees M roots cut rootDepth who (profile who) later.trace).symm
  rw [same]
  simpa only [runBehavioralFrom, pbsRoot_behavioralFullChooser, pbsRoot_behavioralChooser]
    using pbsRoot_runFrom_some roots
      ((fullInformation.{0, u, u, u, u, u} M).randomizedChooser
        (pbsRootDecodeProfile M roots cut profile)) fuel original trace

/-- Exact full continuation laws from the child posterior, for every fuel
including zero and terminal histories. The old public cut still decodes AOHs. -/
theorem pbsRootChild_continuation_law
    (cut : Nat) (rootDepth : ∀ history ∈ roots.support, history.trace.length = cut)
    {observations : List M.PublicSignal} {past : List (Option (List M.PublicSignal))}
    (child : PublicBelief (pbsRootFullInformation M roots).toInfoSignals
      (some observations :: past))
    (profile : Profile (pbsRootFullInformation M roots).behavioralSignature) (fuel : Nat) :
    (child.law.bind
      ((pbsRootFullInformation M roots).runBehavioralFrom profile fuel)).map History.state =
      ((pbsRootChildBelief M roots child).law.bind
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom
          (pbsRootDecodeProfile M roots cut profile) fuel)).map some := by
  simp only [pbsRootChildBelief, FinDist.map_bind, FinDist.bind_map]
  apply FinDist.bind_congr
  intro history supported
  have read := (pbsRootChildRead_public M roots observations past history
    (child.supported history supported)).1
  rcases history with ⟨state, trace⟩
  cases state with
  | none => cases read
  | some original =>
      exact pbsRootDecodeProfile_from_some M roots cut rootDepth profile fuel original trace

/-- All original-history observables, not just training payoffs, are preserved. -/
theorem pbsRootChild_continuation_expect
    (cut : Nat) (rootDepth : ∀ history ∈ roots.support, history.trace.length = cut)
    {observations : List M.PublicSignal} {past : List (Option (List M.PublicSignal))}
    (child : PublicBelief (pbsRootFullInformation M roots).toInfoSignals
      (some observations :: past))
    (profile : Profile (pbsRootFullInformation M roots).behavioralSignature)
    (fuel : Nat) (value : E.History → ℝ) :
    (child.law.bind ((pbsRootFullInformation M roots).runBehavioralFrom profile fuel)).expect
      (fun history => history.state.elim 0 value) =
      ((pbsRootChildBelief M roots child).law.bind
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom
          (pbsRootDecodeProfile M roots cut profile) fuel)).expect value := by
  have equal := congrArg (fun law : FinDist (Option E.History) =>
    law.expect (fun state => state.elim 0 value))
      (pbsRootChild_continuation_law M roots cut rootDepth child profile fuel)
  simpa only [FinDist.expect_map, Option.elim] using equal

/-- One player's rooted replacement is played against unchanged original
opponents. This identity is independent of any Nash or accuracy assumption. -/
theorem pbsRootChild_own_law
    (cut : Nat) (rootDepth : ∀ history ∈ roots.support, history.trace.length = cut)
    {observations : List M.PublicSignal} {past : List (Option (List M.PublicSignal))}
    (child : PublicBelief (pbsRootFullInformation M roots).toInfoSignals
      (some observations :: past))
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (who : Fin 2) (policy : (pbsRootFullInformation M roots).BehavioralPolicy who)
    (fuel : Nat) :
    (child.law.bind ((pbsRootFullInformation M roots).runBehavioralFrom
      (Profile.update (pbsRootBehavioralFullProfile M roots unknown) who policy) fuel)).map
        History.state =
      ((pbsRootChildBelief M roots child).law.bind
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom
          (Profile.update unknown who (pbsRootDecodePolicy M roots cut who policy)) fuel)).map
            some := by
  simpa only [pbsRootDecodeProfile_update, pbsRootDecodeProfile_lift] using
    pbsRootChild_continuation_law M roots cut rootDepth child
      (Profile.update (pbsRootBehavioralFullProfile M roots unknown) who policy) fuel

/-- Every original deviation lifts at the child query, transferring the
rooted child Nash guarantee with the same error and remaining horizon. -/
theorem pbsRootChild_isNash
    (cut : Nat) (rootDepth : ∀ history ∈ roots.support, history.trace.length = cut)
    {observations : List M.PublicSignal} {past : List (Option (List M.PublicSignal))}
    (child : PublicBelief (pbsRootFullInformation M roots).toInfoSignals
      (some observations :: past))
    (profile : Profile (pbsRootFullInformation M roots).behavioralSignature)
    (payoff : Fin 2 → E.History → ℝ) (fuel : Nat) (error : ℝ)
    (equilibrium : IsNash (behavioralBeliefForm (pbsRootFullInformation M roots) child fuel)
      (euPreferenceWithin error (fun history who => pbsRootPayoff roots payoff who history))
      profile) :
    IsNash (behavioralBeliefForm (fullInformation.{0, u, u, u, u, u} M)
      (pbsRootChildBelief M roots child) fuel)
      (euPreferenceWithin error (fun history who => payoff who history))
      (pbsRootDecodeProfile M roots cut profile) := by
  rw [isNash_iff] at equilibrium ⊢
  intro who replacement
  have bound := equilibrium who (pbsRootBehavioralFullPolicy M roots who replacement)
  rw [euPreferenceWithin_apply] at bound ⊢
  have payoffEq (history : (pbsRootProtocol roots).History) :
      pbsRootPayoff roots payoff who history = history.state.elim 0 (payoff who) := by
    cases state : history.state <;> simp only [pbsRootPayoff, state, Option.elim]
  have estimate :
      (child.law.bind ((pbsRootFullInformation M roots).runBehavioralFrom
        (Profile.update profile who (pbsRootBehavioralFullPolicy M roots who replacement))
        fuel)).expect (fun history => history.state.elim 0 (payoff who)) ≤
      (child.law.bind ((pbsRootFullInformation M roots).runBehavioralFrom profile fuel)).expect
        (fun history => history.state.elim 0 (payoff who)) + error := by
    simpa only [expectedUtility, behavioralBeliefForm, PublicBelief.continuationLaw, payoffEq]
      using bound
  rw [pbsRootChild_continuation_expect M roots cut rootDepth,
    pbsRootChild_continuation_expect M roots cut rootDepth,
    pbsRootDecodeProfile_update, pbsRootDecodePolicy_lift] at estimate
  exact estimate

end GameTheory.ReBeL
