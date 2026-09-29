/-
# The actual rooted parent's saved public law

Read out the existing native saved state without replacing its posterior by
a live-filtered child. The result consumes the selected round's prefix theorem,
and can be used with the decoded public/live scalar and private-security bounds.
-/

import GameTheory.Analysis.ReBeL.PBSRootStoredValue

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u v
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable (roots : FinDist E.History)

/-- Read only the saved joint law; the native state and its private memory
remain untouched. Missing beliefs remain missing. -/
def pbsRootSavedLaw {obs : List (Option (List M.PublicSignal))}
    (belief : Option (PublicBelief (pbsRootFullInformation M roots).toInfoSignals obs)) :
    Option (FinDist E.History) :=
  belief.map (fun posterior => posterior.law.map (pbsRootChildRead roots))

/-- A present saved posterior reads out to exactly the decoded joint PBS.
This is a law projection, not a reconstruction of a native private state. -/
theorem pbsRootSavedLaw_some
    {observations : List M.PublicSignal} {past : List (Option (List M.PublicSignal))}
    (posterior : PublicBelief (pbsRootFullInformation M roots).toInfoSignals
      (some observations :: past)) :
    pbsRootSavedLaw M roots (some posterior) =
      some (pbsRootChildBelief M roots posterior).law := rfl

variable [Fintype (pbsRootProtocol roots).History]
variable [∀ who, Fintype ((pbsRootProtocol roots).Action who)]
variable [∀ who info, Fintype ((pbsRootFullInformation M roots).Choice who info)]
variable [∀ who, DecidableEq ((pbsRootFullInformation M roots).InfoState who)]

/-- The actual noisy parent saves its unfiltered public MODEL posterior.
The initial-law premise concerns this rooted protocol's initial state only. -/
theorem pbsRootComposed_stored_law {K : Type v}
    (fallback : Profile
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots).strategicSignature)
    (payoff : Fin 2 → (pbsRootProtocol roots).History → ℝ)
    (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots))
    (noise : CFRDPredictionNoise
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots)) (round : Nat)
    (state : PrivateIterationState (pbsRootFullInformation M roots) K)
    (prior : PublicBelief (pbsRootFullInformation M roots).toInfoSignals
      (publicTrace (pbsRootFullInformation M roots).toInfoSignals state.history.trace))
    (stored : state.belief = some prior)
    (initial : prior.law = FinDist.pure (pbsRootProtocol roots).initHistory)
    (history : (pbsRootProtocol roots).History)
    (possible : PublicBelief.Possible (S := (pbsRootFullInformation M roots).toInfoSignals)
      ((pbsRootFullInformation M roots).runBehavioral
        (cfrDComposedTrunk
          (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots)
          fallback payoff cut remaining loss solve noise round) cut)
      (publicTrace (pbsRootFullInformation M roots).toInfoSignals history.trace)) :
    let rootModel := pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots
    let trunk := cfrDComposedTrunk rootModel fallback payoff cut remaining loss solve noise round
    let obs := publicTrace (pbsRootFullInformation M roots).toInfoSignals history.trace
    let posterior := PublicBelief.condition
      (S := (pbsRootFullInformation M roots).toInfoSignals)
      ((pbsRootFullInformation M roots).runBehavioral trunk cut) obs possible
    pbsRootSavedLaw M roots
      (cfrDComposedNextState rootModel fallback payoff cut remaining loss solve noise round
        state history).belief =
      some (posterior.law.map (pbsRootChildRead roots)) := by
  intro rootModel trunk obs posterior
  have saved := cfrDComposedRound_storedPublic rootModel fallback payoff cut remaining loss
    solve noise round state prior stored initial history possible
  exact congrArg (pbsRootSavedLaw M roots) saved

/-- At a noninitial public query, the actual saved state reads out to the
public PBS used by the fresh original solve, including any stopped atoms. -/
theorem pbsRootComposed_stored_query_law {K : Type v}
    (fallback : Profile
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots).strategicSignature)
    (payoff : Fin 2 → (pbsRootProtocol roots).History → ℝ)
    (cut remaining : Nat) (loss : ℝ)
    (solve : PBSChildSolve
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots))
    (noise : CFRDPredictionNoise
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots)) (round : Nat)
    (state : PrivateIterationState (pbsRootFullInformation M roots) K)
    (prior : PublicBelief (pbsRootFullInformation M roots).toInfoSignals
      (publicTrace (pbsRootFullInformation M roots).toInfoSignals state.history.trace))
    (stored : state.belief = some prior)
    (initial : prior.law = FinDist.pure (pbsRootProtocol roots).initHistory)
    (history : (pbsRootProtocol roots).History)
    (observations : List M.PublicSignal) (past : List (Option (List M.PublicSignal)))
    (observed : publicTrace (pbsRootFullInformation M roots).toInfoSignals history.trace =
      some observations :: past)
    (possible : CFRDFactualChildPossible
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots)
      (cfrDComposedTrunk
        (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots)
        fallback payoff cut remaining loss solve noise round)
      cut remaining (some observations :: past)) :
    let rootModel := pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) roots
    let trunk := cfrDComposedTrunk rootModel fallback payoff cut remaining loss solve noise round
    let posterior := pbsRootPublicPosterior M roots trunk cut remaining observations past possible
    pbsRootSavedLaw M roots
      (cfrDComposedNextState rootModel fallback payoff cut remaining loss solve noise round
        state history).belief =
      some (pbsRootChildBelief M roots posterior).law := by
  intro rootModel trunk posterior
  have publicPossible : PublicBelief.Possible
      (S := (pbsRootFullInformation M roots).toInfoSignals)
      ((pbsRootFullInformation M roots).runBehavioral trunk cut)
      (publicTrace (pbsRootFullInformation M roots).toInfoSignals history.trace) := by
    rw [observed]
    exact cfrDFactualChildPossible_public rootModel trunk cut remaining
      (some observations :: past) possible
  have saved := pbsRootComposed_stored_law M roots fallback payoff cut remaining loss solve
    noise round state prior stored initial history publicPossible
  refine saved.trans ?_
  apply congrArg some
  dsimp only [pbsRootChildBelief, posterior, pbsRootPublicPosterior, PublicBelief.condition]
  apply congrArg (fun law : FinDist (pbsRootProtocol roots).History =>
    law.map (pbsRootChildRead roots))
  apply FinDist.condOn_eq_of_support_iff
  intro h _
  rw [observed]

end GameTheory.ReBeL
