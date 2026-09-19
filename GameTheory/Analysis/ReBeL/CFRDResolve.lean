/-
# Public re-solving at a carried private-iteration cut

The resolver receives the retained private seed and its optional MODEL PBS,
not the hidden history or the unknown opponent's policy. Returned profiles
are information-local. Only live cuts invoke the resolver. A conditional
continuation comparison under positive opponent-reference reach is transferred
to the actual unknown-opponent law; no final security conclusion is stored
in the resolver. Establishing that comparison for a particular recursive
solver remains separate from this compositional result.
-/

import GameTheory.Analysis.ReBeL.CFRDCarriedPlay

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*}

/-- Re-solving may introduce fresh private randomness. Its inputs are only
model data and public observations, never an actual hidden history. -/
abbrev CarriedPublicResolver (K : Type*) :=
  K → (observations : List M.PublicSignal) →
    Option (PublicBelief M.toInfoSignals observations) →
      FinDist (Profile M.behavioralSignature)

/-- The referee executes the new focal policy against the unchanged unknown
opponent. Real terminals and exhausted fuel bypass the resolver entirely. -/
def carriedResolvedTail (resolver : CarriedPublicResolver M K)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (remaining : Nat)
    (state : PrivateIterationState M K) : FinDist E.History :=
  if cfrDCutLive remaining state.history = true then
    (resolver state.iteration (publicTrace M.toInfoSignals state.history.trace)
      state.belief).bind fun next =>
        M.runBehavioralFrom (Profile.update unknown who (next who)) remaining state.history
  else FinDist.pure state.history

/-- Actual execution of a public re-solve after a privately selected prefix. -/
def privateCarriedResolve (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (resolver : CarriedPublicResolver M K) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut remaining : Nat) : FinDist E.History :=
  (privateCarriedPrefix M seed plays unknown who cut).bind
    (carriedResolvedTail M resolver unknown who remaining)

/-- Loss at one canonical cut history from changing the continuation.
The model posterior remains independent of the unknown opposing policy. -/
def privateResolvedLoss (plays : K → Profile M.behavioralSignature)
    (resolver : CarriedPublicResolver M K) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut remaining : Nat) (payoff : E.History → ℝ)
    (iteration : K) (history : E.History) : ℝ :=
  (M.runBehavioralFrom (Profile.update unknown who (plays iteration who))
      remaining history).expect payoff -
    (carriedResolvedTail M resolver unknown who remaining
      (privateIterationState M plays cut iteration history)).expect payoff

/-- Stopped leaves have exactly zero replacement loss, for every resolver. -/
theorem privateResolvedLoss_stopped (plays : K → Profile M.behavioralSignature)
    (resolver : CarriedPublicResolver M K) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut remaining : Nat) (payoff : E.History → ℝ)
    (iteration : K) (history : E.History)
    (stopped : cfrDCutLive remaining history ≠ true) :
    privateResolvedLoss M plays resolver unknown who cut remaining payoff
      iteration history = 0 := by
  have tail : carriedResolvedTail M resolver unknown who remaining
      (privateIterationState M plays cut iteration history) = FinDist.pure history := by
    unfold carriedResolvedTail
    exact if_neg stopped
  unfold privateResolvedLoss
  rw [tail, FinDist.expect_pure,
    cfrDCutValue_stopped M _ payoff remaining history stopped, sub_self]

/-- A stopped conditional fiber also has zero replacement loss. -/
theorem privateResolvedLoss_conditional_stopped
    (plays : K → Profile M.behavioralSignature) (resolver : CarriedPublicResolver M K)
    (unknown : Profile M.behavioralSignature) (who opponent : Fin 2)
    (cut remaining : Nat) (payoff : E.History → ℝ) (iteration : K)
    (law : FinDist E.History) (info : M.InfoState opponent)
    (sampled : (info, false) ∈ (law.map fun history =>
      (M.infoOf opponent history.trace, cfrDCutLive remaining history)).support) :
    conditionalOracleValue law
      (fun history => (M.infoOf opponent history.trace, cfrDCutLive remaining history))
      (privateResolvedLoss M plays resolver unknown who cut remaining payoff iteration)
      (info, false) = 0 := by
  unfold conditionalOracleValue
  calc
    _ = (law.condOnFibre
        (fun history => (M.infoOf opponent history.trace, cfrDCutLive remaining history))
        (info, false)).expect (fun _ => (0 : ℝ)) := by
      apply FinDist.expect_congr
      intro history reached
      have same := congrArg Prod.snd (conditionalOracle_support law
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
        (info, false) sampled history reached)
      apply privateResolvedLoss_stopped
      rw [show cfrDCutLive remaining history = false from same]
      decide
    _ = 0 := FinDist.expect_const _ _

/-- With two players the actual focal-policy profile is a unilateral
opponent deviation from the selected complete model profile. -/
theorem privateOpponent_profile (base unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (different : opponent ≠ who) :
    Profile.update unknown who (base who) =
      Profile.update base opponent (unknown opponent) := by
  funext player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_of_ne _ _ (Ne.symm different)]
  · have other : player = opponent := by omega
    subst player
    rw [Profile.update_of_ne _ _ different, Profile.update_same]

variable [∀ who info, Fintype (M.Choice who info)]

/-- A LOCAL live-fiber continuation comparison. Conditioning uses the
opponent's positive reference law, so off-model opposing actions are covered.
This is not assumed to follow from ordinary on-path Nash values alone. -/
def CFRDResolverLocal (plays : K → Profile M.behavioralSignature)
    (resolver : CarriedPublicResolver M K) (fallback : (who : Fin 2) → M.Policy who)
    (unknown : Profile M.behavioralSignature) (who opponent : Fin 2)
    (cut remaining : Nat) (payoff : E.History → ℝ) (loss : ℝ) : Prop :=
  ∀ iteration info,
    (info, true) ∈ ((unilateralReferenceLaw M (plays iteration) fallback opponent cut).map
      (fun history => (M.infoOf opponent history.trace, cfrDCutLive remaining history))).support →
    conditionalOracleValue (unilateralReferenceLaw M (plays iteration) fallback opponent cut)
      (fun history => (M.infoOf opponent history.trace, cfrDCutLive remaining history))
      (privateResolvedLoss M plays resolver unknown who cut remaining payoff iteration)
      (info, true) ≤ loss

/-- The local comparison transfers to the ACTUAL opponent-induced cut law.
Its density is derived from perfect recall, not supplied as an assumption. -/
theorem privateResolvedLoss_prefix_le (hrecall : M.PerfectRecall)
    (plays : K → Profile M.behavioralSignature) (resolver : CarriedPublicResolver M K)
    (fallback : (who : Fin 2) → M.Policy who) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (different : opponent ≠ who) (cut remaining : Nat)
    (payoff : E.History → ℝ) (loss : ℝ) (nonneg : 0 ≤ loss)
    (localBound : CFRDResolverLocal M plays resolver fallback unknown who opponent
      cut remaining payoff loss) (iteration : K) :
    (M.runBehavioral (Profile.update unknown who (plays iteration who)) cut).expect
      (privateResolvedLoss M plays resolver unknown who cut remaining payoff iteration) ≤ loss := by
  rw [privateOpponent_profile M (plays iteration) unknown who opponent different]
  apply conditionalOracle_reweight_le
    (unilateralReferenceLaw M (plays iteration) fallback opponent cut)
    (M.runBehavioral (Profile.update (plays iteration) opponent (unknown opponent)) cut)
    (fun history => (M.infoOf opponent history.trace, cfrDCutLive remaining history))
    (fun tag : M.InfoState opponent × Bool =>
      unilateralDensity M (plays iteration) fallback opponent (unknown opponent) tag.1)
    (unilateralReference_density M hrecall (plays iteration) fallback opponent
      (unknown opponent) cut)
    (privateResolvedLoss M plays resolver unknown who cut remaining payoff iteration) loss
  rintro ⟨info, flag⟩ sampled
  cases flag
  · rw [privateResolvedLoss_conditional_stopped M plays resolver unknown who opponent
      cut remaining payoff iteration _ info sampled]
    exact nonneg
  · exact localBound iteration info sampled

/-- Public re-solving loses at most the explicit local allowance against
any seed-blind opponent. Neither the old private seed nor a hidden history
is revealed to that opponent or passed to the resolver's policy argument. -/
theorem privateCarriedResolve_loss_le (hrecall : M.PerfectRecall)
    (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (resolver : CarriedPublicResolver M K) (fallback : (who : Fin 2) → M.Policy who)
    (unknown : Profile M.behavioralSignature) (who opponent : Fin 2)
    (different : opponent ≠ who) (cut remaining : Nat) (payoff : E.History → ℝ)
    (loss : ℝ) (nonneg : 0 ≤ loss)
    (localBound : CFRDResolverLocal M plays resolver fallback unknown who opponent
      cut remaining payoff loss) :
    (privateCarriedContinue M seed plays unknown who cut remaining).expect payoff -
      (privateCarriedResolve M seed plays resolver unknown who cut remaining).expect payoff ≤
        loss := by
  simp only [privateCarriedContinue, privateCarriedResolve, privateCarriedPrefix,
    FinDist.map_eq_bind, FinDist.bind_bind, FinDist.pure_bind]
  rw [FinDist.expect_bind, FinDist.expect_bind, ← FinDist.expect_sub]
  apply FinDist.expect_le_of_forall
  intro iteration _
  rw [FinDist.expect_bind, FinDist.expect_bind, ← FinDist.expect_sub]
  exact privateResolvedLoss_prefix_le M hrecall plays resolver fallback unknown who opponent
    different cut remaining payoff loss nonneg localBound iteration

end GameTheory.ReBeL
