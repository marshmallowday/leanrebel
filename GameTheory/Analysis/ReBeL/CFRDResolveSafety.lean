/-
# Security after a public continuation re-solve

The extra local replacement allowance is retained explicitly. The solver's
finite-iteration error does not disappear when numerical value error is zero.
This compositional theorem is separate from proving the local contract for
a particular recursively computed continuation.
-/

import GameTheory.Analysis.ReBeL.CFRDResolve

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*}

/-- The boundary resolver preserves the already selected complete profile. -/
def keepCarriedResolver (plays : K → Profile M.behavioralSignature) :
    CarriedPublicResolver M K := fun iteration _ _ => FinDist.pure (plays iteration)

/-- Preserving the selected profile loses nothing, including at stopped leaves
and public observations with no model posterior. -/
theorem privateResolvedLoss_keep (plays : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (cut remaining : Nat)
    (payoff : E.History → ℝ) (iteration : K) (history : E.History) :
    privateResolvedLoss M plays (keepCarriedResolver M plays) unknown who
      cut remaining payoff iteration history = 0 := by
  by_cases live : cfrDCutLive remaining history = true
  · have tail : carriedResolvedTail M (keepCarriedResolver M plays) unknown who remaining
        (privateIterationState M plays cut iteration history) =
        M.runBehavioralFrom (Profile.update unknown who (plays iteration who))
          remaining history := by
      unfold carriedResolvedTail
      rw [if_pos (show cfrDCutLive remaining
        (privateIterationState M plays cut iteration history).history = true from live)]
      exact FinDist.pure_bind _ _
    unfold privateResolvedLoss
    rw [tail, sub_self]
  · exact privateResolvedLoss_stopped M plays (keepCarriedResolver M plays) unknown who
      cut remaining payoff iteration history live

private theorem resolver_fibre_support {A B : Type*} (law : FinDist A)
    (observe : A → B) (info : B) (value : A)
    (reached : value ∈ (law.condOnFibre observe info).support) : value ∈ law.support := by
  unfold FinDist.condOnFibre at reached
  split at reached
  · exact (FinDist.support_condOn _ _ _ reached).2
  · exact reached

variable [∀ who info, Fintype (M.Choice who info)]

/-- A pointwise semantic calculation at reached live leaves supplies the
conditional contract; unreachable histories need not satisfy this premise. -/
theorem CFRDResolverLocal_of_pointwise
    (plays : K → Profile M.behavioralSignature) (resolver : CarriedPublicResolver M K)
    (fallback : (who : Fin 2) → M.Policy who) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (cut remaining : Nat) (payoff : E.History → ℝ) (loss : ℝ)
    (bounded : ∀ iteration history,
      history ∈ (unilateralReferenceLaw M (plays iteration) fallback opponent cut).support →
      cfrDCutLive remaining history = true →
      privateResolvedLoss M plays resolver unknown who cut remaining payoff
        iteration history ≤ loss) :
    CFRDResolverLocal M plays resolver fallback unknown who opponent
      cut remaining payoff loss := by
  intro iteration info sampled
  unfold conditionalOracleValue
  apply FinDist.expect_le_of_forall
  intro history reached
  have same := congrArg Prod.snd (conditionalOracle_support
    (unilateralReferenceLaw M (plays iteration) fallback opponent cut)
    (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
    (info, true) sampled history reached)
  exact bounded iteration history (resolver_fibre_support _ _ _ history reached) same

/-- The preservation boundary satisfies the local contract without assuming it. -/
theorem keepCarriedResolver_local (plays : K → Profile M.behavioralSignature)
    (fallback : (who : Fin 2) → M.Policy who) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (cut remaining : Nat) (payoff : E.History → ℝ) :
    CFRDResolverLocal M plays (keepCarriedResolver M plays) fallback unknown who opponent
      cut remaining payoff 0 := by
  apply CFRDResolverLocal_of_pointwise
  intro iteration history _ _
  rw [privateResolvedLoss_keep]

variable [Fintype E.History] [∀ who, DecidableEq (M.InfoState who)]

/-- Actual public re-solving inherits the solver's one-sided security bound
plus its LOCAL continuation-replacement loss. The unknown opposing strategy
remains arbitrary and seed-blind. This is not a mutual-Nash claim about it. -/
theorem cfrDDepth_resolved_security (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : Fin 2) → M.Policy who)
    (payoff : Fin 2 → E.History → ℝ)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (cut remaining : Nat) (oracle : CFRDValueOracle M) (bound error loss : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 ≤ loss)
    (bounded : ∀ who history, |payoff who history| ≤ bound)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error)
    (optimal : CFRDDepthLeafOptimal M clock fallback payoff cut remaining oracle loss)
    (reference : Profile M.behavioralSignature)
    (equilibrium : IsNash (M.toBehavioralGameForm (cut + remaining))
      (euPreference (fun history who => payoff who history)) reference)
    (unknown : Profile M.behavioralSignature) (who opponent : Fin 2)
    (different : opponent ≠ who) (t : Nat) [NeZero t]
    (resolver : CarriedPublicResolver M (Fin t)) (replacementLoss : ℝ)
    (nonneg : 0 ≤ replacementLoss)
    (localBound : CFRDResolverLocal M
      (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val)
      resolver fallback unknown who opponent cut remaining (payoff who) replacementLoss) :
    (M.runBehavioral reference (cut + remaining)).expect (payoff who) -
      ((cfrDDepthErrorConstant M clock fallback cut remaining 0 +
          cfrDDepthErrorConstant M clock fallback cut remaining 1) * error +
        (cfrDDepthFiniteConstant M clock fallback cut remaining bound 0 +
          cfrDDepthFiniteConstant M clock fallback cut remaining bound 1) / Real.sqrt t +
        2 * loss + replacementLoss) ≤
      (privateCarriedResolve M (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val)
        resolver unknown who cut remaining).expect (payoff who) := by
  have prior := cfrDDepth_carried_security M clock hrecall fallback payoff hzero cut remaining
    oracle bound error loss hb he hl bounded accurate optimal reference equilibrium unknown who t
  have replacement := privateCarriedResolve_loss_le M hrecall (cfrIterationLaw t)
    (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val)
    resolver fallback unknown who opponent different cut remaining (payoff who)
    replacementLoss nonneg localBound
  linarith

end GameTheory.ReBeL
