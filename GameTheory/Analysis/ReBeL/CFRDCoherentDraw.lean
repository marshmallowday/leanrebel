/-
# Coherent finite-plan draws of the parent's constructed continuation

Finite predrawing refines one fixed behavioral child family. The resolver
samples fresh private legal plans, not an independently selected equilibrium.
Equality holds at every legal root against every fixed unknown opponent,
including off-model roots. No extra replacement loss is introduced.
-/

import GameTheory.Analysis.ReBeL.CFRDResolveEnvelope
import GameTheory.Analysis.ReBeL.ValueDeviations

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History]

/-- Independently predraw each player's finite information-local action table.
The input is the actual computed profile, never a witness of its quality. -/
def cfrDPolicyDraw (fallback : Profile M.strategicSignature)
    (profile : Profile M.behavioralSignature) : FinDist (Profile M.behavioralSignature) :=
  FinDist.pi fun who =>
    (FinDist.pi fun info : finiteSites M who => profile who info.val).map
      (fun plan => (FinitePlan.toPolicy M (fallback who) plan).toBehavioral)

/-- Sampling a whole private profile leaves the focal player's marginal equal
to its own finite-plan law; the unknown opponent is not inside this draw. -/
theorem cfrDPolicyDraw_marginal (fallback : Profile M.strategicSignature)
    (profile : Profile M.behavioralSignature) (who : Fin 2) :
    (cfrDPolicyDraw M fallback profile).map (fun next => next who) =
      (FinDist.pi fun info : finiteSites M who => profile who info.val).map
        (fun plan => (FinitePlan.toPolicy M (fallback who) plan).toBehavioral) :=
  FinDist.map_apply_pi who _

/-- Every sampled profile contains deterministic legal policies, even when
its source profile randomizes. Distribution equality is not profile equality. -/
theorem cfrDPolicyDraw_supported_pure (fallback : Profile M.strategicSignature)
    (profile next : Profile M.behavioralSignature)
    (sampled : next ∈ (cfrDPolicyDraw M fallback profile).support)
    (who : Fin 2) (info : M.InfoState who) :
    ∃ action, next who info = FinDist.pure action := by
  have coordinate := FinDist.mem_support_pi.mp sampled who
  rw [FinDist.support_map] at coordinate
  obtain ⟨plan, _, same⟩ := coordinate
  rw [← same]
  exact ⟨_, rfl⟩

/-- The complete unilateral continuation law, not just an expected value,
is preserved at every legal history by one coherent private plan draw. -/
theorem cfrDPolicyDraw_run (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature)
    (profile unknown : Profile M.behavioralSignature) (who : Fin 2)
    (fuel : Nat) (history : E.History) :
    (cfrDPolicyDraw M fallback profile).bind (fun next =>
      M.runBehavioralFrom (Profile.update unknown who (next who)) fuel history) =
      M.runBehavioralFrom (Profile.update unknown who (profile who)) fuel history := by
  calc
    _ = ((cfrDPolicyDraw M fallback profile).map (fun next => next who)).bind
        (fun policy => M.runBehavioralFrom (Profile.update unknown who policy) fuel history) :=
      (FinDist.bind_map _ _ _).symm
    _ = _ := by
      rw [cfrDPolicyDraw_marginal, FinDist.bind_map]
      exact (PublicBelief.deviationLaw_eq_bind_finitePlans_from M hrecall fuel history
        unknown fallback who (profile who)).symm

variable {K : Type*}

/-- Re-evaluate the same parent-indexed family and privately realize its
finite plans. The model PBS may be absent and is not replaced by a true PBS.
This is deferred sampling of that family, not fresh independent re-solving. -/
def cfrDCoherentResolver (fallback : Profile M.strategicSignature)
    (plays : K → Profile M.behavioralSignature) : CarriedPublicResolver M K :=
  fun n _ _ => cfrDPolicyDraw M fallback (plays n)

/-- At every carried state, coherent resampling realizes its parent's
continuation. Terminal and zero-fuel states bypass the draw exactly. -/
theorem cfrDCoherentResolver_tail (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (plays : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (remaining : Nat)
    (state : PrivateIterationState M K) :
    carriedResolvedTail M (cfrDCoherentResolver M fallback plays) unknown who remaining state =
      M.runBehavioralFrom (Profile.update unknown who (plays state.iteration who))
        remaining state.history := by
  by_cases active : cfrDCutLive remaining state.history = true
  · simpa only [carriedResolvedTail, if_pos active, cfrDCoherentResolver] using
      cfrDPolicyDraw_run M hrecall fallback (plays state.iteration) unknown who
        remaining state.history
  · simp only [carriedResolvedTail, if_neg active]
    exact (cfrD_run_stopped M _ remaining state.history active).symm

/-- Fresh finite-plan draws at the cut have the same entire actual law as
carrying the parent family. No reference-support or payoff premise is needed. -/
theorem cfrDCoherentResolver_resolve_eq (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (seed : FinDist K)
    (plays : K → Profile M.behavioralSignature) (unknown : Profile M.behavioralSignature)
    (who : Fin 2) (cut remaining : Nat) :
    privateCarriedResolve M seed plays (cfrDCoherentResolver M fallback plays)
        unknown who cut remaining =
      privateCarriedContinue M seed plays unknown who cut remaining := by
  unfold privateCarriedResolve privateCarriedContinue
  apply FinDist.bind_congr
  intro state _
  exact cfrDCoherentResolver_tail M hrecall fallback plays unknown who remaining state

variable [∀ who info, Fintype (M.Choice who info)]

/-- The existing opponent model envelope follows from the parent's child
contract for this genuinely sampled realization. No replacement inequality
or equality between model and actual opponent beliefs is supplied. -/
theorem cfrDCoherentResolver_envelope (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (plays : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who opponent : Fin 2)
    (different : opponent ≠ who) (cut remaining : Nat) (payoff : E.History → ℝ)
    (loss : ℝ)
    (optimal : ∀ n, CFRDLeafOptimal M (plays n) fallback opponent payoff cut remaining loss) :
    CFRDResolverEnvelope M plays (cfrDCoherentResolver M fallback plays) fallback
      unknown who opponent cut remaining payoff loss := by
  have gap (n : K) (history : E.History) :
      privateResolvedEnvelopeGap M plays (cfrDCoherentResolver M fallback plays)
          unknown who cut remaining payoff n history =
        cfrDLeafGain M (plays n) opponent (unknown opponent) payoff remaining history := by
    unfold privateResolvedEnvelopeGap cfrDLeafGain
    rw [cfrDCoherentResolver_tail M hrecall]
    rw [show (privateIterationState M plays cut n history).iteration = n from rfl,
      show (privateIterationState M plays cut n history).history = history from rfl,
      privateOpponent_profile M (plays n) unknown who opponent different]
  intro n info sampled
  simpa only [conditionalOracleValue, funext (gap n)] using
    optimal n (unknown opponent) info sampled

end GameTheory.ReBeL
