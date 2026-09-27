/-
# Changed-kernel native gaps of the actual noisy depth parent

The selected private seed/type law comes from the actual tagged execution.
Fresh compatible kernels and an explicit type readout may depend on that seed.
Only the exact measured kernel discrepancy is added to the constructed native
budget. The same computed average comparison opponent and horizon are retained.
This is not a smallness theorem for arbitrary re-solving or an identification
of supplied fresh kernels with a particular resolver's posterior.
-/

import GameTheory.Analysis.ReBeL.PBSDepthNativeGap
import GameTheory.Analysis.ReBeL.PBSKernelValueTransport

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk ut uv
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {observations nextObservations : List M.PublicSignal} {who : Fin 2}
variable {T : Type ut} {U : Type uv}

/-- Transport the genuine depth-parent conditional gap to changed joint
kernels under the actual correlated event-selected query. The native error
pays the actual event reciprocal; the kernel error is averaged under the
already selected query and is NOT divided by that probability again. -/
theorem pbsInformationDepthCFR_conditioned_kernelGap_le
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun history player => payoff player history))
    (cut remaining : Nat) (bound error loss : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 < loss)
    (bounded : ∀ player history, |payoff player history| ≤ bound)
    (noise : PBSRootDepthNoise M (slice.mixture own).law)
    (noiseBound : ∀ n trunk player info, |noise n trunk player info| ≤ error)
    (t : Nat) [NeZero t]
    (opponents : Profile (fullInformation M).behavioralSignature) (steps : Nat)
    (event : Set ((Fin t × T) × E.History))
    (possible : ∃ point ∈ event, point ∈
      (pbsInformationDepthCFRTaggedExecution M slice own fallback payoff cut remaining
        bound loss noise t opponents steps).support)
    (fresh : Fin t → TypeBeliefSlice (fullInformation M) nextObservations who U)
    (retag : Fin t × T → U) :
    let average := pbsInformationDepthCFR M (slice.mixture own) fallback payoff cut remaining
      bound loss noise t
    let execution := pbsInformationDepthCFRTaggedExecution M slice own fallback payoff cut
      remaining bound loss noise t opponents steps
    let query := (execution.condOn event possible).map Prod.fst
    query.expect (fun pair =>
      |(fresh pair.1).infoValue (fun player => liftPolicy M player (fallback player))
          (cut + remaining) (payoff who) average (retag pair) -
        (fresh pair.1).conditionalPayoff average (cut + remaining) (payoff who)
          (pbsInformationDepthCFRIterate M (slice.mixture own) fallback payoff cut remaining
            bound loss noise pair.1.val who) (retag pair)|) ≤
      pbsRootDepthBudget M (slice.mixture own).law fallback cut remaining bound error loss t /
        execution.probOf event +
      2 * bound * query.expect (fun pair =>
        FinDist.atomVariation (slice.kernel pair.2).law
          ((fresh pair.1).kernel (retag pair)).law) := by
  intro average execution query
  calc
    _ ≤ query.expect (fun pair =>
        |pbsInformationDepthCFRConditionalDrawGap M slice own fallback payoff cut remaining
          bound loss noise t pair.2 pair.1| +
        2 * bound * FinDist.atomVariation (slice.kernel pair.2).law
          ((fresh pair.1).kernel (retag pair)).law) := by
      apply FinDist.expect_mono
      intro pair _
      exact slice.conditionalGap_abs_le_old_add_kernelVariation (fresh pair.1)
        (fullSignals_perfectRecall M.toInfoSignals)
        (fun player => liftPolicy M player (fallback player)) (cut + remaining) (payoff who)
        average (pbsInformationDepthCFRIterate M (slice.mixture own) fallback payoff cut
          remaining bound loss noise pair.1.val who) pair.2 (retag pair) bound (bounded who)
    _ = query.expect (fun pair =>
        |pbsInformationDepthCFRConditionalDrawGap M slice own fallback payoff cut remaining
          bound loss noise t pair.2 pair.1|) +
        2 * bound * query.expect (fun pair => FinDist.atomVariation (slice.kernel pair.2).law
          ((fresh pair.1).kernel (retag pair)).law) := by
      rw [FinDist.expect_add, FinDist.expect_smul]
    _ ≤ _ := add_le_add
      (pbsInformationDepthCFR_conditioned_native_mean_abs_le M slice own fallback payoff zeroSum
        cut remaining bound error loss hb he hl bounded noise noiseBound t opponents steps
        event possible) le_rfl

end GameTheory.ReBeL
