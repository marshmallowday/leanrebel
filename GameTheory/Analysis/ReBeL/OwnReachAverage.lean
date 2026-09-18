/-
# Own-reach weighted behavioral averages

The averaging law depends only on the player's information. Perfect recall
proves that its own-reach weight is independent of the representative history.
The construction retains a stated fallback on zero-reach information states.
-/

import GameTheory.Analysis.ReBeL.PayoffBounds
import GameTheory.Analysis.ReBeL.WeightedAverage
import GameTheory.ReBeL.ReachFactorization

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Own reach as a function of local information. A fixed representative is
used only by the specification; perfect recall proves its independence. -/
def informationOwnReach (strategy : Profile M.behavioralSignature)
    (who : ι) (info : M.InfoState who) : ℝ := by
  classical
  exact if h : ∃ history : E.History, M.infoOf who history.trace = info then
    M.playerReachProbability strategy who h.choose.trace else 0

/-- A representative's own reach is a lawful product of probabilities. -/
theorem informationOwnReach_unitInterval (strategy : Profile M.behavioralSignature)
    (who : ι) (info : M.InfoState who) :
    0 ≤ informationOwnReach M strategy who info ∧
      informationOwnReach M strategy who info ≤ 1 := by
  classical
  unfold informationOwnReach
  split
  · exact playerReach_unitInterval M strategy who _
  · exact ⟨le_rfl, zero_le_one⟩

/-- Equal local information suffices for the actual own-reach coefficient,
including histories unreachable under this particular profile. -/
theorem informationOwnReach_eq_player (hrecall : M.PerfectRecall)
    (strategy : Profile M.behavioralSignature) (who : ι) (history : E.History) :
    informationOwnReach M strategy who (M.infoOf who history.trace) =
      M.playerReachProbability strategy who history.trace := by
  classical
  have hexists : ∃ other : E.History,
      M.infoOf who other.trace = M.infoOf who history.trace := ⟨history, rfl⟩
  unfold informationOwnReach
  rw [dif_pos hexists]
  exact M.playerReachProbability_eq_of_perfectRecall hrecall strategy who
    hexists.choose.trace history.trace hexists.choose_spec

variable {K : Type*} [Fintype K]

/-- Iteration weight times the player's own reach, never the joint reach or
an opponent's posterior. Zero-reach iterations remain present with zero mass. -/
def ownReachWeights (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (who : ι) (info : M.InfoState who) : ReachWeights K :=
  ⟨fun k => seed.prob k * informationOwnReach M (plays k) who info,
    fun k => mul_nonneg (seed.prob_nonneg k)
      (informationOwnReach_unitInterval M (plays k) who info).1⟩

/-- The behavioral average weights local laws by own reach and uses the
specified deterministic policy only where the total own reach vanishes. -/
def ownReachAveragePolicy (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (who : ι) (fallback : M.Policy who) : M.BehavioralPolicy who :=
  fun info => (ownReachWeights M seed plays who info).average
    (fun k => plays k who info) (FinDist.pure (fallback info))

/-- Each player's average uses its own private iteration distribution. This
definition does not couple the players by a shared iteration draw. -/
def ownReachAverageProfile (seeds : ι → FinDist K)
    (plays : K → Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who) :
    Profile M.behavioralSignature :=
  fun who => ownReachAveragePolicy M (seeds who) plays who (fallback who)

/-- A zero denominator selects exactly the stated fallback, at an actual or
unrealized information state. No division by zero defines a fictitious law. -/
theorem ownReachAveragePolicy_zero (seed : FinDist K)
    (plays : K → Profile M.behavioralSignature) (who : ι) (fallback : M.Policy who)
    (info : M.InfoState who) (hzero : (ownReachWeights M seed plays who info).mass = 0) :
    ownReachAveragePolicy M seed plays who fallback info = FinDist.pure (fallback info) :=
  ReachWeights.average_of_mass_zero _ _ _ hzero

/-- Weighted behavioral averaging preserves the complete own-reach function,
not merely one-step coordinate averages. The zero-denominator case is included
by the mass-times-probability identity, rather than removed by an assumption. -/
theorem ownReachAverage_playerReach (hrecall : M.PerfectRecall)
    (seeds : ι → FinDist K) (plays : K → Profile M.behavioralSignature)
    (fallback : (who : ι) → M.Policy who) (who : ι)
    {state : E.State} (trace : E.Trace state) :
    M.playerReachProbability (ownReachAverageProfile M seeds plays fallback) who trace =
      (seeds who).expect (fun k => M.playerReachProbability (plays k) who trace) := by
  induction trace with
  | start => simp [InformationModel.playerReachProbability]
  | @extend source target prior joint hlegal realized ih =>
      let info := M.infoOf who prior
      let weights := ownReachWeights M (seeds who) plays who info
      let choice := M.choicesOfLegal prior ⟨joint, hlegal⟩ who
      have hweight (k : K) : weights.weight k =
          (seeds who).prob k * M.playerReachProbability (plays k) who prior := by
        dsimp [weights, ownReachWeights, info]
        rw [informationOwnReach_eq_player M hrecall (plays k) who ⟨source, prior⟩]
      have hmass : weights.mass =
          (seeds who).expect (fun k => M.playerReachProbability (plays k) who prior) := by
        rw [FinDist.expect_eq_sum]
        exact Finset.sum_congr rfl (fun k _ => hweight k)
      calc
        _ = M.playerReachProbability (ownReachAverageProfile M seeds plays fallback)
              who prior *
            (weights.average (fun k => plays k who info)
              (FinDist.pure (fallback who info))).prob choice := rfl
        _ = weights.mass *
            (weights.average (fun k => plays k who info)
              (FinDist.pure (fallback who info))).prob choice := by rw [ih, ← hmass]
        _ = ∑ k, weights.weight k * (plays k who info).prob choice :=
          ReachWeights.mass_mul_prob_average _ _ _ _
        _ = (seeds who).expect
            (fun k => M.playerReachProbability (plays k) who
              (prior.extend joint hlegal realized)) := by
          rw [FinDist.expect_eq_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [hweight]
          simp only [InformationModel.playerReachProbability,
            InformationModel.playerStepProb, info, choice]
          ring

end GameTheory.ReBeL
