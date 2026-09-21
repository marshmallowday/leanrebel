/-
# Reverse PBS-policy and original information-set CFR controls

A live factual posterior exercises the computed fixed-T solver, arbitrary
unilateral randomization, and conditional type gains. The remaining controls
check local non-leakage, exact original round trips, stopping and cut sensitivity.
-/

import GameTheory.Analysis.ReBeL.PBSInformationCFR
import GameTheory.Analysis.ReBeL.Examples.PBSRootCFR

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

/-- Retain the existing exhaustive finite carrier, not a restricted play trace. -/
local instance decodeControlHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- The actual fixed-T information-set output is Nash up to its derived error
in the ORIGINAL live PBS continuation game, not only the administrative game. -/
theorem pbsDecode_live_cfr (t : Nat) [NeZero t] :
    IsNash (behavioralBeliefForm (model fullPrior) finiteBudgetControlBelief 1)
      (euPreferenceWithin
        (pbsRootCFRBound (reducedModel fullPrior) finiteBudgetControlBelief.law (fun _ => 2) 1 t)
        (fun history who => cfrPayoff who history))
      (pbsInformationCFR (reducedModel fullPrior) finiteBudgetControlBelief
        pbsRootControlFallback cfrPayoff 1 t) :=
  pbsInformationCFR_isNash (reducedModel fullPrior) finiteBudgetControlBelief
    pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior)
    (fun _ => 2) (fun _ => by norm_num) cfrPayoff_abs_le_two 1 t

/-- A fresh randomized deviation preserves the full history law against
newly computed CFR opponents, not merely an original-to-root lifted profile. -/
theorem pbsDecode_live_computed_deviation (t : Nat) [NeZero t] :
    ((pbsRootFullInformation (reducedModel fullPrior) finiteBudgetControlBelief.law).runBehavioral
      (Profile.update (pbsRootCFR (reducedModel fullPrior) finiteBudgetControlBelief.law
        pbsRootControlFallback cfrPayoff 1 t) 0
        (pbsRootBehavioralFullPolicy (reducedModel fullPrior) finiteBudgetControlBelief.law
          0 freshBitPolicy)) 2).map History.state =
      (finiteBudgetControlBelief.law.bind ((model fullPrior).runBehavioralFrom
        (Profile.update (pbsInformationCFR (reducedModel fullPrior) finiteBudgetControlBelief
          pbsRootControlFallback cfrPayoff 1 t) 0 freshBitPolicy) 1)).map some :=
  pbsRootDecodeProfile_unilateral_law (reducedModel fullPrior) finiteBudgetControlBelief.law _
    (pbsRoot_publicBelief_depth (reducedModel fullPrior) finiteBudgetControlBelief) _
    0 freshBitPolicy 1

/-- The actual supported type has a conditional finite-T gain guarantee with
its own posterior mass visible in the denominator. No uniform floor is supplied. -/
theorem pbsDecode_live_conditional_gain (t : Nat) [NeZero t]
    (replacement : (model fullPrior).BehavioralPolicy 0) :
    let profile := pbsInformationCFR (reducedModel fullPrior)
      (finiteBudgetControlSlice.mixture finiteBudgetControlOwn) pbsRootControlFallback cfrPayoff 1 t
    finiteBudgetControlSlice.conditionalPayoff profile 1 (cfrPayoff 0) replacement
        finiteBudgetControlRoot -
      finiteBudgetControlSlice.conditionalPayoff profile 1 (cfrPayoff 0) (profile 0)
        finiteBudgetControlRoot ≤
      pbsRootCFRBound (reducedModel fullPrior)
        (finiteBudgetControlSlice.mixture finiteBudgetControlOwn).law (fun _ => 2) 1 t /
          finiteBudgetControlOwn.prob finiteBudgetControlRoot := by
  have sampled : finiteBudgetControlRoot ∈ finiteBudgetControlOwn.support :=
    (cfrDFactualChildTypeLaw_support (reducedModel fullPrior) (carriedBitProfile false)
      2 1 factualChild_possible finiteBudgetControlRoot finiteBudgetControlRoot).mpr
      factualChild_live_sampled
  exact pbsInformationCFR_conditional_gain (reducedModel fullPrior) finiteBudgetControlSlice
    finiteBudgetControlOwn pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior)
    (fun _ => 2) (fun _ => by norm_num) cfrPayoff_abs_le_two 1 t
    finiteBudgetControlRoot sampled replacement

/-- Decoded policies cannot distinguish an opponent's hidden bit, even when
that rooted policy is newly chosen and its syntactic histories are arbitrary. -/
theorem pbsDecode_no_hidden_leak (cut : Nat)
    (policy : (pbsRootFullInformation (reducedModel fullPrior)
      pbsRootHiddenRoots).BehavioralPolicy 0) :
    pbsRootDecodePolicy (reducedModel fullPrior) pbsRootHiddenRoots cut 0 policy
        ((model fullPrior).infoOf 0 (fullDraw (false, false)).trace) =
      pbsRootDecodePolicy (reducedModel fullPrior) pbsRootHiddenRoots cut 0 policy
        ((model fullPrior).infoOf 0 (fullDraw (false, true)).trace) := rfl

/-- The complete genuinely randomized original profile survives the round trip. -/
theorem pbsDecode_randomized_roundtrip (cut : Nat) :
    pbsRootDecodeProfile (reducedModel fullPrior) finiteBudgetControlBelief.law cut
      (pbsRootBehavioralFullProfile (reducedModel fullPrior) finiteBudgetControlBelief.law
        carriedBitOpponent) = carriedBitOpponent :=
  pbsRootDecodeProfile_lift (reducedModel fullPrior) finiteBudgetControlBelief.law cut
    carriedBitOpponent

/-- One administrative step but no continuation step preserves the entire
joint factual root law for ANY newly chosen rooted profile. -/
theorem pbsDecode_zero_continuation
    (profile : Profile (pbsRootFullInformation (reducedModel fullPrior)
      finiteBudgetControlBelief.law).behavioralSignature) :
    ((pbsRootFullInformation (reducedModel fullPrior) finiteBudgetControlBelief.law).runBehavioral
      profile 1).map History.state = finiteBudgetControlBelief.law.map some := by
  have law := pbsRootDecodeProfile_law (reducedModel fullPrior) finiteBudgetControlBelief.law _
    (pbsRoot_publicBelief_depth (reducedModel fullPrior) finiteBudgetControlBelief) profile 0
  simpa only [Nat.zero_add, runBehavioralFrom, runRandomizedFor_zero, FinDist.bind_pure] using law

/-- Every newly decoded rooted policy stops at a terminal original root. -/
theorem pbsDecode_terminal_stops
    (profile : Profile (pbsRootFullInformation (reducedModel fullPrior)
      (FinDist.pure (offPathFinish false))).behavioralSignature) (fuel : Nat) :
    ((pbsRootFullInformation (reducedModel fullPrior)
      (FinDist.pure (offPathFinish false))).runBehavioral profile (fuel + 1)).map History.state =
      FinDist.pure (some (offPathFinish false)) := by
  have depth : ∀ history ∈ (FinDist.pure (offPathFinish false)).support,
      history.trace.length = (offPathFinish false).trace.length := by
    intro history supported
    rw [FinDist.mem_support_pure.mp supported]
  rw [pbsRootDecodeProfile_law (reducedModel fullPrior) _ _ depth,
    FinDist.pure_bind, runBehavioralFrom_of_terminal (model fullPrior) _ fuel
      (h := offPathFinish false) (by trivial), FinDist.map_pure]

/-- Different public cuts can encode the same final AOH differently. This
prevents silently dropping the shared-cut premise for mixed-depth root laws. -/
theorem pbsDecode_cut_matters :
    (AOH.step (AOH.initial () ()) (some true) () ()).rootedAt 0 ≠
      (AOH.step (AOH.initial () ()) (some true) () ()).rootedAt 1 := by
  intro equal
  have lengths := congrArg AOH.length equal
  norm_num [AOH.rootedAt, AOH.rootedSnapshot, AOH.length] at lengths

end GameTheory.ReBeL.Examples.HiddenTypes
