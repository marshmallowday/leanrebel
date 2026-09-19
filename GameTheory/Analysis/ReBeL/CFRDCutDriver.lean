/-
# The coupled depth-limited value-oracle driver

An oracle supplies only a legal continuation and one information-value vector
per player. The adapter computes the action scores by stopped execution; it
cannot accept a supplied root-regret certificate or a separate score trace.
Current trunk play, continuation play, value queries and learner updates are
all projections of this one recursively constructed process.
-/

import GameTheory.Analysis.ReBeL.CFRDCutBackup

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- A value response contains no regret, safety or equilibrium conclusion. -/
structure CFRDValueResponse where
  /-- The same information-local continuation used by the value contract. -/
  continuation : Profile M.behavioralSignature
  /-- Values for live cut information states; never pointwise hidden histories. -/
  prediction : (who : ι) → M.InfoState who → ℝ

/-- Iteration and the current legal trunk identify a single response. -/
abbrev CFRDValueOracle := Nat → Profile M.behavioralSignature → CFRDValueResponse M

/-- A clock-depth trunk is information-local and has a fixed public depth. -/
def cfrDDepthTrunk (clock : ObservationClock M) (cut : Nat) : CFRDTrunk M :=
  fun who info => decide (clock.depth who info < cut)

/-- Preserve current trunk choices; use the response only beyond the cut. -/
def cfrDDepthProfile (clock : ObservationClock M) (cut : Nat)
    (strategy continuation : Profile M.behavioralSignature) : Profile M.behavioralSignature :=
  fun who info => if cfrDDepthTrunk M clock cut who info = true then strategy who info
    else continuation who info

variable [Fintype ι] [DecidableEq ι]
variable [∀ who info, Fintype (M.Choice who info)]
variable [∀ who, DecidableEq (M.InfoState who)]

/-- Convert a value response to actual stopped action backups. The full
continuation runner occurs only in proofs and accuracy specifications. -/
def cfrDDepthOracle (clock : ObservationClock M) (fallback : (who : ι) → M.Policy who)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) (oracle : CFRDValueOracle M) :
    CFRDOracle M := fun n strategy =>
  let response := oracle n strategy
  let base := cfrDDepthProfile M clock cut strategy response.continuation
  { continuation := response.continuation
    actionValue := fun who site choice =>
      if cfrDDepthTrunk M clock cut who site.1 = true then
        cfrDCutScore M clock base fallback who site (payoff who) cut remaining
          (response.prediction who) choice
      else 0 }

/-- The actual value response at a round of the coupled learner. -/
def cfrDDepthQuery (clock : ObservationClock M) (fallback : (who : ι) → M.Policy who)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) (oracle : CFRDValueOracle M)
    (n : Nat) : CFRDValueResponse M :=
  oracle n (cfrProfile M fallback (cfrDState M (cfrDDepthTrunk M clock cut) fallback
    (cfrDDepthOracle M clock fallback payoff cut remaining oracle) n))

/-- This is the existing CFR-D recurrence, not a separately assumed play trace. -/
abbrev cfrDDepthPlay (clock : ObservationClock M) (fallback : (who : ι) → M.Policy who)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) (oracle : CFRDValueOracle M)
    (n : Nat) : Profile M.behavioralSignature :=
  cfrDPlay M (cfrDDepthTrunk M clock cut) fallback
    (cfrDDepthOracle M clock fallback payoff cut remaining oracle) n

/-- Play contains exactly the continuation returned with this round's vector. -/
theorem cfrDDepthPlay_eq (clock : ObservationClock M) (fallback : (who : ι) → M.Policy who)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) (oracle : CFRDValueOracle M)
    (n : Nat) :
    cfrDDepthPlay M clock fallback payoff cut remaining oracle n =
      cfrDDepthProfile M clock cut
        (cfrProfile M fallback (cfrDState M (cfrDDepthTrunk M clock cut) fallback
          (cfrDDepthOracle M clock fallback payoff cut remaining oracle) n))
        (cfrDDepthQuery M clock fallback payoff cut remaining oracle n).continuation := rfl

/-- The action table actually consumed by regret matching is computed from
this same iteration's cut law and value vector, not supplied independently. -/
theorem cfrDDepth_actionValue (clock : ObservationClock M)
    (fallback : (who : ι) → M.Policy who) (payoff : ι → E.History → ℝ)
    (cut remaining : Nat) (oracle : CFRDValueOracle M) (n : Nat) (who : ι)
    (site : M.InformationSite who) (searched : clock.depth who site.1 < cut)
    (choice : M.Choice who site.1) :
    (cfrDQuery M (cfrDDepthTrunk M clock cut) fallback
        (cfrDDepthOracle M clock fallback payoff cut remaining oracle) n).actionValue
        who site choice =
      cfrDCutScore M clock (cfrDDepthPlay M clock fallback payoff cut remaining oracle n)
        fallback who site (payoff who) cut remaining
        ((cfrDDepthQuery M clock fallback payoff cut remaining oracle n).prediction who)
        choice := by
  change (if cfrDDepthTrunk M clock cut who site.1 = true then
      cfrDCutScore M clock (cfrDDepthPlay M clock fallback payoff cut remaining oracle n)
        fallback who site (payoff who) cut remaining
        ((cfrDDepthQuery M clock fallback payoff cut remaining oracle n).prediction who) choice
      else 0) = _
  exact if_pos (by simpa only [cfrDDepthTrunk, decide_eq_true_eq] using searched)

/-- The oracle contract is checked against the actual same-iteration profile
on every live information fiber, including counterfactual completions. -/
def CFRDDepthAccurate (clock : ObservationClock M) (fallback : (who : ι) → M.Policy who)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) (oracle : CFRDValueOracle M)
    (error : ℝ) : Prop :=
  ∀ n who, CFRDCutAccurate M (cfrDDepthPlay M clock fallback payoff cut remaining oracle n)
    fallback who (payoff who) cut remaining
    ((cfrDDepthQuery M clock fallback payoff cut remaining oracle n).prediction who) error

/-- Bounded payoffs and the live oracle contract prove the numerical size
premise of the existing coupled learner. No independent bound is assumed. -/
theorem cfrDDepth_score_abs_le (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (fallback : (who : ι) → M.Policy who) (payoff : ι → E.History → ℝ)
    (cut remaining : Nat) (oracle : CFRDValueOracle M) (bound error : ℝ)
    (nonneg : 0 ≤ error) (bounded : ∀ who history, |payoff who history| ≤ bound)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error)
    (n : Nat) (who : ι) (site : M.InformationSite who)
    (searched : clock.depth who site.1 < cut) (choice : M.Choice who site.1) :
    |(cfrDQuery M (cfrDDepthTrunk M clock cut) fallback
        (cfrDDepthOracle M clock fallback payoff cut remaining oracle) n).actionValue
        who site choice| ≤
      (bound + error) / M.playerReachProbability (uniformLegalProfile M fallback)
        who site.2.choose.1.trace := by
  rw [cfrDDepth_actionValue M clock fallback payoff cut remaining oracle n who site searched]
  exact cfrDCutScore_abs_le M clock hrecall _ fallback who site (payoff who) cut remaining
    searched _ bound error nonneg (bounded who) (accurate n who) choice

/-- The actual score regrets approximate canonical regrets. The common
full-score offset cancels before the estimate reaches this recurrence. -/
theorem cfrDDepth_regret_le_prediction (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : (who : ι) → M.Policy who)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) (oracle : CFRDValueOracle M)
    (error : ℝ) (nonneg : 0 ≤ error)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error)
    (n : Nat) (who : ι) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (searched : clock.depth who site.1 < cut) (choice : M.Choice who site.1) :
    M.counterfactualActionRegret (cfrDDepthPlay M clock fallback payoff cut remaining oracle n)
        who site (payoff who) (cut + remaining - clock.depth who site.1) choice ≤
      cfrDPredictedRegret M (cfrDDepthTrunk M clock cut) fallback
        (cfrDDepthOracle M clock fallback payoff cut remaining oracle) n who site choice +
        2 * (error / M.playerReachProbability (uniformLegalProfile M fallback)
          who site.2.choose.1.trace) := by
  have values :
      (cfrDQuery M (cfrDDepthTrunk M clock cut) fallback
          (cfrDDepthOracle M clock fallback payoff cut remaining oracle) n).actionValue who site =
        cfrDCutScore M clock (cfrDDepthPlay M clock fallback payoff cut remaining oracle n)
          fallback who site (payoff who) cut remaining
          ((cfrDDepthQuery M clock fallback payoff cut remaining oracle n).prediction who) := by
    funext action
    exact cfrDDepth_actionValue M clock fallback payoff cut remaining oracle n who site
      searched action
  rw [cfrDPredictedRegret, values]
  exact cfrDCutScore_regret_le M clock hrecall _ fallback who site (payoff who) cut remaining
    searched _ error nonneg (accurate n who) choice

/-- These are the ACTUAL iteration-specific joint public-belief queries.
They are model beliefs, not a claim about an unknown opponent's policy. -/
def cfrDDepthBeliefs (clock : ObservationClock M) (fallback : (who : ι) → M.Policy who)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) (oracle : CFRDValueOracle M)
    (n : Nat) : FinDist (Σ observation, PublicBelief M.toInfoSignals observation) :=
  PublicBelief.split (M.runBehavioral (cfrDDepthPlay M clock fallback payoff cut remaining oracle n)
    cut)

/-- The queried joint PBSs disintegrate this very iteration's stopped law. -/
theorem cfrDDepthBeliefs_bind (clock : ObservationClock M)
    (fallback : (who : ι) → M.Policy who) (payoff : ι → E.History → ℝ)
    (cut remaining : Nat) (oracle : CFRDValueOracle M) (n : Nat) :
    (cfrDDepthBeliefs M clock fallback payoff cut remaining oracle n).bind
        (fun belief => belief.2.law) =
      M.runBehavioral (cfrDDepthPlay M clock fallback payoff cut remaining oracle n) cut :=
  PublicBelief.split_bind_law _

end GameTheory.ReBeL
