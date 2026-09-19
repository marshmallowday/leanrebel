/-
# Actual iteration-specific joint PBS queries

The PBS adapter invokes its oracle with the current stopped joint law, split
by public observation, plus explicit counterfactual completions. The numerical
update uses that response. These are not metadata for an independently chosen
play trace. The continuation cannot change a prefix law already searched.
-/

import GameTheory.Analysis.ReBeL.CFRDCutDriver

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Public query data contains joint posteriors, never products of marginals.
Zero factual mass is not relabeled as an observed posterior: the separately
identified unilateral completions retain those needed counterfactual branches. -/
structure CFRDPBSQuery where
  factual : FinDist (Σ observations, PublicBelief M.toInfoSignals observations)
  counterfactual : (who : ι) →
    FinDist (Σ observations, PublicBelief M.toInfoSignals observations)

/-- The oracle receives this iteration's PBS data and returns legal information
policies and value vectors. It cannot return a root-regret or safety certificate. -/
abbrev CFRDPBSOracle := Nat → CFRDPBSQuery M → CFRDValueResponse M

variable [Fintype ι]

/-- Continuation choices outside the searched depth cannot affect its joint
prefix law, including chance and early terminal absorption. -/
theorem runBehavioral_eq_of_before_depth (clock : ObservationClock M)
    (first second : Profile M.behavioralSignature) (cut : Nat)
    (agree : ∀ who info, clock.depth who info < cut → first who info = second who info) :
    M.runBehavioral first cut = M.runBehavioral second cut := by
  unfold InformationModel.runBehavioral
  apply M.runBehavioralFrom_congr_before
  intro history _ _ before who
  apply agree
  rw [clock.correct]
  simpa only [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length,
    Nat.zero_add] using before

variable [DecidableEq ι] [∀ who info, Fintype (M.Choice who info)]

/-- Construct every query from this one current prefix strategy. -/
def cfrDCurrentPBS (fallback : (who : ι) → M.Policy who)
    (strategy : Profile M.behavioralSignature) (cut : Nat) : CFRDPBSQuery M where
  factual := PublicBelief.split (M.runBehavioral strategy cut)
  counterfactual := fun who =>
    PublicBelief.split (unilateralReferenceLaw M strategy fallback who cut)

/-- Query packets depend only on the searched prefix, even for counterfactual
completions. They do not depend circularly on an oracle's returned continuation. -/
theorem cfrDCurrentPBS_prefix_eq (clock : ObservationClock M)
    (fallback : (who : ι) → M.Policy who) (first second : Profile M.behavioralSignature)
    (cut : Nat)
    (agree : ∀ who info, clock.depth who info < cut → first who info = second who info) :
    cfrDCurrentPBS M fallback first cut = cfrDCurrentPBS M fallback second cut := by
  have factual := runBehavioral_eq_of_before_depth M clock first second cut agree
  unfold cfrDCurrentPBS
  rw [factual]
  congr 1
  funext who
  apply congrArg PublicBelief.split
  unfold unilateralReferenceLaw
  apply runBehavioral_eq_of_before_depth M clock
  intro player info before
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]
    exact agree player info before

/-- Completing the current trunk with a legal response leaves its query packet unchanged. -/
theorem cfrDCurrentPBS_depthProfile (clock : ObservationClock M)
    (fallback : (who : ι) → M.Policy who) (cut : Nat)
    (strategy continuation : Profile M.behavioralSignature) :
    cfrDCurrentPBS M fallback (cfrDDepthProfile M clock cut strategy continuation) cut =
      cfrDCurrentPBS M fallback strategy cut := by
  apply cfrDCurrentPBS_prefix_eq M clock
  intro who info before
  exact if_pos (by simpa only [cfrDDepthTrunk, decide_eq_true_eq] using before)

/-- The factual queries disintegrate the actual current joint law. -/
theorem cfrDCurrentPBS_factual_bind (fallback : (who : ι) → M.Policy who)
    (strategy : Profile M.behavioralSignature) (cut : Nat) :
    (cfrDCurrentPBS M fallback strategy cut).factual.bind (fun query => query.2.law) =
      M.runBehavioral strategy cut := PublicBelief.split_bind_law _

/-- Each completion is labeled by the unilateral reference law it disintegrates. -/
theorem cfrDCurrentPBS_counterfactual_bind (fallback : (who : ι) → M.Policy who)
    (strategy : Profile M.behavioralSignature) (cut : Nat) (who : ι) :
    ((cfrDCurrentPBS M fallback strategy cut).counterfactual who).bind
        (fun query => query.2.law) =
      unilateralReferenceLaw M strategy fallback who cut := PublicBelief.split_bind_law _

/-- This adapter really calls the PBS oracle, rather than simply recording
unused posterior data alongside an unrelated action table. -/
def cfrDValueOracleOfPBS (fallback : (who : ι) → M.Policy who) (cut : Nat)
    (oracle : CFRDPBSOracle M) : CFRDValueOracle M :=
  fun n strategy => oracle n (cfrDCurrentPBS M fallback strategy cut)

variable [∀ who, DecidableEq (M.InfoState who)]

/-- The value response consumed by the actual learner was queried at this
same iteration's PBSs, including its counterfactual completion packet. -/
theorem cfrDDepthQuery_uses_PBS (clock : ObservationClock M)
    (fallback : (who : ι) → M.Policy who) (payoff : ι → E.History → ℝ)
    (cut remaining : Nat) (oracle : CFRDPBSOracle M) (n : Nat) :
    cfrDDepthQuery M clock fallback payoff cut remaining
        (cfrDValueOracleOfPBS M fallback cut oracle) n =
      oracle n (cfrDCurrentPBS M fallback
        (cfrDDepthPlay M clock fallback payoff cut remaining
          (cfrDValueOracleOfPBS M fallback cut oracle) n) cut) := by
  rw [cfrDDepthPlay_eq, cfrDCurrentPBS_depthProfile]
  rfl

/-- On a genuinely supported factual live observation the completed value
vector is the ordinary current-profile conditional value vector. No equality
with a posterior is asserted for a zero-mass factual observation. -/
theorem cfrDCutAccurate_factual (hrecall : M.PerfectRecall)
    (base : Profile M.behavioralSignature) (fallback : (who : ι) → M.Policy who)
    (who : ι) (payoff : E.History → ℝ) (cut remaining : Nat)
    (prediction : M.InfoState who → ℝ) (error : ℝ)
    (accurate : CFRDCutAccurate M base fallback who payoff cut remaining prediction error)
    (info : M.InfoState who)
    (sampled : (info, true) ∈ ((M.runBehavioral base cut).map
      (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))).support) :
    |prediction info - conditionalOracleValue (M.runBehavioral base cut)
      (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))
      (fun history => (M.runBehavioralFrom base remaining history).expect payoff) (info, true)| ≤
      error := by
  have density : ∀ history, (M.runBehavioral base cut).prob history =
      (unilateralReferenceLaw M base fallback who cut).prob history *
        unilateralDensity M base fallback who (base who) (M.infoOf who history.trace) := by
    simpa only [Profile.update_eq_self] using
      unilateralReference_density M hrecall base fallback who (base who) cut
  have referenceSample : (info, true) ∈
      ((unilateralReferenceLaw M base fallback who cut).map
        (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))).support := by
    rw [FinDist.support_map] at sampled ⊢
    obtain ⟨history, reached, same⟩ := sampled
    exact ⟨history, informationReweight_support _ _
      (fun history => M.infoOf who history.trace) _ density reached, same⟩
  rw [conditionalOracle_reweight_value (unilateralReferenceLaw M base fallback who cut)
    (M.runBehavioral base cut)
    (fun history => (M.infoOf who history.trace, cfrDCutLive remaining history))
    (fun tag : M.InfoState who × Bool => unilateralDensity M base fallback who (base who) tag.1)
    density (info, true) sampled]
  exact accurate info referenceSample

end GameTheory.ReBeL
