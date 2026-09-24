/-
# Actual-prefix-weighted fresh continuation error

Query costs are integrated under the original private seed/history law against
an arbitrary fixed unknown opponent. The model reference conditional is used
only where perfect recall proves the required change of measure. Stopped leaves
cost zero; rare changed or disappearing queries are not charged at their maximum
everywhere. The resulting finite-time root theorem is not later-PBS recursion.
-/

import GameTheory.Analysis.ReBeL.CFRDReferenceReweight
import GameTheory.Analysis.ReBeL.CFRDFreshChain

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*}

/-- The charge is averaged under the ACTUAL carried prefix, retaining its
private seed. It does not average under an unrelated model PBS or product law. -/
def cfrDWeightedEnvelopeLoss (seed : FinDist K) (plays : K → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who opponent : Fin 2) (cut remaining : Nat)
    (charge : K → M.InfoState opponent × Bool → ℝ) : ℝ :=
  (privateCarriedPrefix M seed plays unknown who cut).expect fun state =>
    charge state.iteration (M.infoOf opponent state.history.trace,
      cfrDCutLive remaining state.history)

/-- Nonnegative supported costs stay nonnegative without any minimum reach. -/
theorem cfrDWeightedEnvelopeLoss_nonneg (seed : FinDist K)
    (plays : K → Profile M.behavioralSignature) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (cut remaining : Nat)
    (charge : K → M.InfoState opponent × Bool → ℝ) (nonneg : ∀ n tag, 0 ≤ charge n tag) :
    0 ≤ cfrDWeightedEnvelopeLoss M seed plays unknown who opponent cut remaining charge := by
  unfold cfrDWeightedEnvelopeLoss
  have lower := FinDist.expect_mono
    (μ := privateCarriedPrefix M seed plays unknown who cut) (u := fun _ => (0 : ℝ))
    (fun state _ => nonneg state.iteration
      (M.infoOf opponent state.history.trace, cfrDCutLive remaining state.history))
  simpa only [FinDist.expect_const] using lower

variable [∀ who info, Fintype (M.Choice who info)]

/-- Perfect recall transfers a query-dependent reference envelope to the
actual opposing prefix. No worst-case density factor is introduced. -/
theorem privateResolvedEnvelopeGap_prefix_le_weighted (hrecall : M.PerfectRecall)
    (plays : K → Profile M.behavioralSignature) (resolver : CarriedPublicResolver M K)
    (fallback : Profile M.strategicSignature) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (different : opponent ≠ who) (cut remaining : Nat)
    (payoff : E.History → ℝ) (charge : K → M.InfoState opponent × Bool → ℝ)
    (envelope : ∀ n tag, tag ∈ ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).support →
      conditionalOracleValue (unilateralReferenceLaw M (plays n) fallback opponent cut)
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
        (privateResolvedEnvelopeGap M plays resolver unknown who cut remaining payoff n)
        tag ≤ charge n tag) (n : K) :
    (M.runBehavioral (Profile.update unknown who (plays n who)) cut).expect
        (privateResolvedEnvelopeGap M plays resolver unknown who cut remaining payoff n) ≤
      (M.runBehavioral (Profile.update unknown who (plays n who)) cut).expect
        (fun h => charge n (M.infoOf opponent h.trace, cfrDCutLive remaining h)) := by
  rw [privateOpponent_profile M (plays n) unknown who opponent different]
  let reference := unilateralReferenceLaw M (plays n) fallback opponent cut
  let actual := M.runBehavioral (Profile.update (plays n) opponent (unknown opponent)) cut
  let observe := fun h : E.History => (M.infoOf opponent h.trace, cfrDCutLive remaining h)
  let weight := fun tag : M.InfoState opponent × Bool =>
    unilateralDensity M (plays n) fallback opponent (unknown opponent) tag.1
  have density : ∀ h, actual.prob h = reference.prob h * weight (observe h) :=
    unilateralReference_density M hrecall (plays n) fallback opponent (unknown opponent) cut
  calc
    _ = (actual.map observe).expect (conditionalOracleValue reference observe
        (privateResolvedEnvelopeGap M plays resolver unknown who cut remaining payoff n)) :=
      (conditionalOracle_reweight_exact reference actual observe weight density _).symm
    _ ≤ _ := by
      rw [FinDist.expect_map]
      apply FinDist.expect_mono
      intro h reached
      exact envelope n (observe h) (FinDist.support_map.mpr
        ⟨h, informationReweight_support reference actual observe weight density reached, rfl⟩)

/-- The original coherent carried execution consumes the averaged envelope,
not the maximum over all queries. The actual seed/history coupling is preserved. -/
theorem privateCarriedResolve_weighted_envelope_le_prefix (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (seed : FinDist K)
    (plays : K → Profile M.behavioralSignature) (resolver : CarriedPublicResolver M K)
    (fallback : Profile M.strategicSignature) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (different : opponent ≠ who) (cut remaining : Nat)
    (payoff : E.History → ℝ) (charge : K → M.InfoState opponent × Bool → ℝ)
    (envelope : ∀ n tag, tag ∈ ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).support →
      conditionalOracleValue (unilateralReferenceLaw M (plays n) fallback opponent cut)
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
        (privateResolvedEnvelopeGap M plays resolver unknown who cut remaining payoff n)
        tag ≤ charge n tag) :
    (privateCarriedResolve M seed plays resolver unknown who cut remaining).expect payoff -
      seed.expect (fun n => (M.runBehavioral (Profile.update (plays n) opponent
        (cfrDPrefixPolicy M clock (plays n) opponent (unknown opponent) cut))
        (cut + remaining)).expect payoff) ≤
      cfrDWeightedEnvelopeLoss M seed plays unknown who opponent cut remaining charge := by
  have virtual (n : K) :
      (M.runBehavioral (Profile.update (plays n) opponent
        (cfrDPrefixPolicy M clock (plays n) opponent (unknown opponent) cut))
        (cut + remaining)).expect payoff =
      (M.runBehavioral (Profile.update unknown who (plays n who)) cut).expect
        (fun h => (M.runBehavioralFrom (plays n) remaining h).expect payoff) := by
    rw [cfrDPrefix_run_bind, FinDist.expect_bind,
      ← privateOpponent_profile M (plays n) unknown who opponent different]
  simp only [privateCarriedResolve, cfrDWeightedEnvelopeLoss, privateCarriedPrefix,
    FinDist.expect_bind, FinDist.expect_map, privateIterationState, virtual]
  rw [← FinDist.expect_sub]
  apply FinDist.expect_mono
  intro n _
  rw [← FinDist.expect_sub]
  exact privateResolvedEnvelopeGap_prefix_le_weighted M hrecall plays resolver fallback
    unknown who opponent different cut remaining payoff charge envelope n

variable [Fintype E.History]

/-- A computed live query cost. Losing NEW support is charged by the existing
conditional transport defect, never by consulting a NEW fallback posterior. -/
def cfrDFreshTransportCharge (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (opponent : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (n : K) (tag : M.InfoState opponent × Bool) : ℝ :=
  if tag.2 then
    loss + max 0 (cfrDFreshValueChange M (plays n) (next n) fallback opponent payoff
      cut remaining tag.1) + 2 * bound * FinDist.conditionalTransportDefect
        (unilateralReferenceLaw M (plays n) fallback opponent cut)
        (unilateralReferenceLaw M (next n) fallback opponent cut)
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h)) tag
  else 0

/-- The computed allowance is nonnegative even for absent or stopped queries. -/
theorem cfrDFreshTransportCharge_nonneg (plays next : K → Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (opponent : Fin 2) (payoff : E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (hb : 0 ≤ bound) (hl : 0 ≤ loss)
    (n : K) (tag : M.InfoState opponent × Bool) :
    0 ≤ cfrDFreshTransportCharge M plays next fallback opponent payoff
      cut remaining bound loss n tag := by
  unfold cfrDFreshTransportCharge
  split_ifs
  · exact add_nonneg (add_nonneg hl (le_max_left _ _))
      (mul_nonneg (mul_nonneg (by norm_num) hb)
        (FinDist.conditionalTransportDefect_nonneg _ _ _ _))
  · exact le_refl _

/-- NEW local child quality supplies each OLD reference envelope with its own
value change and conditional transport. No cross-family reference equality is
assumed. The private resolver is the original final-average legal-plan draw. -/
theorem cfrDFreshCoherentResolver_query_bound (hrecall : M.PerfectRecall)
    (plays next : K → Profile M.behavioralSignature) (fallback : Profile M.strategicSignature)
    (unknown : Profile M.behavioralSignature) (who opponent : Fin 2)
    (different : opponent ≠ who) (cut remaining : Nat) (payoff : E.History → ℝ)
    (bound loss : ℝ) (lossNonneg : 0 ≤ loss) (bounded : ∀ h, |payoff h| ≤ bound)
    (optimal : ∀ n, CFRDLeafOptimal M (next n) fallback opponent payoff cut remaining loss)
    (n : K) (tag : M.InfoState opponent × Bool)
    (sampled : tag ∈ ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).support) :
    conditionalOracleValue (unilateralReferenceLaw M (plays n) fallback opponent cut)
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
      (privateResolvedEnvelopeGap M plays (cfrDCoherentResolver M fallback next)
        unknown who cut remaining payoff n) tag ≤
      cfrDFreshTransportCharge M plays next fallback opponent payoff
        cut remaining bound loss n tag := by
  rcases tag with ⟨info, flag⟩
  cases flag
  · rw [privateResolvedEnvelopeGap_conditional_stopped M plays
      (cfrDCoherentResolver M fallback next) unknown who opponent cut remaining
      payoff n _ info sampled]
    exact le_refl _
  · have gap (history : E.History) :
        privateResolvedEnvelopeGap M plays (cfrDCoherentResolver M fallback next)
            unknown who cut remaining payoff n history =
          cfrDLeafGain M (next n) opponent (unknown opponent) payoff remaining history +
            ((M.runBehavioralFrom (next n) remaining history).expect payoff -
              (M.runBehavioralFrom (plays n) remaining history).expect payoff) := by
      unfold privateResolvedEnvelopeGap
      rw [cfrDCoherentResolver_tail M hrecall]
      dsimp only [privateIterationState]
      rw [privateOpponent_profile M (next n) unknown who opponent different]
      unfold cfrDLeafGain
      ring
    have gainBound (h : E.History) :
        |cfrDLeafGain M (next n) opponent (unknown opponent) payoff remaining h| ≤ 2 * bound := by
      unfold cfrDLeafGain
      have first := FinDist.abs_expect_le_of_abs_bound
        (M.runBehavioralFrom (Profile.update (next n) opponent (unknown opponent)) remaining h)
        payoff (fun history _ => bounded history)
      have second := FinDist.abs_expect_le_of_abs_bound
        (M.runBehavioralFrom (next n) remaining h) payoff (fun history _ => bounded history)
      have triangle := abs_sub
        ((M.runBehavioralFrom (Profile.update (next n) opponent (unknown opponent))
          remaining h).expect payoff) ((M.runBehavioralFrom (next n) remaining h).expect payoff)
      linarith
    have transported := FinDist.condOnFibre_expect_le_add_transport
      (unilateralReferenceLaw M (plays n) fallback opponent cut)
      (unilateralReferenceLaw M (next n) fallback opponent cut)
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h)) (info, true) sampled
      (cfrDLeafGain M (next n) opponent (unknown opponent) payoff remaining)
      (2 * bound) loss lossNonneg gainBound (optimal n (unknown opponent) info)
    have drift := le_max_right 0 (cfrDFreshValueChange M (plays n) (next n) fallback
      opponent payoff cut remaining info)
    unfold cfrDFreshTransportCharge
    dsimp only
    unfold conditionalOracleValue
    rw [funext gap, FinDist.expect_add]
    unfold cfrDFreshValueChange conditionalOracleValue at drift
    linarith

/-- Root security uses the ACTUAL weighted envelope together with focal full
regret and opponent prefix regret. A seed-revealed opponent is not introduced. -/
theorem privateCarriedResolve_security_of_weighted_envelope (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (seed : FinDist K)
    (plays : K → Profile M.behavioralSignature) (resolver : CarriedPublicResolver M K)
    (fallback : Profile M.strategicSignature) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (different : opponent ≠ who) (cut remaining : Nat)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (reference : Profile M.behavioralSignature)
    (equilibrium : IsNash (M.toBehavioralGameForm (cut + remaining))
      (euPreference (fun h player => payoff player h)) reference)
    (ownLoss trunkLoss : ℝ) (charge : K → M.InfoState opponent × Bool → ℝ)
    (focalRegret : seed.expect (fun n =>
      (M.runBehavioral (Profile.update (plays n) who (reference who))
        (cut + remaining)).expect (payoff who) -
      (M.runBehavioral (plays n) (cut + remaining)).expect (payoff who)) ≤ ownLoss)
    (trunkRegret : seed.expect (fun n =>
      (M.runBehavioral (Profile.update (plays n) opponent
        (cfrDPrefixPolicy M clock (plays n) opponent (unknown opponent) cut))
        (cut + remaining)).expect (payoff opponent) -
      (M.runBehavioral (plays n) (cut + remaining)).expect (payoff opponent)) ≤ trunkLoss)
    (envelope : ∀ n tag, tag ∈ ((unilateralReferenceLaw M (plays n) fallback opponent cut).map
      (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))).support →
      conditionalOracleValue (unilateralReferenceLaw M (plays n) fallback opponent cut)
        (fun h => (M.infoOf opponent h.trace, cfrDCutLive remaining h))
        (privateResolvedEnvelopeGap M plays resolver unknown who cut remaining (payoff opponent) n)
        tag ≤ charge n tag) :
    (M.runBehavioral reference (cut + remaining)).expect (payoff who) -
        (ownLoss + trunkLoss +
          cfrDWeightedEnvelopeLoss M seed plays unknown who opponent cut remaining charge) ≤
      (privateCarriedResolve M seed plays resolver unknown who cut remaining).expect
        (payoff who) := by
  have opposite (law : FinDist E.History) :
      law.expect (payoff opponent) = -law.expect (payoff who) := by
    rcases (by decide : ∀ p : Fin 2, p = 0 ∨ p = 1) who with rfl | rfl
    · have other : opponent = 1 := by omega
      subst opponent
      exact zeroSum.expectedUtility_one law
    · have other : opponent = 0 := by omega
      subst opponent
      have negation : law.expect (payoff 1) = -law.expect (payoff 0) :=
        zeroSum.expectedUtility_one law
      linarith
  have referenceLower :
      (M.runBehavioral reference (cut + remaining)).expect (payoff who) ≤
        seed.expect (fun n => (M.runBehavioral
          (Profile.update (plays n) who (reference who)) (cut + remaining)).expect
            (payoff who)) := by
    rw [← FinDist.expect_const seed
      ((M.runBehavioral reference (cut + remaining)).expect (payoff who))]
    apply FinDist.expect_mono
    intro n _
    have secured :
        (M.runBehavioral (Profile.update reference opponent (plays n opponent))
          (cut + remaining)).expect (payoff opponent) ≤
        (M.runBehavioral reference (cut + remaining)).expect (payoff opponent) :=
      (isNash_iff (F := M.toBehavioralGameForm (cut + remaining))
        (weaklyPrefers := euPreference (fun h p => payoff p h)) reference).mp
          equilibrium opponent (plays n opponent)
    rw [opposite, opposite,
      ← privateOpponent_profile M reference (plays n) who opponent different] at secured
    linarith
  have resolved := privateCarriedResolve_weighted_envelope_le_prefix M clock hrecall seed plays
    resolver fallback unknown who opponent different cut remaining (payoff opponent) charge envelope
  rw [FinDist.expect_sub] at focalRegret trunkRegret
  have negate (f : K → ℝ) : seed.expect (fun n => -f n) = -seed.expect f := by
    simpa only [neg_one_mul] using FinDist.expect_smul (-1) seed f
  simp_rw [opposite, negate] at trunkRegret resolved
  linarith

variable [∀ who, DecidableEq (M.InfoState who)]

/-- The actual noisy depth-limited parent supplies both regret bounds. The
NEW child's ordinary local quality supplies the query bounds, and transport
and value change are integrated under the original unknown-opponent prefix.
The finite outer iteration and positive numerical-error terms remain explicit. -/
theorem cfrDDepth_fresh_weighted_security (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (oracle : CFRDValueOracle M) (bound error loss newLoss : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 ≤ loss) (hn : 0 ≤ newLoss)
    (bounded : ∀ who h, |payoff who h| ≤ bound)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error)
    (optimal : CFRDDepthLeafOptimal M clock fallback payoff cut remaining oracle loss)
    (reference : Profile M.behavioralSignature)
    (equilibrium : IsNash (M.toBehavioralGameForm (cut + remaining))
      (euPreference (fun h who => payoff who h)) reference)
    (unknown : Profile M.behavioralSignature) (who opponent : Fin 2)
    (different : opponent ≠ who) (t : Nat) [NeZero t]
    (next : Fin t → Profile M.behavioralSignature)
    (newOptimal : ∀ n, CFRDLeafOptimal M (next n) fallback opponent
      (payoff opponent) cut remaining newLoss) :
    let plays := fun n : Fin t => cfrDDepthPlay M clock fallback payoff
      cut remaining oracle n.val
    (M.runBehavioral reference (cut + remaining)).expect (payoff who) -
      ((cfrDDepthErrorConstant M clock fallback cut remaining who +
          cfrDDepthErrorConstant M clock fallback cut remaining opponent) * error +
        (cfrDDepthFiniteConstant M clock fallback cut remaining bound who +
          cfrDDepthFiniteConstant M clock fallback cut remaining bound opponent) / Real.sqrt t +
        loss + cfrDWeightedEnvelopeLoss M (cfrIterationLaw t) plays unknown who opponent
          cut remaining (cfrDFreshTransportCharge M plays next fallback opponent
            (payoff opponent) cut remaining bound newLoss)) ≤
      (privateCarriedResolve M (cfrIterationLaw t) plays
        (cfrDCoherentResolver M fallback next) unknown who cut remaining).expect (payoff who) := by
  dsimp only
  let plays := fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val
  let charge := cfrDFreshTransportCharge M plays next fallback opponent (payoff opponent)
    cut remaining bound newLoss
  have security := privateCarriedResolve_security_of_weighted_envelope M clock hrecall
    (cfrIterationLaw t) plays (cfrDCoherentResolver M fallback next) fallback unknown
    who opponent different cut remaining payoff zeroSum reference equilibrium
    (cfrDDepthMeanBudget M clock fallback cut remaining bound error loss who t)
    (cfrDDepthMeanBudget M clock fallback cut remaining bound error 0 opponent t) charge
    (cfrDDepth_mean_regret_le M clock hrecall fallback payoff cut remaining oracle
      bound error loss hb he hl bounded accurate optimal who (reference who) t)
    (cfrDDepth_prefix_mean_le M clock hrecall fallback payoff cut remaining oracle
      bound error hb he bounded accurate opponent (unknown opponent) t)
    (cfrDFreshCoherentResolver_query_bound M hrecall plays next fallback unknown who opponent
      different cut remaining (payoff opponent) bound newLoss hn (bounded opponent) newOptimal)
  have ownBound := cfrDDepthMeanBudget_le_constants M clock fallback cut remaining
    bound error loss he who t
  have otherBound := cfrDDepthMeanBudget_le_constants M clock fallback cut remaining
    bound error 0 he opponent t
  dsimp only [plays, charge] at security
  rw [add_mul, add_div]
  linarith

end GameTheory.ReBeL
