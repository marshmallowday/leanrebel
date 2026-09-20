/-
# Global security from counterfactual continuation envelopes

Trunk regret is used directly, rather than bounding loss against the previous
policy's exploitation of a fixed opponent. The actual CFR-D recurrence supplies
both regret terms. A source-consistent recursive child still has to establish
the local opponent envelope; independent Nash selection does not discharge it.
-/

import GameTheory.Analysis.ReBeL.CFRDResolveEnvelope

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K : Type*}
variable [∀ who info, Fintype (M.Choice who info)]

/-- The focal player's full regret and the opponent's PREFIX regret suffice.
No old-versus-new fixed-opponent comparison, refresh rate or regret bound for
a seed-revealed opponent is required. The following theorem supplies the two
regret premises from the actual depth-limited learning recurrence. -/
theorem privateCarriedResolve_security_of_envelope (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (seed : FinDist K)
    (plays : K → Profile M.behavioralSignature) (resolver : CarriedPublicResolver M K)
    (fallback : Profile M.strategicSignature) (unknown : Profile M.behavioralSignature)
    (who opponent : Fin 2) (different : opponent ≠ who) (cut remaining : Nat)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (reference : Profile M.behavioralSignature)
    (equilibrium : IsNash (M.toBehavioralGameForm (cut + remaining))
      (euPreference (fun h player => payoff player h)) reference)
    (ownLoss trunkLoss envelopeLoss : ℝ) (nonneg : 0 ≤ envelopeLoss)
    (focalRegret : seed.expect (fun n =>
      (M.runBehavioral (Profile.update (plays n) who (reference who))
        (cut + remaining)).expect (payoff who) -
      (M.runBehavioral (plays n) (cut + remaining)).expect (payoff who)) ≤ ownLoss)
    (trunkRegret : seed.expect (fun n =>
      (M.runBehavioral (Profile.update (plays n) opponent
        (cfrDPrefixPolicy M clock (plays n) opponent (unknown opponent) cut))
        (cut + remaining)).expect (payoff opponent) -
      (M.runBehavioral (plays n) (cut + remaining)).expect (payoff opponent)) ≤ trunkLoss)
    (envelope : CFRDResolverEnvelope M plays resolver fallback unknown who opponent
      cut remaining (payoff opponent) envelopeLoss) :
    (M.runBehavioral reference (cut + remaining)).expect (payoff who) -
        (ownLoss + trunkLoss + envelopeLoss) ≤
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
      have negation := zeroSum.expectedUtility_one law
      change law.expect (payoff 1) = -law.expect (payoff 0) at negation
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
  have resolved := privateCarriedResolve_envelope_le_prefix M clock hrecall seed plays
    resolver fallback unknown who opponent different cut remaining (payoff opponent)
    envelopeLoss nonneg envelope
  rw [FinDist.expect_sub] at focalRegret trunkRegret
  simp_rw [opposite, FinDist.expect_neg] at trunkRegret resolved
  linarith

variable [Fintype E.History] [∀ who, DecidableEq (M.InfoState who)]

/-- The prefix-only mean regret comes directly from the searched-site learner.
Unlike full root regret it contains no separate continuation-loss term. -/
theorem cfrDDepth_prefix_mean_le (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (oracle : CFRDValueOracle M) (bound error : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (bounded : ∀ who h, |payoff who h| ≤ bound)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error)
    (who : Fin 2) (target : M.BehavioralPolicy who) (t : Nat) [NeZero t] :
    (cfrIterationLaw t).expect (fun n =>
      (M.runBehavioral (Profile.update
        (cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val) who
        (cfrDPrefixPolicy M clock
          (cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val) who target cut))
        (cut + remaining)).expect (payoff who) -
      (M.runBehavioral (cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val)
        (cut + remaining)).expect (payoff who)) ≤
      cfrDDepthMeanBudget M clock fallback cut remaining bound error 0 who t := by
  rw [cfrIterationLaw_expect t (fun n =>
    (M.runBehavioral (Profile.update
      (cfrDDepthPlay M clock fallback payoff cut remaining oracle n) who
      (cfrDPrefixPolicy M clock (cfrDDepthPlay M clock fallback payoff cut remaining oracle n)
        who target cut)) (cut + remaining)).expect (payoff who) -
      (M.runBehavioral (cfrDDepthPlay M clock fallback payoff cut remaining oracle n)
        (cut + remaining)).expect (payoff who))]
  have positive : 0 < (t : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne t))
  simpa only [cfrDDepthMeanBudget, add_zero] using
    div_le_div_of_nonneg_right (cfrDDepth_prefix_cumulative_le M clock hrecall fallback
      payoff cut remaining oracle bound error hb he bounded accurate who target t) positive.le

/-- The actual noisy CFR-D supplies both regret bounds. The only unresolved
re-solving obligation is the LOCAL opponent envelope, not a final lower bound.
Numerical error, finite iterations, focal child loss and envelope loss remain
separate. No bounded-refresh mixture or fixed-opponent no-loss premise is used. -/
theorem cfrDDepth_resolve_envelope_security (clock : ObservationClock M)
    (hrecall : M.PerfectRecall) (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h who => payoff who h)) (cut remaining : Nat)
    (oracle : CFRDValueOracle M) (bound error loss envelopeLoss : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error) (hl : 0 ≤ loss) (hc : 0 ≤ envelopeLoss)
    (bounded : ∀ who h, |payoff who h| ≤ bound)
    (accurate : CFRDDepthAccurate M clock fallback payoff cut remaining oracle error)
    (optimal : CFRDDepthLeafOptimal M clock fallback payoff cut remaining oracle loss)
    (reference : Profile M.behavioralSignature)
    (equilibrium : IsNash (M.toBehavioralGameForm (cut + remaining))
      (euPreference (fun h who => payoff who h)) reference)
    (unknown : Profile M.behavioralSignature) (who opponent : Fin 2)
    (different : opponent ≠ who) (t : Nat) [NeZero t]
    (resolver : CarriedPublicResolver M (Fin t))
    (envelope : CFRDResolverEnvelope M
      (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val)
      resolver fallback unknown who opponent cut remaining (payoff opponent) envelopeLoss) :
    (M.runBehavioral reference (cut + remaining)).expect (payoff who) -
      ((cfrDDepthErrorConstant M clock fallback cut remaining who +
          cfrDDepthErrorConstant M clock fallback cut remaining opponent) * error +
        (cfrDDepthFiniteConstant M clock fallback cut remaining bound who +
          cfrDDepthFiniteConstant M clock fallback cut remaining bound opponent) / Real.sqrt t +
        loss + envelopeLoss) ≤
      (privateCarriedResolve M (cfrIterationLaw t)
        (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val)
        resolver unknown who cut remaining).expect (payoff who) := by
  have security := privateCarriedResolve_security_of_envelope M clock hrecall
    (cfrIterationLaw t)
    (fun n : Fin t => cfrDDepthPlay M clock fallback payoff cut remaining oracle n.val)
    resolver fallback unknown who opponent different cut remaining payoff zeroSum
    reference equilibrium
    (cfrDDepthMeanBudget M clock fallback cut remaining bound error loss who t)
    (cfrDDepthMeanBudget M clock fallback cut remaining bound error 0 opponent t)
    envelopeLoss hc
    (cfrDDepth_mean_regret_le M clock hrecall fallback payoff cut remaining oracle
      bound error loss hb he hl bounded accurate optimal who (reference who) t)
    (cfrDDepth_prefix_mean_le M clock hrecall fallback payoff cut remaining oracle
      bound error hb he bounded accurate opponent (unknown opponent) t) envelope
  have ownBound := cfrDDepthMeanBudget_le_constants M clock fallback cut remaining
    bound error loss he who t
  have otherBound := cfrDDepthMeanBudget_le_constants M clock fallback cut remaining
    bound error 0 he opponent t
  rw [add_mul, add_div]
  linarith

end GameTheory.ReBeL
