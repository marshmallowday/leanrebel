/-
# Actual child-iteration sampling at each supported original root

Complete histories retain their unique prefix at the public cut. This
proof-only readout separates the root mixture, so its equality implies
kernel equality at each positive-mass root. The deployed policies still
read only their own AOH; the prefix readout is never a policy argument.
Reweighting supported roots need not preserve the model probabilities.
-/

import GameTheory.Analysis.ReBeL.PBSInformationSampling

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

private theorem sampled_bind_prob_at_root {A B : Type*} [Fintype A]
    (law : FinDist A) (kernel : A → FinDist B) (read : B → A)
    (preserves : ∀ root ∈ law.support, ∀ result ∈ (kernel root).support, read result = root)
    (root : A) (result : B) (same : read result = root) :
    (law.bind kernel).prob result = law.prob root * (kernel root).prob result := by
  classical
  rw [FinDist.prob_bind, FinDist.expect_eq_sum]
  apply Finset.sum_eq_single root
  · intro other _ different
    by_cases supported : other ∈ law.support
    · have impossible : result ∉ (kernel other).support := by
        intro member
        exact different ((preserves other supported result member).symm.trans same)
      rw [FinDist.prob_eq_zero_iff.mpr impossible, mul_zero]
    · rw [FinDist.prob_eq_zero_iff.mpr supported, zero_mul]
  · intro absent
    exact False.elim (absent (Finset.mem_univ root))

private theorem sampled_bind_injective_at_root {A B : Type*} [Fintype A]
    (law : FinDist A) (first second : A → FinDist B) (read : B → A)
    (firstPreserves :
      ∀ root ∈ law.support, ∀ result ∈ (first root).support, read result = root)
    (secondPreserves :
      ∀ root ∈ law.support, ∀ result ∈ (second root).support, read result = root)
    (equal : law.bind first = law.bind second) (root : A) (supported : root ∈ law.support) :
    first root = second root := by
  classical
  have nonzero : law.prob root ≠ 0 := by
    intro zero
    exact (FinDist.prob_eq_zero_iff.mp zero) supported
  apply FinDist.ext_of_prob
  intro result
  by_cases same : read result = root
  · apply mul_left_cancel₀ nonzero
    calc
      law.prob root * (first root).prob result = (law.bind first).prob result :=
        (sampled_bind_prob_at_root law first read firstPreserves root result same).symm
      _ = (law.bind second).prob result := congrArg (fun distribution =>
        distribution.prob result) equal
      _ = law.prob root * (second root).prob result :=
        sampled_bind_prob_at_root law second read secondPreserves root result same
  · have firstZero : (first root).prob result = 0 :=
      FinDist.prob_eq_zero_iff.mpr (fun member =>
        same (firstPreserves root supported result member))
    have secondZero : (second root).prob result = 0 :=
      FinDist.prob_eq_zero_iff.mpr (fun member =>
        same (secondPreserves root supported result member))
    exact firstZero.trans secondZero.symm

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}

/-- Canonical original prefix at the cut, used only to separate mixture fibers.
Earlier terminal histories are retained rather than assigned a fabricated root. -/
def pbsSamplingPrefix (cut : Nat) : {state : E.State} → E.Trace state → E.History
  | _, .start => E.initHistory
  | _, .extend prior joint legal realized =>
      if prior.length < cut then ⟨_, .extend prior joint legal realized⟩
      else pbsSamplingPrefix cut prior

/-- Reading exactly the depth of a legal trace recovers the same history. -/
theorem pbsSamplingPrefix_self {state : E.State} (trace : E.Trace state) :
    pbsSamplingPrefix trace.length trace = (⟨state, trace⟩ : E.History) := by
  cases trace with
  | start => rfl
  | extend prior joint legal realized =>
      simp only [pbsSamplingPrefix, Trace.length, Nat.lt_succ_self, if_true]

/-- No legal continuation after the cut can alter the remembered root prefix. -/
theorem pbsSamplingPrefix_reaches {fuel : Nat} {first last : E.History}
    (reaches : E.ReachesWithin fuel first last) (cut : Nat)
    (before : cut ≤ first.trace.length) :
    pbsSamplingPrefix cut last.trace = pbsSamplingPrefix cut first.trace := by
  revert before
  induction reaches with
  | refl => intro _; rfl
  | step joint legal realized rest ih =>
      intro before
      have next := ih (by
        simpa only [History.extend, Trace.length] using Nat.le_succ_of_le before)
      simpa only [History.extend, pbsSamplingPrefix,
        if_neg (Nat.not_lt.mpr before)] using next

variable (M : InformationModel.{0, us, ua, up, uq, uk} E)

private theorem pbsSamplingPrefix_behavioral
    (profile : Profile M.behavioralSignature) (cut fuel : Nat) (first last : E.History)
    (atCut : first.trace.length = cut)
    (supported : last ∈ (M.runBehavioralFrom profile fuel first).support) :
    pbsSamplingPrefix cut last.trace = first := by
  have reaches := behavioral_support_reaches M profile fuel first last supported
  have same := pbsSamplingPrefix_reaches reaches cut (by omega)
  exact same.trans (by rw [← atCut]; exact pbsSamplingPrefix_self first.trace)

variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {observations : List M.PublicSignal}

/-- Any realized mixture of legal profiles agrees pointwise on the model's
supported roots when its complete model-root law agrees with a single profile.
The proof uses retained history prefixes, not equality of actual/model weights.
Concrete solvers must prove the model-law premise from their own recurrence. -/
theorem pbsPublicBelief_sampling_from_support {K : Type*}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (law : FinDist K) (profiles : K → Profile (fullInformation M).behavioralSignature)
    (average : Profile (fullInformation M).behavioralSignature) (steps : Nat)
    (equal : belief.law.bind (fun history => law.bind (fun k =>
        (fullInformation M).runBehavioralFrom (profiles k) steps history)) =
      belief.law.bind ((fullInformation M).runBehavioralFrom average steps))
    (history : E.History) (supported : history ∈ belief.law.support) :
    law.bind (fun k => (fullInformation M).runBehavioralFrom (profiles k) steps history) =
      (fullInformation M).runBehavioralFrom average steps history := by
  refine sampled_bind_injective_at_root belief.law _ _
    (fun result => pbsSamplingPrefix (observations.length - 1) result.trace)
    ?_ ?_ equal history supported
  · intro first atRoot last inLaw
    rw [FinDist.support_bind] at inLaw
    simp only [Set.mem_iUnion] at inLaw
    obtain ⟨k, _, realized⟩ := inLaw
    exact pbsSamplingPrefix_behavioral (fullInformation M) _ _ steps first last
      (pbsRoot_publicBelief_depth M belief first atRoot) realized
  · intro first atRoot last realized
    exact pbsSamplingPrefix_behavioral (fullInformation M) _ _ steps first last
      (pbsRoot_publicBelief_depth M belief first atRoot) realized

/-- A private draw of the computed child's actual iteration, starting from an
arbitrary legal original history. The model belief still determines the solver. -/
def pbsInformationCFRSampleFrom
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) (history : E.History) : FinDist E.History :=
  (cfrIterationLaw t).bind (fun n => (fullInformation M).runBehavioralFrom
    (Profile.update unknown who (pbsInformationCFRIterate M belief fallback payoff
      fuel n.val who)) steps history)

/-- Mixture equality strengthens to every supported original root because
complete output histories preserve distinct same-depth prefixes. No positive
uniform mass floor, conditional value certificate or opponent model is supplied. -/
theorem pbsInformationCFR_sampling_from_support
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) (history : E.History) (supported : history ∈ belief.law.support) :
    pbsInformationCFRSampleFrom M belief fallback payoff fuel t unknown who steps history =
      (fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFR M belief fallback payoff fuel t who))
        steps history := by
  exact pbsPublicBelief_sampling_from_support M belief (cfrIterationLaw t)
    (fun n => Profile.update unknown who
      (pbsInformationCFRIterate M belief fallback payoff fuel n.val who))
    (Profile.update unknown who (pbsInformationCFR M belief fallback payoff fuel t who)) steps
    (pbsInformationCFR_delayed_sampling M belief fallback payoff fuel t unknown who steps)
    history supported

/-- Any reweighting or conditioning within the model support preserves the
same sampled law. Actual root probabilities need not equal model probabilities. -/
theorem pbsInformationCFR_sampling_reweighted
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) (actual : FinDist E.History)
    (dominated : ∀ history ∈ actual.support, history ∈ belief.law.support) :
    actual.bind (pbsInformationCFRSampleFrom M belief fallback payoff fuel t unknown who steps) =
      actual.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFR M belief fallback payoff fuel t who))
        steps) := by
  apply FinDist.bind_congr
  intro history sampled
  exact pbsInformationCFR_sampling_from_support M belief fallback payoff fuel t unknown who
    steps history (dominated history sampled)

/-- The conditional value consumer uses the same sampled family on any
supported root law. Zero-model-support histories remain outside this theorem. -/
theorem pbsInformationCFR_sampling_reweighted_value
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (fuel t : Nat) [NeZero t]
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) (actual : FinDist E.History)
    (dominated : ∀ history ∈ actual.support, history ∈ belief.law.support)
    (value : E.History → ℝ) :
    (actual.bind
      (pbsInformationCFRSampleFrom M belief fallback payoff fuel t unknown who steps)).expect
        value =
      (actual.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who (pbsInformationCFR M belief fallback payoff fuel t who))
        steps)).expect value :=
  congrArg (fun law : FinDist E.History => law.expect value)
    (pbsInformationCFR_sampling_reweighted M belief fallback payoff fuel t unknown who
      steps actual dominated)

end GameTheory.ReBeL
