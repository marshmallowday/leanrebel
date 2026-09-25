/-
# Recomputing a finite information child on the same searched prefix

The actual child table depends on the full joint cut law. Restoring any
continuation after the cut leaves the child, including its zero-own-reach
completion, unchanged. This discharges a same-configuration replay obligation;
it is not a stability theorem for different losses or later carried PBSs.
-/

import GameTheory.Analysis.ReBeL.CFRDInformationSampledDriver
import GameTheory.Analysis.ReBeL.CFRDFreshValueDrift

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- Equal JOINT cut laws give exactly the same finite information-CFR table.
Possible public queries and posterior-dependent iteration budgets agree too. -/
theorem cfrDInformationChildTable_eq_of_prefixLaw
    (first second : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ)
    (same : (fullInformation M).runBehavioral first cut =
      (fullInformation M).runBehavioral second cut) :
    cfrDInformationChildTable M first fallback cut remaining utility bound loss =
      cfrDInformationChildTable M second fallback cut remaining utility bound loss := by
  classical
  funext obs
  have possible : CFRDFactualChildPossible M first cut remaining obs ↔
      CFRDFactualChildPossible M second cut remaining obs := by
    simp only [CFRDFactualChildPossible, same]
  by_cases hp : CFRDFactualChildPossible M first cut remaining obs
  · have hq := possible.mp hp
    simp only [cfrDInformationChildTable, dif_pos hp, dif_pos hq]
    apply congrArg (fun belief =>
      pbsInformationConditionalProfile M belief fallback remaining utility bound loss)
    have ext (a b : PublicBelief (fullInformation M).toInfoSignals obs)
        (equal : a.law = b.law) : a = b := by
      cases a
      cases b
      cases equal
      rfl
    apply ext
    simp only [cfrDFactualChildBelief, same]
  · have hq : ¬ CFRDFactualChildPossible M second cut remaining obs :=
      fun h => hp (possible.mpr h)
    simp only [cfrDInformationChildTable, dif_neg hp, dif_neg hq]

/-- Prefix agreement preserves the complete child profile, not just a scalar
Nash value. Menus beyond the cut are chosen by the identical child table. -/
theorem cfrDInformationChildProfile_eq_of_before
    (first second : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ)
    (same : ∀ who info, (fullObservationClock M).depth who info < cut →
      first who info = second who info) :
    cfrDInformationChildProfile M first fallback cut remaining utility bound loss =
      cfrDInformationChildProfile M second fallback cut remaining utility bound loss := by
  have law := runBehavioral_eq_of_before_depth (fullInformation M) (fullObservationClock M)
    first second cut same
  have table := cfrDInformationChildTable_eq_of_prefixLaw M first second fallback
    cut remaining utility bound loss law
  unfold cfrDInformationChildProfile
  rw [table]
  funext who info
  by_cases before : (fullObservationClock M).depth who info < cut
  · simp only [cfrDDepthProfile, cfrDDepthTrunk, decide_eq_true_eq, if_pos before,
      same who info before]
  · simp only [cfrDDepthProfile, cfrDDepthTrunk, decide_eq_true_eq, if_neg before]

variable [∀ who info, Fintype ((fullInformation M).Choice who info)]

/-- Equality survives computed off-path completion: its reference table and
base child are equal, so no arbitrary best-response selection is substituted. -/
theorem cfrDInformationContinuation_eq_of_before
    (first second : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ)
    (same : ∀ who info, (fullObservationClock M).depth who info < cut →
      first who info = second who info) :
    cfrDInformationContinuation M first fallback cut remaining utility bound loss =
      cfrDInformationContinuation M second fallback cut remaining utility bound loss := by
  unfold cfrDInformationContinuation
  rw [cfrDInformationChildProfile_eq_of_before M first second fallback
    cut remaining utility bound loss same]

/-- Re-solving a restored prefix computes the ORIGINAL child afresh. There
is no equality, small-drift, Nash or child-quality premise on the output. -/
theorem cfrDInformationContinuation_clamp
    (trunk tail : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) :
    cfrDInformationContinuation M
        (cfrDDepthProfile (fullInformation M) (fullObservationClock M) cut trunk tail)
        fallback cut remaining utility bound loss =
      cfrDInformationContinuation M trunk fallback cut remaining utility bound loss := by
  apply cfrDInformationContinuation_eq_of_before
  intro who info before
  simp only [cfrDDepthProfile, cfrDDepthTrunk, decide_eq_true_eq, if_pos before]

/-- Actual retained child-iteration queries are invariant under this replay,
also on reference-supported zero-factual-mass queries. The unknown opponent
is fixed outside the child's private draw; no factual posterior is invented. -/
theorem cfrDInformationQuerySample_clamp
    (trunk tail : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ)
    (who : Fin 2) (info : (fullInformation M).InfoState who)
    (sampled : CFRDInformationQuerySampled M trunk fallback cut remaining who info)
    (unknown : Profile (fullInformation M).behavioralSignature) (steps : Nat) :
    cfrDInformationQuerySample M
        (cfrDDepthProfile (fullInformation M) (fullObservationClock M) cut trunk tail)
        fallback cut remaining utility bound loss who info unknown steps =
      cfrDInformationQuerySample M trunk fallback cut remaining utility bound loss
        who info unknown steps := by
  have supported : CFRDInformationQuerySampled M
      (cfrDDepthProfile (fullInformation M) (fullObservationClock M) cut trunk tail)
      fallback cut remaining who info := by
    simpa only [CFRDInformationQuerySampled, cfrDDepthProfile_referenceLaw] using sampled
  rw [cfrDInformationQuerySample_law M _ fallback cut remaining utility bound loss
      who info supported unknown steps,
    cfrDInformationQuerySample_law M trunk fallback cut remaining utility bound loss
      who info sampled unknown steps, cfrDInformationContinuation_clamp]
  simp only [cfrDInformationQueryLaw, cfrDDepthProfile_referenceLaw]

variable [∀ who, DecidableEq ((fullInformation M).InfoState who)]

/-- At EVERY actual noisy parent iteration, a same-setting recomputation
returns exactly that round's continuation. The learned trunk is not frozen to
an unrelated sequence and prediction noise is not required to vanish. -/
theorem cfrDConstructedSampledInformationOracle_replay
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (cut remaining : Nat) (bound loss : ℝ) (noise : CFRDPredictionNoise M) (n : Nat) :
    cfrDInformationContinuation M
        (cfrDDepthPlay (fullInformation M) (fullObservationClock M)
          (cfrDInformationFallback M fallback) payoff cut remaining
          (cfrDConstructedSampledInformationOracle M fallback payoff cut remaining
            bound loss noise) n)
        fallback cut remaining (fun h who => payoff who h) bound loss =
      (cfrDDepthQuery (fullInformation M) (fullObservationClock M)
        (cfrDInformationFallback M fallback) payoff cut remaining
        (cfrDConstructedSampledInformationOracle M fallback payoff cut remaining
          bound loss noise) n).continuation := by
  rw [cfrDDepthPlay_eq]
  exact cfrDInformationContinuation_clamp M _ _ fallback cut remaining
    (fun h who => payoff who h) bound loss

end GameTheory.ReBeL
