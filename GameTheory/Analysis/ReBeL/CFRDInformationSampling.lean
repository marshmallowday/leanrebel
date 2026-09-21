/-
# The parent's actual information-set child as a private iteration draw

The factual joint posterior determines the positive finite child count.
Sampling an actual decoded child iterate gives the same unilateral law as
the parent's public-prefix-spliced child policy. This result keeps the model
root law explicit; no off-model or zero-own-reach safety is inferred from it.
-/

import GameTheory.Analysis.ReBeL.PBSInformationSampling
import GameTheory.Analysis.ReBeL.CFRDInformationChild

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {observations : List M.PublicSignal}

/-- The exact positive count used by the existing conditional child solver. -/
abbrev pbsInformationConditionalRounds
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fuel : Nat) (bound loss : ℝ) : Nat :=
  pbsInformationBudgetRounds M belief.law (fun _ => bound) fuel
    (belief.law.positiveMassFloor * loss)

/-- Sample a private index from the actual finite child recurrence, then
retain that decoded policy for the entire continuation against fixed opponents. -/
def pbsInformationConditionalSample
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) : FinDist E.History :=
  (cfrIterationLaw (pbsInformationConditionalRounds M belief fuel bound loss)).bind
    (fun n => belief.law.bind ((fullInformation M).runBehavioralFrom
      (Profile.update unknown who (pbsInformationCFRIterate M belief fallback
        (fun player h => utility h player) fuel n.val who)) steps))

/-- The computed posterior-dependent draw has exactly the law of the existing
conditional output. Semantic equality does not require a positive error budget. -/
theorem pbsInformationConditionalSample_eq
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) :
    pbsInformationConditionalSample M belief fallback fuel utility bound loss unknown who steps =
      belief.law.bind ((fullInformation M).runBehavioralFrom
        (Profile.update unknown who
          (pbsInformationConditionalProfile M belief fallback fuel utility bound loss who))
        steps) :=
  pbsInformationCFR_sampling_law M belief fallback (fun player h => utility h player) fuel
    (pbsInformationConditionalRounds M belief fuel bound loss) unknown who steps

/-- The selected child's public table entry and its sampled actual iterations
have the same complete continuation law at the factual posterior. -/
theorem cfrDInformationChildTable_sampling
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) :
    pbsInformationConditionalSample M (cfrDFactualChildBelief M trunk cut remaining obs possible)
        fallback remaining utility bound loss unknown who steps =
      (cfrDFactualChildBelief M trunk cut remaining obs possible).law.bind
        ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who
            (cfrDInformationChildTable M trunk fallback cut remaining utility bound loss obs who))
          steps) := by
  simp only [pbsInformationConditionalSample_eq, cfrDInformationChildTable, dif_pos possible]

/-- The actual parent-spliced child policy has that same sampled law. Only the
deploying player's policy changes; arbitrary unknown opponents are held fixed. -/
theorem cfrDInformationChildProfile_sampling
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) :
    pbsInformationConditionalSample M (cfrDFactualChildBelief M trunk cut remaining obs possible)
        fallback remaining utility bound loss unknown who steps =
      (cfrDFactualChildBelief M trunk cut remaining obs possible).law.bind
        ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who
            (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss who))
          steps) := by
  rw [cfrDInformationChildTable_sampling M trunk fallback cut remaining
    utility bound loss obs possible unknown who steps]
  apply FinDist.bind_congr
  intro first supported
  have rootPublic :=
    (cfrDFactualChildBelief M trunk cut remaining obs possible).supported first supported
  rw [publicRoot_trace_eq] at rootPublic
  apply (fullInformation M).runBehavioralFrom_congr
  intro later reaches _ player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    symm
    simpa only [rootPublic] using cfrDInformationChildProfile_of_reaches M trunk fallback cut
      remaining utility bound loss who first later
      (cfrDFactualChildBelief_atCut M trunk cut remaining obs possible first supported) reaches
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]

/-- All original-history observables agree, so parent value consumers can use
the same sampled iteration family rather than an unrelated child value witness. -/
theorem cfrDInformationChildProfile_sampling_value
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile M.strategicSignature) (cut remaining : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) (obs : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining obs)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : Fin 2)
    (steps : Nat) (value : E.History → ℝ) :
    (pbsInformationConditionalSample M
      (cfrDFactualChildBelief M trunk cut remaining obs possible)
      fallback remaining utility bound loss unknown who steps).expect value =
      ((cfrDFactualChildBelief M trunk cut remaining obs possible).law.bind
        ((fullInformation M).runBehavioralFrom
          (Profile.update unknown who
            (cfrDInformationChildProfile M trunk fallback cut remaining utility bound loss who))
          steps)).expect value :=
  congrArg (fun law : FinDist E.History => law.expect value)
    (cfrDInformationChildProfile_sampling M trunk fallback cut remaining
      utility bound loss obs possible unknown who steps)

end GameTheory.ReBeL
