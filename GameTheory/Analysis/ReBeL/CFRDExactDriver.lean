/-
# A constructed exact continuation oracle in the actual CFR-D recurrence

Each queried trunk supplies its own factual child games and counterfactual
completion. The driver restores that trunk and uses conditional predictions
from the same completed continuation. Both numerical accuracy and local leaf
optimality are derived for every actual iteration, not provided as certificates.
The child solve is noncomputable exact Nash, not finite-T recursive CFR.
-/

import GameTheory.Analysis.ReBeL.CFRDFactualMixture
import GameTheory.Analysis.ReBeL.CFRDClamp

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι] [DecidableEq ι] [Fintype E.History]
variable [∀ who, Fintype (E.Action who)]
variable [∀ who info, Fintype ((fullInformation M).Choice who info)]

/-- Construct exact factual child Nash and the compatible off-path response.
No continuation policy, posterior or local optimality inequality is an input. -/
def cfrDExactContinuation (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) : Profile (fullInformation M).behavioralSignature :=
  let base := cfrDFactualChildProfile M trunk fallback cut remaining utility
  cfrDCompleteZeroReach (fullInformation M) base
    (cfrDPublicResponseCompletion M cut (cfrDReferenceTable M base fallback cut remaining)
      fallback remaining utility base)

/-- The completion retains the original trunk's entire unilateral cut law. -/
theorem cfrDExactContinuation_referenceLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) (who : ι) :
    unilateralReferenceLaw (fullInformation M)
        (cfrDExactContinuation M trunk fallback cut remaining utility) fallback who cut =
      unilateralReferenceLaw (fullInformation M) trunk fallback who cut := by
  unfold cfrDExactContinuation
  rw [cfrDCompleteZeroReach_referenceLaw (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals), cfrDFactualChildProfile_referenceLaw]

/-- The constructed exact continuation is optimal on every supported live
reference information fiber, including types of zero factual own reach. -/
theorem cfrDExactContinuation_leafOptimal
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) (who : ι) :
    CFRDLeafOptimal (fullInformation M)
      (cfrDExactContinuation M trunk fallback cut remaining utility)
      fallback who (fun h => utility h who) cut remaining 0 :=
  cfrDFactualChildProfile_completed_leafOptimal M trunk fallback cut remaining utility who

variable [∀ who, DecidableEq ((fullInformation M).InfoState who)]

/-- The actual stopped-backup driver receives a constructed response at its
current trunk, with exact conditional values from that same response. -/
def cfrDConstructedExactOracle (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) :
    CFRDValueOracle (fullInformation M) :=
  cfrDExactValueOracle (fullInformation M) (fullObservationClock M) fallback payoff cut remaining
    (fun _ trunk => cfrDExactContinuation M trunk fallback cut remaining
      (fun history who => payoff who history))

/-- Numerical accuracy is derived for the oracle's own coupled update sequence. -/
theorem cfrDConstructedExactOracle_accurate
    (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) :
    CFRDDepthAccurate (fullInformation M) (fullObservationClock M) fallback payoff cut remaining
      (cfrDConstructedExactOracle M fallback payoff cut remaining) 0 :=
  cfrDExactValueOracle_accurate (fullInformation M) (fullObservationClock M)
    fallback payoff cut remaining _

/-- Restoring the learned trunk preserves the constructed leaf contract.
This discharges continuation optimality at EVERY actual round of CFR-D,
without assuming any Nash, query identity or continuation-quality certificate. -/
theorem cfrDConstructedExactOracle_leafOptimal
    (fallback : Profile (fullInformation M).strategicSignature)
    (payoff : ι → E.History → ℝ) (cut remaining : Nat) :
    CFRDDepthLeafOptimal (fullInformation M) (fullObservationClock M) fallback payoff cut remaining
      (cfrDConstructedExactOracle M fallback payoff cut remaining) 0 := by
  intro n who
  rw [cfrDDepthPlay_eq]
  apply cfrDDepthProfile_leafOptimal
  · exact cfrDExactContinuation_referenceLaw M _ fallback cut remaining
      (fun history player => payoff player history) who
  · exact cfrDExactContinuation_leafOptimal M _ fallback cut remaining
      (fun history player => payoff player history) who

end GameTheory.ReBeL
