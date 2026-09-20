/-
# Information-local public-state splicing at a fixed cut

The child table is selected by the public part of the player's remembered
cut prefix, not by its latest public observation or any hidden state. Every
legal descendant keeps that table, including paths of zero policy reach.
This is a continuation constructor, not an equilibrium or quality oracle.
-/

import GameTheory.Analysis.ReBeL.CFRDCompletedContract
import GameTheory.Analysis.ReBeL.PBSFullAOH

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Select one complete legal response using only the public cut prefix.
Each selected response still reads the player's entire current local AOH. -/
def cfrDPublicContinuation (cut : Nat)
    (responses : List M.PublicSignal → Profile (fullInformation M).behavioralSignature) :
    Profile (fullInformation M).behavioralSignature := fun who info =>
  responses (info.prefixAt cut).publicHistory who info

/-- The same public response is used throughout every legal continuation
from the cut, not only along trajectories of positive current probability. -/
theorem cfrDPublicContinuation_eq_of_reaches (cut : Nat)
    (responses : List M.PublicSignal → Profile (fullInformation M).behavioralSignature)
    (who : ι) (first later : E.History) (atCut : first.trace.length = cut)
    {fuel : Nat} (reaches : E.ReachesWithin fuel first later) :
    cfrDPublicContinuation M cut responses who ((fullInformation M).infoOf who later.trace) =
      responses (publicTrace M.toInfoSignals first.trace) who
        ((fullInformation M).infoOf who later.trace) := by
  unfold cfrDPublicContinuation
  rw [prefixAt_infoOf_reaches M cut who reaches (by omega),
    AOH.prefixAt_eq_of_length_le cut _ (by rw [length_infoOf, atCut]), publicHistory_infoOf]

variable [Fintype ι]

/-- The whole canonical continuation law agrees with that public root's
selected response, including all players' independent behavioral draws. -/
theorem cfrDPublicContinuation_runFrom (cut : Nat)
    (responses : List M.PublicSignal → Profile (fullInformation M).behavioralSignature)
    (first : E.History) (atCut : first.trace.length = cut) (fuel : Nat) :
    (fullInformation M).runBehavioralFrom (cfrDPublicContinuation M cut responses) fuel first =
      (fullInformation M).runBehavioralFrom
        (responses (publicTrace M.toInfoSignals first.trace)) fuel first := by
  apply (fullInformation M).runBehavioralFrom_congr
  intro later reaches _ who
  exact cfrDPublicContinuation_eq_of_reaches M cut responses who first later atCut reaches

/-- Splicing preserves the full joint-belief continuation, without replacing
correlated hidden histories by a product of private marginals. -/
theorem cfrDPublicContinuation_beliefLaw (cut : Nat)
    (responses : List M.PublicSignal → Profile (fullInformation M).behavioralSignature)
    {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (atCut : ∀ history ∈ belief.law.support, history.trace.length = cut) (fuel : Nat) :
    PublicBelief.continuationLaw (fullInformation M)
        (cfrDPublicContinuation M cut responses) fuel belief =
      PublicBelief.continuationLaw (fullInformation M) (responses observations) fuel belief := by
  apply FinDist.bind_congr
  intro history supported
  have public := belief.supported history supported
  rw [publicRoot_trace_eq] at public
  simpa only [public] using
    cfrDPublicContinuation_runFrom M cut responses history (atCut history supported) fuel

variable [DecidableEq ι]

/-- Every fixed unknown opponent sees the same continuation law. Only the
focal player's policy is spliced; no opponent reads its private memory. -/
theorem cfrDPublicContinuation_unilateral_runFrom (cut : Nat)
    (responses : List M.PublicSignal → Profile (fullInformation M).behavioralSignature)
    (unknown : Profile (fullInformation M).behavioralSignature) (who : ι)
    (first : E.History) (atCut : first.trace.length = cut) (fuel : Nat) :
    (fullInformation M).runBehavioralFrom
        (Profile.update unknown who (cfrDPublicContinuation M cut responses who)) fuel first =
      (fullInformation M).runBehavioralFrom
        (Profile.update unknown who (responses (publicTrace M.toInfoSignals first.trace) who))
        fuel first := by
  apply (fullInformation M).runBehavioralFrom_congr
  intro later reaches _ player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    exact cfrDPublicContinuation_eq_of_reaches M cut responses who first later atCut reaches
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]

end GameTheory.ReBeL
