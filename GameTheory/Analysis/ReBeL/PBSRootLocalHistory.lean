/-
# Reconstructing rooted information from an original local history

A common public cut fixes the original root depth. The rooted local sequence
can then be reconstructed from one player's original full AOH alone. No hidden
root, opponent observation, realization witness or joint action is an input to
this readout. Mixed-depth roots are deliberately not asserted equivalent.
-/

import GameTheory.Analysis.ReBeL.PBSRootInformation
import GameTheory.Analysis.ReBeL.PBSFullAOH

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk

namespace AOH

variable {Action : Type ua} {Private : Type uq} {Public : Type up}

/-- The local record of the administrative chance draw, with no player action. -/
def rootedSnapshot (info : AOH Action Private Public) :
    AOH Action (Option (AOH Action Private Public)) (Option (List Public)) :=
  .step (.initial none none) none (some info) (some info.publicHistory)

/-- Reconstruct the subsequent sequence at a fixed public cut depth. Before
that depth the total readout uses a legal snapshot, not a fabricated world. -/
def rootedAt (cut : Nat) : AOH Action Private Public →
    AOH Action (Option (AOH Action Private Public)) (Option (List Public))
  | .initial privateObservation publicObservation =>
      rootedSnapshot (.initial privateObservation publicObservation)
  | .step prior action privateObservation publicObservation =>
      let current := AOH.step prior action privateObservation publicObservation
      if prior.length < cut then rootedSnapshot current else
        .step (rootedAt cut prior) action (some current) (some current.publicHistory)

/-- At the cut there is exactly one administrative observation. -/
theorem rootedAt_eq_snapshot_of_length_le (cut : Nat) (info : AOH Action Private Public)
    (before : info.length ≤ cut) : info.rootedAt cut = info.rootedSnapshot := by
  cases info with
  | initial => rfl
  | step prior action privateObservation publicObservation =>
      have earlier : prior.length < cut := by
        simp only [length] at before
        omega
      simp only [rootedAt, if_pos earlier]

/-- Every original step after the cut appends exactly its own action and view. -/
theorem rootedAt_step (cut : Nat) (prior : AOH Action Private Public)
    (afterCut : cut ≤ prior.length) (action : Option Action)
    (privateObservation : Private) (publicObservation : Public) :
    (AOH.step prior action privateObservation publicObservation).rootedAt cut =
      .step (prior.rootedAt cut) action
        (some (.step prior action privateObservation publicObservation))
        (some (AOH.step prior action privateObservation publicObservation).publicHistory) := by
  simp only [rootedAt, if_neg (Nat.not_lt.mpr afterCut)]

end AOH

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- The reconstructed sequence always ends in the same original local snapshot.
This proves menu preservation even for syntactic, off-policy AOH inputs. -/
theorem pbsRootLocalHistory_read (roots : FinDist E.History) (who : ι) (cut : Nat)
    (info : (fullInformation M).InfoState who) :
    reduceAOH (pbsRootInformation (fullInformation M) roots).toInfoSignals who
      (info.rootedAt cut) = some info := by
  cases info with
  | initial => rfl
  | step prior action privateObservation publicObservation =>
      dsimp only [AOH.rootedAt]
      split <;> rfl

/-- Every true public belief is concentrated on a common original depth.
No positivity floor or independence between private observations is used. -/
theorem pbsRoot_publicBelief_depth {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (history : E.History) (supported : history ∈ belief.law.support) :
    history.trace.length = observations.length - 1 := by
  have length := publicTrace_length (fullInformation M).toInfoSignals history.trace
  rw [belief.supported history supported] at length
  omega

/-- At every legal rooted trace, local reconstruction is exact. The statement
covers all legal transitions, not only the support of one chosen policy. -/
theorem pbsRootLocalHistory_trace (roots : FinDist E.History) (cut : Nat)
    (rootDepth : ∀ history ∈ roots.support, history.trace.length = cut) (who : ι)
    {state : (pbsRootProtocol roots).State} (trace : (pbsRootProtocol roots).Trace state) :
    match state with
    | none => (fullInformation (pbsRootInformation (fullInformation M) roots)).infoOf who trace =
        AOH.initial none none
    | some original => cut ≤ original.trace.length ∧
        (fullInformation (pbsRootInformation (fullInformation M) roots)).infoOf who trace =
          ((fullInformation M).infoOf who original.trace).rootedAt cut := by
  induction trace with
  | start => rfl
  | @extend source target prior joint legal realized ih =>
      cases source with
      | none =>
          obtain ⟨original, supported, rfl⟩ :=
            (pbsRootProtocol_step_none_support roots ⟨joint, legal⟩ target).mp realized
          have depth := rootDepth original supported
          have idle : joint who = none := by
            have localLegal := (pbsRootProtocol roots).legalOption_of_legal legal who
            cases choice : joint who with
            | none => rfl
            | some action =>
                rw [choice] at localLegal
                exact localLegal.1.elim
          refine ⟨by omega, ?_⟩
          rw [AOH.rootedAt_eq_snapshot_of_length_le cut _ (by
            rw [length_infoOf, depth])]
          have stepEquation : AOH.step
            ((fullInformation (pbsRootInformation (fullInformation M) roots)).infoOf who prior)
            (joint who) (some ((fullInformation M).infoOf who original.trace))
            (some (publicTrace (fullInformation M).toInfoSignals original.trace)) =
              AOH.rootedSnapshot ((fullInformation M).infoOf who original.trace) := by
            rw [ih, idle, publicRoot_trace_eq M original.trace]
            simp only [AOH.rootedSnapshot, publicHistory_infoOf]
          exact stepEquation
      | some original =>
          obtain ⟨next, hnext, rfl⟩ :=
            (pbsRootProtocol_step_support roots original ⟨joint, legal⟩ target).mp realized
          obtain ⟨afterCut, priorInfo⟩ := ih
          refine ⟨by simpa only [History.extend, Trace.length] using
            Nat.le_succ_of_le afterCut, ?_⟩
          have stepRead := AOH.rootedAt_step cut
            ((fullInformation M).infoOf who original.trace)
            (by simpa only [length_infoOf] using afterCut) (joint who)
            (M.privateSignal who ⟨_, joint, legal, next, hnext⟩)
            (M.publicSignal ⟨_, joint, legal, next, hnext⟩)
          have currentRead :
              ((fullInformation M).infoOf who (original.extend legal hnext).trace).rootedAt cut =
                AOH.step (((fullInformation M).infoOf who original.trace).rootedAt cut)
                  (joint who) (some ((fullInformation M).infoOf who
                    (original.extend legal hnext).trace))
                  (some (((fullInformation M).infoOf who
                    (original.extend legal hnext).trace).publicHistory)) := stepRead
          have stepEquation : AOH.step
            ((fullInformation (pbsRootInformation (fullInformation M) roots)).infoOf who prior)
            (joint who) (some ((fullInformation M).infoOf who
              (original.extend legal hnext).trace))
            (some (publicTrace (fullInformation M).toInfoSignals
              (original.extend legal hnext).trace)) =
              ((fullInformation M).infoOf who
                (original.extend legal hnext).trace).rootedAt cut := by
            rw [currentRead, priorInfo,
              publicRoot_trace_eq M (original.extend legal hnext).trace,
              publicHistory_infoOf M.toInfoSignals who (original.extend legal hnext).trace]
          exact stepEquation

end GameTheory.ReBeL
