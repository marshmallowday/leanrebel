/-
# Exhaustive chronological scheduling of canonical decision information sites

The schedule enumerates all legal information sites before the requested cut,
not merely the support of a reference strategy. Equal-depth sites are retained
and ordered by a stable sort; no policy receives the enumeration or a hidden
history. Full action-observation histories supply the required local clock.
-/

import GameTheory.Protocol.BehavioralAssessment
import GameTheory.ReBeL.FiniteSites
import GameTheory.ReBeL.Information
import Mathlib.Data.List.Sort

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- An information-local clock records the number of realized transitions.
This is structural information, not a regret or equilibrium assumption. -/
structure ObservationClock where
  /-- Time is a function of the player's information alone. -/
  depth : (i : ι) → M.InfoState i → ℕ
  /-- Every legal history has its actual trace depth. -/
  correct : ∀ (i : ι) (history : E.History),
    depth i (M.infoOf i history.trace) = history.trace.length

/-- Full AOHs reveal their own length without revealing the hidden state. -/
def fullObservationClock : ObservationClock (fullInformation M) where
  depth _ := AOH.length
  correct i history := length_infoOf M.toInfoSignals i history.trace

/-- Every canonical decision site belongs to the all-history cover. -/
theorem decisionSite_mem_finiteSites [Fintype E.History] (who : ι)
    (site : M.InformationSite who) : site.1 ∈ finiteSites M who := by
  obtain ⟨history, _, _⟩ := site.2
  exact (mem_finiteSites M who _).mpr ⟨history.1, history.2⟩

/-- Only realized decision sites need enumeration; the ambient AOH carrier
may still be infinite. Terminal members of a decision fiber remain present. -/
@[instance_reducible]
def decisionSiteFintype [Fintype E.History] (who : ι) :
    Fintype (M.InformationSite who) := by
  classical
  exact Fintype.ofInjective
    (fun site : M.InformationSite who =>
      (⟨site.1, decisionSite_mem_finiteSites M who site⟩ : finiteSites M who))
    (fun _ _ h => Subtype.ext (congrArg (fun x : finiteSites M who => x.1) h))

/-- The policy-independent list of every genuine decision before the cut,
ordered from shallow to deep. Ties are not collapsed. -/
def scheduledSites [Fintype E.History] (clock : ObservationClock M)
    (horizon : ℕ) (who : ι) : List (M.InformationSite who) := by
  classical
  let := decisionSiteFintype M who
  exact ((Finset.univ.filter fun site : M.InformationSite who =>
    clock.depth who site.1 < horizon).toList).mergeSort
      (fun a b => decide (clock.depth who a.1 ≤ clock.depth who b.1))

/-- Scheduling is exhaustive and does not depend on any strategy's reach. -/
theorem mem_scheduledSites [Fintype E.History] (clock : ObservationClock M)
    (horizon : ℕ) (who : ι) (site : M.InformationSite who) :
    site ∈ scheduledSites M clock horizon who ↔ clock.depth who site.1 < horizon := by
  classical
  let := decisionSiteFintype M who
  simp [scheduledSites]

/-- Each information site appears exactly once, even when depths coincide. -/
theorem scheduledSites_nodup [Fintype E.History] (clock : ObservationClock M)
    (horizon : ℕ) (who : ι) : (scheduledSites M clock horizon who).Nodup := by
  classical
  let := decisionSiteFintype M who
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

/-- All earlier scheduled sites are at an earlier or equal trace depth. -/
theorem scheduledSites_ordered [Fintype E.History] (clock : ObservationClock M)
    (horizon : ℕ) (who : ι) :
    (scheduledSites M clock horizon who).Pairwise
      (fun a b => clock.depth who a.1 ≤ clock.depth who b.1) := by
  classical
  unfold scheduledSites
  simpa only [decide_eq_true_eq] using
    (List.pairwise_mergeSort
      (le := fun a b : M.InformationSite who =>
        decide (clock.depth who a.1 ≤ clock.depth who b.1))
      (fun _ _ _ hab hbc => by
        simpa only [decide_eq_true_eq] using
          Nat.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
      (fun a b => by
        simpa only [Bool.or_eq_true, decide_eq_true_eq] using
          le_total (clock.depth who a.1) (clock.depth who b.1)) _)

/-- Every nonterminal active history before the cut supplies a scheduled
information site, including histories with zero probability under current play. -/
theorem scheduledSites_covers [Fintype E.History] (clock : ObservationClock M)
    (horizon : ℕ) (who : ι) (history : E.History)
    (hbefore : history.trace.length < horizon)
    (hterm : ¬ E.terminal history.state) (hactive : E.active history.state who) :
    ∃ site ∈ scheduledSites M clock horizon who, site.1 = M.infoOf who history.trace := by
  obtain ⟨joint, hjoint⟩ := E.exists_legal hterm
  obtain ⟨action, haction⟩ := LegalOption.exists_eq_some_of_active (joint who)
    (ExecutionProtocol.legalOption_of_legal hjoint who) hactive
  have hmenu : some action ∈ M.menu who (M.infoOf who history.trace) := by
    apply (M.menu_adequate who history.trace _).mpr
    rw [← haction]
    exact ExecutionProtocol.legalOption_of_legal hjoint who
  let site := M.informationSite who history action hterm hmenu
  refine ⟨site, (mem_scheduledSites M clock horizon who site).mpr ?_, rfl⟩
  change clock.depth who (M.infoOf who history.trace) < horizon
  rw [clock.correct]
  exact hbefore

/-- No site is scheduled for a zero-step run. -/
@[simp]
theorem scheduledSites_zero [Fintype E.History] (clock : ObservationClock M)
    (who : ι) : scheduledSites M clock 0 who = [] := by
  classical
  simp [scheduledSites]

end GameTheory.ReBeL
