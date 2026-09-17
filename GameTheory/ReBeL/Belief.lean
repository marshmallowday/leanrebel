/-
# Public beliefs as supported joint history laws

The reference semantics is a joint law on canonical histories. No independence
between private observations is assumed. Zero-probability observations have no
posterior; an internal total conditional is only used at sampled observations.
-/

import GameTheory.ReBeL.Information

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability Classical

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

/-- A joint history law supported at the named public history. -/
structure PublicBelief (S : InfoSignals E) (observations : List S.PublicSignal) where
  law : FinDist E.History
  supported : ∀ h ∈ law.support, publicTrace S h.trace = observations

namespace PublicBelief

variable {S : InfoSignals E} {observations : List S.PublicSignal}

/-- A possible public observation meets the actual joint-law support. -/
def Possible (law : FinDist E.History) (observations : List S.PublicSignal) : Prop :=
  ∃ h, publicTrace S h.trace = observations ∧ h ∈ law.support

/-- The public observation law is a pushforward, not an individual Bayes belief. -/
def publicLaw (law : FinDist E.History) : FinDist (List S.PublicSignal) :=
  law.map fun h => publicTrace S h.trace

theorem possible_iff_mem_publicLaw (law : FinDist E.History)
    (observations : List S.PublicSignal) :
    Possible (S := S) law observations ↔ observations ∈ (publicLaw (S := S) law).support := by
  rw [publicLaw, FinDist.support_map]
  exact ⟨fun ⟨h, heq, hs⟩ => ⟨h, hs, heq⟩, fun ⟨h, hs, heq⟩ => ⟨h, heq, hs⟩⟩

/-- Bayes conditioning with an explicit positive-support witness. -/
def condition (law : FinDist E.History) (observations : List S.PublicSignal)
    (possible : Possible (S := S) law observations) : PublicBelief S observations where
  law := law.condOn {h | publicTrace S h.trace = observations}
    (by obtain ⟨h, heq, hs⟩ := possible; exact ⟨h, heq, hs⟩)
  supported h hh := (FinDist.support_condOn _ _ _ hh).1

/-- There is no certified posterior for an impossible observation. -/
def condition? (law : FinDist E.History) (observations : List S.PublicSignal) :
    Option (PublicBelief S observations) := by
  classical
  exact if possible : Possible (S := S) law observations then
    some (condition law observations possible) else none

@[simp]
theorem condition?_eq_none (law : FinDist E.History)
    (observations : List S.PublicSignal) :
    condition? law observations = none ↔ ¬ Possible (S := S) law observations := by
  classical
  unfold condition?
  split_ifs <;> simp_all

theorem prob_condition (law : FinDist E.History) (observations : List S.PublicSignal)
    (possible : Possible (S := S) law observations) (h : E.History) :
    (condition law observations possible).law.prob h =
      if publicTrace S h.trace = observations then
        law.prob h / law.probOf {k | publicTrace S k.trace = observations} else 0 := by
  classical
  by_cases hp : publicTrace S h.trace = observations <;>
    simp [condition, FinDist.prob_condOn, hp]

/-- Conditioning an already-supported PBS on its public history does nothing. -/
theorem condition_self (belief : PublicBelief S observations) :
    (condition belief.law observations (by
      obtain ⟨h, hh⟩ := belief.law.support_nonempty
      exact ⟨h, belief.supported h hh, hh⟩)).law = belief.law := by
  exact FinDist.condOn_of_support_subset belief.law _
    (by obtain ⟨h, hh⟩ := belief.law.support_nonempty
        exact ⟨h, belief.supported h hh, hh⟩) belief.supported

/-- Package the posterior only for a public observation with positive mass. -/
def atObservation (law : FinDist E.History) (observations : List S.PublicSignal)
    (positive : observations ∈ (publicLaw (S := S) law).support) :
    PublicBelief S observations :=
  condition law observations ((possible_iff_mem_publicLaw law observations).mpr positive)

/-- The total internal conditional agrees with the certified one on all sampled branches. -/
theorem atObservation_law (law : FinDist E.History) (observations : List S.PublicSignal)
    (positive : observations ∈ (publicLaw (S := S) law).support) :
    (atObservation law observations positive).law =
      law.condOnFibre (fun h => publicTrace S h.trace) observations := by
  classical
  have possible := (possible_iff_mem_publicLaw law observations).mpr positive
  unfold FinDist.condOnFibre
  rw [dif_pos (show ∃ h ∈ (fun h : E.History => publicTrace S h.trace) ⁻¹' {observations},
      h ∈ law.support from possible)]
  rfl

/-- Publicly sample a state and retain its certified joint posterior. -/
def split (law : FinDist E.History) : FinDist (Σ p, PublicBelief S p) :=
  (publicLaw (S := S) law).bindOnSupport fun p hp =>
    FinDist.pure ⟨p, atObservation law p hp⟩

/-- Sampling a public state and its hidden history recovers exactly the original law. -/
theorem split_bind_law (law : FinDist E.History) :
    (split (S := S) law).bind (fun belief => belief.2.law) = law := by
  rw [split, FinDist.bind_bindOnSupport]
  simp only [FinDist.pure_bind]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (fun p hp => atObservation_law law p hp)]
  exact (FinDist.eq_bind_condOnFibre law (fun h => publicTrace S h.trace)).symm

/-- Every continuation kernel commutes with the public split, not only the identity kernel. -/
theorem split_bind_continuation {Outcome : Type*} (law : FinDist E.History)
    (continuation : E.History → FinDist Outcome) :
    (split (S := S) law).bind (fun belief => belief.2.law.bind continuation) =
      law.bind continuation := by
  rw [← FinDist.bind_bind, split_bind_law]

/-- Perfect public observation collapses a supported belief to the known history. -/
theorem eq_pure_of_public_injective
    (separates : Function.Injective fun h : E.History => publicTrace S h.trace)
    (belief : PublicBelief S observations) (h : E.History)
    (hmatches : publicTrace S h.trace = observations) : belief.law = FinDist.pure h := by
  apply FinDist.eq_pure_of_support_subset_singleton
  intro other positive
  exact separates ((belief.supported other positive).trans hmatches.symm)

/-- Each player's information law is a marginal of the joint history law. -/
def marginal (belief : PublicBelief S observations) (i : ι) :
    FinDist (AOH (E.Action i) (S.PrivateSignal i) S.PublicSignal) :=
  belief.law.map fun h => (fullSignals S).infoOf i h.trace

/-- Marginalization does not add information from another player's private observation. -/
theorem marginal_public (belief : PublicBelief S observations) (i : ι) :
    (belief.marginal i).map AOH.publicHistory = FinDist.pure observations := by
  rw [marginal, FinDist.map_comp]
  rw [FinDist.map_congr_of_eq_on_support
    (g := fun _ => observations) (fun h hh => by
      simp only [Function.comp_apply, publicHistory_infoOf]
      exact belief.supported h hh)]
  simp [FinDist.map_eq_bind]

end PublicBelief

end GameTheory.ReBeL
