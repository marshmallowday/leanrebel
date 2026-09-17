/-
# Policies on all realizable information states

Realizability quantifies over every canonical history, not the support of one
profile. Thus restriction does not erase off-policy deviations. Extending to
syntactic but unrealizable information states requires an explicit legal
fallback policy. In particular, nonempty terminal menus are not inferred from
the protocol's nonterminal progress law.
-/

import GameTheory.ReBeL.Information
import GameTheory.Protocol.Strategic

noncomputable section

namespace GameTheory.ReBeL.PolicyDomain

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel E)

/-- Includes off-policy and terminal histories, independently of any reference strategy. -/
def Realizable (i : ι) (info : M.InfoState i) : Prop :=
  ∃ h : E.History, M.infoOf i h.trace = info

/-- The information states on which a history-based policy can actually be queried. -/
abbrev Info (i : ι) := {info : M.InfoState i // Realizable M i info}

/-- A legal local distribution at every realizable information state. -/
abbrev Policy (i : ι) := (info : Info M i) → FinDist (M.Choice i info.1)

/-- Restricted policies still have the canonical history outcome carrier. -/
def signature : GameSignature ι where
  Strategy := Policy M
  Outcome := E.History

/-- Restrict a full behavioral policy without selecting a reference profile. -/
def restrict (i : ι) (policy : M.BehavioralPolicy i) : Policy M i :=
  fun info => policy info.1

/-- Only unrealizable syntax uses the explicitly supplied fallback. -/
def extend (i : ι) (fallback : M.BehavioralPolicy i) (policy : Policy M i) :
    M.BehavioralPolicy i := by
  classical
  exact fun info => if realized : Realizable M i info then policy ⟨info, realized⟩
    else fallback info

@[simp]
theorem restrict_extend (i : ι) (fallback : M.BehavioralPolicy i) (policy : Policy M i) :
    restrict M i (extend M i fallback policy) = policy := by
  funext info
  simp [restrict, extend, info.2]

/-- Every canonical history takes the realizable branch, including probability-zero paths. -/
@[simp]
theorem extend_at_history (i : ι) (fallback : M.BehavioralPolicy i)
    (policy : Policy M i) (h : E.History) :
    extend M i fallback policy (M.infoOf i h.trace) =
      policy ⟨M.infoOf i h.trace, ⟨h, rfl⟩⟩ := by
  classical
  exact dif_pos (show Realizable M i (M.infoOf i h.trace) from ⟨h, rfl⟩)

@[simp]
theorem extend_restrict_at_history (i : ι) (fallback policy : M.BehavioralPolicy i)
    (h : E.History) :
    extend M i fallback (restrict M i policy) (M.infoOf i h.trace) =
      policy (M.infoOf i h.trace) :=
  extend_at_history M i fallback (restrict M i policy) h

/-- Coordinatewise restriction cannot inspect an opponent's private policy. -/
def restrictProfile (profile : Profile M.behavioralSignature) : Profile (signature M) :=
  fun i => restrict M i (profile i)

/-- Coordinatewise extension; changing one strategy does not change any other coordinate. -/
def extendProfile (fallback : Profile M.behavioralSignature)
    (profile : Profile (signature M)) : Profile M.behavioralSignature :=
  fun i => extend M i (fallback i) (profile i)

@[simp]
theorem restrictProfile_extendProfile (fallback : Profile M.behavioralSignature)
    (profile : Profile (signature M)) :
    restrictProfile M (extendProfile M fallback profile) = profile := by
  funext i
  exact restrict_extend M i (fallback i) (profile i)

/-- Restriction preserves the full unilateral deviation space. -/
theorem restrictProfile_update [DecidableEq ι] (profile : Profile M.behavioralSignature)
    (i : ι) (replacement : M.BehavioralPolicy i) :
    restrictProfile M (Profile.update profile i replacement) =
      Profile.update (restrictProfile M profile) i (restrict M i replacement) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [restrictProfile]
  · simp [restrictProfile, hj]

/-- Extension commutes with canonical profile update, with the same fixed fallback. -/
theorem extendProfile_update [DecidableEq ι] (fallback : Profile M.behavioralSignature)
    (profile : Profile (signature M)) (i : ι) (replacement : Policy M i) :
    extendProfile M fallback (Profile.update profile i replacement) =
      Profile.update (extendProfile M fallback profile) i (extend M i (fallback i) replacement) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [extendProfile]
  · simp [extendProfile, hj]

/-- Full history-law preservation, for every root and every profile, not only on-policy roots. -/
theorem run_extend_restrict [Fintype ι] (fallback profile : Profile M.behavioralSignature)
    (fuel : Nat) (root : E.History) :
    M.runBehavioralFrom (extendProfile M fallback (restrictProfile M profile)) fuel root =
      M.runBehavioralFrom profile fuel root := by
  apply M.runBehavioralFrom_congr
  intro h _ _ i
  exact extend_restrict_at_history M i (fallback i) (profile i) h

/-- The arbitrary off-domain fallback cannot change any outcome. -/
theorem run_extend_independent [Fintype ι]
    (first second : Profile M.behavioralSignature) (profile : Profile (signature M))
    (fuel : Nat) (root : E.History) :
    M.runBehavioralFrom (extendProfile M first profile) fuel root =
      M.runBehavioralFrom (extendProfile M second profile) fuel root := by
  apply M.runBehavioralFrom_congr
  intro h _ _ i
  exact (extend_at_history M i (first i) (profile i) h).trans
    (extend_at_history M i (second i) (profile i) h).symm

/-- Nonempty menus at all syntactic information states are sufficient for a legal fallback. -/
def fallbackOfNonempty (nonempty : ∀ i info, Nonempty (M.Choice i info)) :
    Profile M.behavioralSignature :=
  fun i info => FinDist.pure (Classical.choice (nonempty i info))

/-- They are also necessary: total policies do not magically repair an empty terminal menu. -/
theorem exists_profile_iff_nonempty_choices :
    Nonempty (Profile M.behavioralSignature) ↔ ∀ i info, Nonempty (M.Choice i info) := by
  constructor
  · rintro ⟨profile⟩ i info
    obtain ⟨choice, _⟩ := (profile i info).support_nonempty
    exact ⟨choice⟩
  · intro nonempty
    exact ⟨fallbackOfNonempty M nonempty⟩

end GameTheory.ReBeL.PolicyDomain
