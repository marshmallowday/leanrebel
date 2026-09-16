/-
# ReBeL rewards through the canonical evaluator

Immediate rewards R_i(w,a), cumulative return and expected strategy value are
distinct. Continuation values remove realized past rewards; they do not assign
posterior probabilities to unreachable information sets (the M03 obligation).
-/

import GameTheory.Protocol.Strategic
import GameTheory.Core.ZeroSum

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

universe uι us ua
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

/-- The paper's immediate reward: world, joint action and player. -/
abbrev StageReward (E : ExecutionProtocol ι) :=
  E.State → (∀ i, Option (E.Action i)) → ι → ℝ

/-- Cumulative utility is the existing history-value fold. -/
def cumulativeUtility (reward : StageReward E) (history : E.History) (i : ι) : ℝ :=
  history.valueSum (fun event => reward event.source event.joint i)

/-- Future reward excludes the fixed root's realized past. -/
def futureUtility (reward : StageReward E) (root history : E.History) (i : ι) : ℝ :=
  cumulativeUtility reward history i - cumulativeUtility reward root i

@[simp]
theorem cumulativeUtility_init (reward : StageReward E) (i : ι) :
    cumulativeUtility reward E.initHistory i = 0 := rfl

@[simp]
theorem cumulativeUtility_extend (reward : StageReward E) (history : E.History)
    {joint : ∀ i, Option (E.Action i)} (legal : E.Legal history.state joint)
    {target : E.State} (realized : target ∈ (E.step history.state ⟨joint, legal⟩).support)
    (i : ι) :
    cumulativeUtility reward (history.extend legal realized) i =
      cumulativeUtility reward history i + reward history.state joint i := rfl

@[simp]
theorem futureUtility_self (reward : StageReward E) (history : E.History) (i : ι) :
    futureUtility reward history history i = 0 := sub_self _

@[simp]
theorem futureUtility_init (reward : StageReward E) (history : E.History) (i : ι) :
    futureUtility reward E.initHistory history i = cumulativeUtility reward history i := by
  simp [futureUtility]

/-- A potential is an optional proved simplification, not a new utility. -/
theorem cumulativeUtility_eq_potential (reward : StageReward E)
    (potential : E.State → ι → ℝ)
    (initial : ∀ i, potential E.init i = 0)
    (increment : ∀ (event : E.StepEvent) (i : ι),
      potential event.target i = potential event.source i + reward event.source event.joint i)
    (history : E.History) (i : ι) :
    cumulativeUtility reward history i = potential history.state i := by
  rcases history with ⟨state, trace⟩
  induction trace with
  | start => exact (initial i).symm
  | extend prior joint legal realized ih =>
      change prior.valueSum (fun event => reward event.source event.joint i) +
        reward _ joint i = _
      rw [increment ⟨_, joint, legal, _, realized⟩ i]
      exact congrArg (fun past => past + reward _ joint i) ih

/-- Stagewise zero-sum rewards remain zero-sum on every realized history. -/
theorem cumulativeUtility_zeroSum [Fintype ι] (reward : StageReward E)
    (zeroSum : ∀ event : E.StepEvent, ∑ i, reward event.source event.joint i = 0) :
    IsZeroSum (cumulativeUtility reward) := by
  intro history
  rcases history with ⟨state, trace⟩
  induction trace with
  | start => simp [cumulativeUtility, History.valueSum, Trace.valueSum]
  | extend prior joint legal realized ih =>
      change (∑ i, (prior.valueSum (fun event => reward event.source event.joint i) +
        reward _ joint i)) = 0
      rw [Finset.sum_add_distrib]
      change (∑ i, prior.valueSum (fun event => reward event.source event.joint i)) = 0 at ih
      rw [ih, zeroSum ⟨_, joint, legal, _, realized⟩, add_zero]

/-- Removing past rewards preserves zero-sum utility. -/
theorem futureUtility_zeroSum [Fintype ι] (reward : StageReward E)
    (zeroSum : ∀ event : E.StepEvent, ∑ i, reward event.source event.joint i = 0)
    (root : E.History) : IsZeroSum (futureUtility reward root) := by
  intro history
  change (∑ i, (cumulativeUtility reward history i - cumulativeUtility reward root i)) = 0
  rw [Finset.sum_sub_distrib, cumulativeUtility_zeroSum reward zeroSum history,
    cumulativeUtility_zeroSum reward zeroSum root, sub_self]

/-- Behavioral profile value uses the canonical information-local game form. -/
def policyValue [Fintype ι] (M : InformationModel E) (reward : StageReward E)
    (horizon : Nat) (profile : Profile M.behavioralSignature) (i : ι) : ℝ :=
  expectedUtility (cumulativeUtility reward) i ((M.toBehavioralGameForm horizon).play profile)

/-- Value from a concrete reached history, without any posterior update. -/
def continuationValue [Fintype ι] (M : InformationModel E) (reward : StageReward E)
    (fuel : Nat) (profile : Profile M.behavioralSignature) (root : E.History) (i : ι) : ℝ :=
  expectedUtility (futureUtility reward root) i (M.runBehavioralFrom profile fuel root)

/-- The paper's maximum characterization is the existing Nash definition.
No equilibrium existence theorem or best-response oracle is assumed. -/
theorem isNash_iff_policyValue_greatest [Fintype ι] [DecidableEq ι]
    (M : InformationModel E) (reward : StageReward E) (horizon : Nat)
    (profile : Profile M.behavioralSignature) :
    IsNash (M.toBehavioralGameForm horizon) (euPreference (cumulativeUtility reward)) profile ↔
      ∀ i, IsGreatest
        (Set.range fun replacement : M.BehavioralPolicy i =>
          policyValue M reward horizon (Profile.update profile i replacement) i)
        (policyValue M reward horizon profile i) := by
  rw [isNash_iff]
  constructor
  · intro hnash i
    refine ⟨⟨profile i, ?_⟩, ?_⟩
    · change policyValue M reward horizon (Profile.update profile i (profile i)) i = _
      rw [Profile.update_eq_self]
    · intro value hvalue
      obtain ⟨replacement, rfl⟩ := hvalue
      exact hnash i replacement
  · intro greatest i replacement
    exact (greatest i).2 ⟨replacement, rfl⟩

end GameTheory.ReBeL
