/-
# Remembering a root type and legally pasting its continuation plans

The memory condition is information-local and structural: continuation may
reveal more observations but cannot forget the player's type at the public
cut. Full AOH memory supplies it by truncation. It is not an assumed payoff,
linearity, best-response, realization or equilibrium certificate.
-/

import GameTheory.ReBeL.PublicSubgame

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk ut
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Extract the earlier AOH at the requested public depth, retaining an AOH
unchanged when it has not yet reached that depth. -/
def AOH.prefixAt {A : Type ua} {P : Type uq} {U : Type up} (cut : ℕ) :
    AOH A P U → AOH A P U
  | .initial privateObs publicObs => .initial privateObs publicObs
  | .step prior action privateObs publicObs =>
      if prior.length < cut then .step prior action privateObs publicObs else prefixAt cut prior

/-- An AOH at or before the cut is unchanged by truncation. -/
theorem AOH.prefixAt_eq_of_length_le {A : Type ua} {P : Type uq} {U : Type up}
    (cut : ℕ) (history : AOH A P U) (before : history.length ≤ cut) :
    history.prefixAt cut = history := by
  cases history with
  | initial => rfl
  | step prior action privateObs publicObs =>
      apply if_pos
      simp only [AOH.length] at before
      omega

/-- Once the cut has passed, another observation does not change its prefix. -/
theorem AOH.prefixAt_step_of_le {A : Type ua} {P : Type uq} {U : Type up}
    (cut : ℕ) (prior : AOH A P U) (action : Option A) (privateObs : P) (publicObs : U)
    (after : cut ≤ prior.length) :
    (AOH.step prior action privateObs publicObs).prefixAt cut = prior.prefixAt cut := by
  exact if_neg (not_lt.mpr after)

/-- Full AOH memory keeps the root prefix along every legal continuation,
independently of any particular strategy's reach probabilities. -/
theorem prefixAt_infoOf_reaches (cut : ℕ) (who : ι) {fuel : ℕ}
    {first later : E.History} (reaches : E.ReachesWithin fuel first later) :
    cut ≤ first.trace.length →
      ((fullInformation M).infoOf who later.trace).prefixAt cut =
        ((fullInformation M).infoOf who first.trace).prefixAt cut := by
  induction reaches with
  | refl => intro _; rfl
  | @step fuel first later joint legal target realized rest ih =>
      intro after
      calc
        _ = ((fullInformation M).infoOf who (first.extend legal realized).trace).prefixAt cut :=
          ih (by simpa only [History.extend, Trace.length] using
            Nat.le_succ_of_le after)
        _ = _ := AOH.prefixAt_step_of_le cut
          ((fullInformation M).infoOf who first.trace) (joint who) _ _
            (by simpa only [length_infoOf] using after)

/-- A root type is remembered by local information throughout its public
subgame. The only premise concerns legal histories and information, not utility. -/
structure RootTypeMemory (observations : List M.PublicSignal) (who : ι) (T : Type ut) where
  /-- Read the root type from one's own information, never from hidden state. -/
  typeAt : M.InfoState who → T
  /-- Every legal continuation preserves this root information. -/
  persistent : ∀ (first later : E.History),
    publicTrace M.toInfoSignals first.trace = observations →
      ∀ {fuel : ℕ}, E.ReachesWithin fuel first later →
        typeAt (M.infoOf who later.trace) = typeAt (M.infoOf who first.trace)

/-- Truncating full AOH memory discharges the structural memory condition.
The finite type encoding may coarsen the remembered prefix but cannot inspect
anything beyond the player's own action-observation history. -/
def fullRootTypeMemory (observations : List M.PublicSignal) (who : ι) {T : Type ut}
    (encode : AOH (E.Action who) (M.PrivateSignal who) M.PublicSignal → T) :
    RootTypeMemory (fullInformation M) observations who T where
  typeAt info := encode (info.prefixAt (observations.length - 1))
  persistent first later hpublic := by
    intro fuel reaches
    have depth : (publicTrace (fullInformation M).toInfoSignals first.trace).length =
        first.trace.length + 1 := by
      rcases first with ⟨state, trace⟩
      induction trace with
      | start => rfl
      | extend prior joint legal realized ih =>
          simp only [publicTrace, List.length_cons, Trace.length, ih]
    rw [hpublic] at depth
    exact congrArg encode (prefixAt_infoOf_reaches M (observations.length - 1) who reaches
      (by omega))

namespace RootTypeMemory

variable {M} {observations : List M.PublicSignal} {who : ι} {T : Type ut}

/-- Paste one total legal plan per remembered type. At a future information
state the selected plan depends only on information visible to this player. -/
def splice (memory : RootTypeMemory M observations who T) (plans : T → M.Policy who) :
    M.Policy who := fun info => plans (memory.typeAt info) info

/-- The pasted plan agrees with the root type's plan at every legal
continuation information state, not just at positive-probability paths. -/
theorem splice_eq_of_reaches (memory : RootTypeMemory M observations who T)
    (plans : T → M.Policy who) (first later : E.History)
    (hpublic : publicTrace M.toInfoSignals first.trace = observations)
    {fuel : ℕ} (reaches : E.ReachesWithin fuel first later) {type : T}
    (typed : memory.typeAt (M.infoOf who first.trace) = type) :
    memory.splice plans (M.infoOf who later.trace) = plans type (M.infoOf who later.trace) := by
  unfold splice
  rw [memory.persistent first later hpublic reaches, typed]

/-- Legal typewise gluing preserves the complete continuation law when the
root has that type, with all opponent coordinates held fixed. -/
theorem splice_law [Fintype ι] [DecidableEq ι]
    (memory : RootTypeMemory M observations who T) (plans : T → M.Policy who)
    (opponents : Profile M.behavioralSignature) (first : E.History) (fuel : ℕ)
    (hpublic : publicTrace M.toInfoSignals first.trace = observations) {type : T}
    (typed : memory.typeAt (M.infoOf who first.trace) = type) :
    M.runBehavioralFrom (Profile.update opponents who (memory.splice plans).toBehavioral)
        fuel first =
      M.runBehavioralFrom (Profile.update opponents who (plans type).toBehavioral) fuel first := by
  apply M.runBehavioralFrom_congr
  intro later reaches _ player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    exact congrArg FinDist.pure (memory.splice_eq_of_reaches plans first later hpublic reaches typed)
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]

end RootTypeMemory
end GameTheory.ReBeL
