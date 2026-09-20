/-
# Constructed Nash continuations at factual live public queries

A child game is built from the current trunk's actual joint history law,
conditioned on a public observation and a live cut. Finite Nash existence
selects its behavioral equilibrium. One information-local public splice
retains the trunk and realizes every selected child, including every unilateral
deviation. This exact reference construction is not finite-iteration CFR.
-/

import GameTheory.Analysis.ReBeL.CFRDReferenceSlice

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
variable [Fintype ι]

/-- A factual live public query must meet the actual trunk support.
Neither an impossible public history nor a terminal leaf supplies a witness. -/
def CFRDFactualChildPossible (trunk : Profile (fullInformation M).behavioralSignature)
    (cut remaining : Nat) (observations : List M.PublicSignal) : Prop :=
  ∃ history ∈ {h : E.History |
      publicTrace (fullInformation M).toInfoSignals h.trace = observations ∧
        cfrDCutLive remaining h = true},
    history ∈ ((fullInformation M).runBehavioral trunk cut).support

/-- The child root is the actual correlated joint law, not private marginals.
A proof of positive support is required before constructing this posterior. -/
def cfrDFactualChildBelief (trunk : Profile (fullInformation M).behavioralSignature)
    (cut remaining : Nat) (observations : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining observations) :
    PublicBelief (fullInformation M).toInfoSignals observations := by
  classical
  exact { law := ((fullInformation M).runBehavioral trunk cut).condOn _ possible
          supported := fun _ reached => (FinDist.support_condOn _ _ _ reached).1.1 }

/-- Every history in a live child posterior is exactly at the searched cut.
Early terminal histories remain in the trunk law but not in this live child. -/
theorem cfrDFactualChildBelief_atCut
    (trunk : Profile (fullInformation M).behavioralSignature) (cut remaining : Nat)
    (observations : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining observations)
    (history : E.History)
    (reached : history ∈
      (cfrDFactualChildBelief M trunk cut remaining observations possible).law.support) :
    history.trace.length = cut := by
  classical
  have member := FinDist.support_condOn _ _ possible reached
  have live : remaining ≠ 0 ∧ ¬ E.terminal history.state := by
    simpa only [cfrDCutLive, decide_eq_true_eq] using member.1.2
  rcases (fullInformation M).terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
      trunk cut E.initHistory history member.2 with stopped | depth
  · exact (live.2 stopped).elim
  · simpa only [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length,
      Nat.zero_add] using depth

/-- No live child posterior is manufactured when no continuation fuel remains. -/
theorem cfrDFactualChildPossible_zero
    (trunk : Profile (fullInformation M).behavioralSignature) (cut : Nat)
    (observations : List M.PublicSignal) :
    ¬ CFRDFactualChildPossible M trunk cut 0 observations := by
  rintro ⟨history, member, _⟩
  have live := member.2
  rw [cfrDCutLive_zero] at live
  cases live

variable [DecidableEq ι] [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- Exact mathematical child solve, obtained from finite canonical Nash existence.
Unqueried public states use a legal fallback, not a fabricated posterior. -/
def cfrDFactualChildTable (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) :
    List M.PublicSignal → Profile (fullInformation M).behavioralSignature := fun observations => by
  classical
  exact if possible : CFRDFactualChildPossible M trunk cut remaining observations then
    Classical.choose (exists_publicBelief_nash (fullInformation M)
      (fullSignals_perfectRecall M.toInfoSignals) (fullObservationClock M) fallback
      (cfrDFactualChildBelief M trunk cut remaining observations possible) remaining utility)
  else fun who => (fallback who).toBehavioral

/-- The selected table entry is Nash by construction; no equilibrium premise
is passed into the child solver. The deviation domain is fully behavioral. -/
theorem cfrDFactualChildTable_isNash
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) (observations : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining observations) :
    IsNash (behavioralBeliefForm (fullInformation M)
        (cfrDFactualChildBelief M trunk cut remaining observations possible) remaining)
      (euPreference utility) (cfrDFactualChildTable M trunk fallback cut remaining
        utility observations) := by
  simp only [cfrDFactualChildTable, dif_pos possible]
  exact Classical.choose_spec (exists_publicBelief_nash (fullInformation M)
    (fullSignals_perfectRecall M.toInfoSignals) (fullObservationClock M) fallback
    (cfrDFactualChildBelief M trunk cut remaining observations possible) remaining utility)

/-- The constructed joint profile leaves the past intact and chooses its child
using only the public part of the remembered cut prefix. -/
def cfrDFactualChildProfile (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) : Profile (fullInformation M).behavioralSignature :=
  cfrDDepthProfile (fullInformation M) (fullObservationClock M) cut trunk
    (cfrDPublicContinuation M cut (cfrDFactualChildTable M trunk fallback cut remaining utility))

/-- Every searched information state retains the original trunk policy. -/
theorem cfrDFactualChildProfile_before
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) (who : ι) (info : (fullInformation M).InfoState who)
    (before : (fullObservationClock M).depth who info < cut) :
    cfrDFactualChildProfile M trunk fallback cut remaining utility who info = trunk who info := by
  simp only [cfrDFactualChildProfile, cfrDDepthProfile, cfrDDepthTrunk,
    decide_eq_true_eq, if_pos before]

/-- The entire factual prefix distribution is unchanged, not just its mean. -/
theorem cfrDFactualChildProfile_prefixLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) :
    (fullInformation M).runBehavioral
        (cfrDFactualChildProfile M trunk fallback cut remaining utility) cut =
      (fullInformation M).runBehavioral trunk cut := by
  apply runBehavioral_eq_of_before_depth (fullInformation M) (fullObservationClock M)
  exact cfrDFactualChildProfile_before M trunk fallback cut remaining utility

/-- Every legal descendant selects the original public child's complete policy.
The statement is independent of the current policy's reach probabilities. -/
theorem cfrDFactualChildProfile_of_reaches
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) (who : ι) (first later : E.History)
    (atCut : first.trace.length = cut) {fuel : Nat}
    (reaches : E.ReachesWithin fuel first later) :
    cfrDFactualChildProfile M trunk fallback cut remaining utility who
        ((fullInformation M).infoOf who later.trace) =
      cfrDFactualChildTable M trunk fallback cut remaining utility
        (publicTrace M.toInfoSignals first.trace) who
        ((fullInformation M).infoOf who later.trace) := by
  have after : ¬ (fullObservationClock M).depth who
      ((fullInformation M).infoOf who later.trace) < cut := by
    rw [(fullObservationClock M).correct]
    have monotone := reaches.trace_length_le
    omega
  simp only [cfrDFactualChildProfile, cfrDDepthProfile, cfrDDepthTrunk,
    decide_eq_true_eq, if_neg after]
  exact cfrDPublicContinuation_eq_of_reaches M cut _ who first later atCut reaches

/-- The spliced profile realizes the selected child's full joint belief law. -/
theorem cfrDFactualChildProfile_beliefLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (atCut : ∀ h ∈ belief.law.support, h.trace.length = cut) (fuel : Nat) :
    PublicBelief.continuationLaw (fullInformation M)
        (cfrDFactualChildProfile M trunk fallback cut remaining utility) fuel belief =
      PublicBelief.continuationLaw (fullInformation M)
        (cfrDFactualChildTable M trunk fallback cut remaining utility observations)
        fuel belief := by
  apply FinDist.bind_congr
  intro first supported
  have rootPublic := belief.supported first supported
  rw [publicRoot_trace_eq] at rootPublic
  apply (fullInformation M).runBehavioralFrom_congr
  intro later reaches _ who
  simpa only [rootPublic] using cfrDFactualChildProfile_of_reaches M trunk fallback cut remaining
    utility who first later (atCut first supported) reaches

/-- Every unilateral behavioral deviation is preserved too. This is needed
for Nash transfer; equality of just the played law would be insufficient. -/
theorem cfrDFactualChildProfile_deviationLaw
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) {observations : List M.PublicSignal}
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (atCut : ∀ h ∈ belief.law.support, h.trace.length = cut)
    (fuel : Nat) (who : ι) (target : (fullInformation M).BehavioralPolicy who) :
    PublicBelief.continuationLaw (fullInformation M)
        (Profile.update (cfrDFactualChildProfile M trunk fallback cut remaining utility) who target)
        fuel belief =
      PublicBelief.continuationLaw (fullInformation M)
        (Profile.update (cfrDFactualChildTable M trunk fallback cut remaining utility observations)
          who target) fuel belief := by
  apply FinDist.bind_congr
  intro first supported
  have rootPublic := belief.supported first supported
  rw [publicRoot_trace_eq] at rootPublic
  apply (fullInformation M).runBehavioralFrom_congr
  intro later reaches _ player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]
    simpa only [rootPublic] using cfrDFactualChildProfile_of_reaches M trunk fallback cut remaining
      utility player first later (atCut first supported) reaches

/-- One legal prefix-preserving profile is Nash at every factual live public
child. Both its played law and all deviating laws are connected to the selected
finite-game equilibrium; no Nash or continuation-quality premise is supplied. -/
theorem cfrDFactualChildProfile_isNash
    (trunk : Profile (fullInformation M).behavioralSignature)
    (fallback : Profile (fullInformation M).strategicSignature) (cut remaining : Nat)
    (utility : E.History → ι → ℝ) (observations : List M.PublicSignal)
    (possible : CFRDFactualChildPossible M trunk cut remaining observations) :
    IsNash (behavioralBeliefForm (fullInformation M)
        (cfrDFactualChildBelief M trunk cut remaining observations possible) remaining)
      (euPreference utility) (cfrDFactualChildProfile M trunk fallback cut remaining utility) := by
  have equilibrium := cfrDFactualChildTable_isNash M trunk fallback cut remaining utility
    observations possible
  rw [isNash_iff] at equilibrium ⊢
  intro who target
  have atCut := cfrDFactualChildBelief_atCut M trunk cut remaining observations possible
  simpa only [euPreference_apply, behavioralBeliefForm,
    cfrDFactualChildProfile_beliefLaw M trunk fallback cut remaining utility _ atCut,
    cfrDFactualChildProfile_deviationLaw M trunk fallback cut remaining utility _ atCut]
    using equilibrium who target

end GameTheory.ReBeL
