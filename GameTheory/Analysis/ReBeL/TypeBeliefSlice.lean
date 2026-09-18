/-
# Admissible own-belief slices of a joint public belief

Own-type weights vary while the complete compatible conditional history laws
are held fixed. These kernels may correlate all other hidden variables. A
zero-own-probability type uses an explicit physically compatible off-path law;
it is not assigned an arbitrary posterior by dividing zero by zero.
-/

import GameTheory.Analysis.ReBeL.RootTypeMemory
import GameTheory.ReBeL.BeliefExecution

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe uι us ua up uq uk ut
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Fixed conditional joint history laws, indexed by an information-local,
remembered own type. This is a domain of beliefs, not a payoff certificate. -/
structure TypeBeliefSlice (observations : List M.PublicSignal) (who : ι) (T : Type ut) where
  /-- The type can be read throughout continuation from the player's own information. -/
  memory : RootTypeMemory M observations who T
  /-- All hidden-state correlations within a type remain in this complete law. -/
  kernel : T → PublicBelief M.toInfoSignals observations
  /-- A conditional law is physically compatible with its named own type. -/
  typed : ∀ type history, history ∈ (kernel type).law.support →
    memory.typeAt (M.infoOf who history.trace) = type

namespace TypeBeliefSlice

variable {M} {observations : List M.PublicSignal} {who : ι} {T : Type ut}

/-- Vary only the own-type law; keep every complete conditional kernel fixed. -/
def mixture (slice : TypeBeliefSlice M observations who T) (own : FinDist T) :
    PublicBelief M.toInfoSignals observations where
  law := own.bind fun type => (slice.kernel type).law
  supported history supported := by
    rw [FinDist.support_bind] at supported
    obtain ⟨type, _, hhistory⟩ := Set.mem_iUnion₂.mp supported
    exact (slice.kernel type).supported history hhistory

/-- The own-type law is recovered exactly, including at boundary beliefs. -/
theorem mixture_typeLaw (slice : TypeBeliefSlice M observations who T) (own : FinDist T) :
    (slice.mixture own).law.map (fun history => slice.memory.typeAt (M.infoOf who history.trace)) =
      own := by
  rw [mixture, FinDist.map_bind]
  calc
    _ = own.bind (fun type => FinDist.pure type) := by
      apply FinDist.bind_congr
      intro type _
      calc
        _ = ((slice.kernel type).law).map (fun _ => type) := by
          simp only [FinDist.map_eq_bind]
          apply FinDist.bind_congr
          intro history supported
          exact congrArg FinDist.pure (slice.typed type history supported)
        _ = _ := FinDist.map_const _ _
    _ = own := FinDist.bind_pure _

/-- The resulting full continuation law is a mixture of the actual canonical
conditional continuation laws, with no independence approximation. -/
theorem mixture_continuationLaw [Fintype ι]
    (slice : TypeBeliefSlice M observations who T) (own : FinDist T)
    (profile : Profile M.behavioralSignature) (fuel : ℕ) :
    PublicBelief.continuationLaw M profile fuel (slice.mixture own) =
      own.bind fun type => PublicBelief.continuationLaw M profile fuel (slice.kernel type) := by
  exact FinDist.bind_bind _ _ _

/-- Expected payoff separates by own type because the root law is a mixture,
not because the target linearity statement is stored in an assumption. -/
theorem mixture_payoff [Fintype ι]
    (slice : TypeBeliefSlice M observations who T) (own : FinDist T)
    (profile : Profile M.behavioralSignature) (fuel : ℕ) (payoff : E.History → ℝ) :
    (PublicBelief.continuationLaw M profile fuel (slice.mixture own)).expect payoff =
      own.expect fun type =>
        (PublicBelief.continuationLaw M profile fuel (slice.kernel type)).expect payoff := by
  rw [mixture_continuationLaw, FinDist.expect_bind]

/-- Typewise plan splicing preserves each conditional full history law,
including kernels whose current own weight is zero. -/
theorem splice_conditionalLaw [Fintype ι] [DecidableEq ι]
    (slice : TypeBeliefSlice M observations who T) (plans : T → M.Policy who)
    (opponents : Profile M.behavioralSignature) (fuel : ℕ) (type : T) :
    PublicBelief.continuationLaw M
        (Profile.update opponents who (slice.memory.splice plans).toBehavioral)
        fuel (slice.kernel type) =
      PublicBelief.continuationLaw M
        (Profile.update opponents who (plans type).toBehavioral) fuel (slice.kernel type) := by
  apply FinDist.bind_congr
  intro history supported
  exact slice.memory.splice_law plans opponents history fuel
    ((slice.kernel type).supported history supported) (slice.typed type history supported)

/-- Bayes-condition a positive own type, otherwise use a specified compatible
law. The off-path law is visible data rather than an invented posterior. -/
def conditionedKernel (memory : RootTypeMemory M observations who T)
    (belief : PublicBelief M.toInfoSignals observations)
    (offPath : T → PublicBelief M.toInfoSignals observations) (type : T) :
    PublicBelief M.toInfoSignals observations := by
  classical
  exact if positive : ∃ history ∈
      {h : E.History | memory.typeAt (M.infoOf who h.trace) = type},
        history ∈ belief.law.support then
    { law := belief.law.condOn _ positive
      supported := fun history supported =>
        belief.supported history (FinDist.support_condOn _ _ _ supported).2 }
  else offPath type

/-- The completed conditional kernel always has the named own type. -/
theorem conditionedKernel_typed (memory : RootTypeMemory M observations who T)
    (belief : PublicBelief M.toInfoSignals observations)
    (offPath : T → PublicBelief M.toInfoSignals observations)
    (compatible : ∀ type history, history ∈ (offPath type).law.support →
      memory.typeAt (M.infoOf who history.trace) = type)
    (type : T) (history : E.History)
    (supported : history ∈ (conditionedKernel memory belief offPath type).law.support) :
    memory.typeAt (M.infoOf who history.trace) = type := by
  classical
  by_cases positive : ∃ h ∈ {h : E.History | memory.typeAt (M.infoOf who h.trace) = type},
      h ∈ belief.law.support
  · simp only [conditionedKernel, dif_pos positive] at supported
    exact (FinDist.support_condOn _ _ _ supported).1
  · simp only [conditionedKernel, dif_neg positive] at supported
    exact compatible type history supported

/-- Every joint PBS with physically compatible off-path kernels supplies an
admissible slice. No product-of-marginals restriction is placed on the PBS. -/
def ofJointBelief (memory : RootTypeMemory M observations who T)
    (belief : PublicBelief M.toInfoSignals observations)
    (offPath : T → PublicBelief M.toInfoSignals observations)
    (compatible : ∀ type history, history ∈ (offPath type).law.support →
      memory.typeAt (M.infoOf who history.trace) = type) :
    TypeBeliefSlice M observations who T where
  memory := memory
  kernel := conditionedKernel memory belief offPath
  typed := conditionedKernel_typed memory belief offPath compatible

/-- Decomposing and reconstructing the actual joint belief preserves its
entire law, not merely its private-type marginals or expected payoff. -/
theorem ofJointBelief_reconstruct (memory : RootTypeMemory M observations who T)
    (belief : PublicBelief M.toInfoSignals observations)
    (offPath : T → PublicBelief M.toInfoSignals observations)
    (compatible : ∀ type history, history ∈ (offPath type).law.support →
      memory.typeAt (M.infoOf who history.trace) = type) :
    ((ofJointBelief memory belief offPath compatible).mixture
      (belief.law.map fun history => memory.typeAt (M.infoOf who history.trace))).law =
        belief.law := by
  classical
  let readType := fun history : E.History => memory.typeAt (M.infoOf who history.trace)
  show (belief.law.map readType).bind
    (fun type => (conditionedKernel memory belief offPath type).law) = belief.law
  conv_rhs => rw [FinDist.eq_bind_condOnFibre belief.law readType]
  apply FinDist.bind_congr
  intro type supported
  have positive : ∃ history ∈ {h : E.History | readType h = type},
      history ∈ belief.law.support := by
    rw [FinDist.support_map] at supported
    obtain ⟨history, hhistory, htype⟩ := supported
    exact ⟨history, htype, hhistory⟩
  have positiveKernel : ∃ history ∈
      {h : E.History | memory.typeAt (M.infoOf who h.trace) = type},
        history ∈ belief.law.support := positive
  have positiveFibre : ∃ history ∈ readType ⁻¹' {type},
      history ∈ belief.law.support := positive
  rw [conditionedKernel, dif_pos positiveKernel, FinDist.condOnFibre, dif_pos positiveFibre]

end TypeBeliefSlice
end GameTheory.ReBeL
