/-
# Constructed optimal responses on zero-own-reach conditional kernels

Zero own reach persists along every legal continuation. Consequently replacing
only these decisions by the canonical simultaneous conditional best response
attains every compatible off-path kernel's best-response value, while leaving
all original-game laws against fixed opponents unchanged. This is a focal
completion against fixed opponents, not a recursive equilibrium solver.
-/

import GameTheory.Analysis.ReBeL.CFRDZeroReachCompletion
import GameTheory.Analysis.ReBeL.PBSInfoValue

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Protocol.InformationModel GameTheory.Math.Probability

universe uι us ua up uq uk ut
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- A vanished own-prefix product stays zero at every legal extension,
independently of the positive or zero probabilities of the other players. -/
theorem cfrD_zero_ownReach_of_reaches (base : Profile M.behavioralSignature)
    (who : ι) {fuel : Nat} {first later : E.History}
    (reaches : E.ReachesWithin fuel first later) :
    M.playerReachProbability base who first.trace = 0 →
      M.playerReachProbability base who later.trace = 0 := by
  induction reaches with
  | refl => exact fun zero => zero
  | @step fuel first later joint legal target realized rest ih =>
      intro zero
      apply ih
      simp only [History.extend, InformationModel.playerReachProbability, zero, zero_mul]

variable [Fintype ι] [DecidableEq ι]

/-- From a zero-own-reach root the completed focal continuation is exactly
its supplied legal completion, even though its original-game law is unchanged. -/
theorem cfrDCompleteZeroReach_continuation (hrecall : M.PerfectRecall)
    (base completion : Profile M.behavioralSignature) (who : ι)
    (fuel : Nat) (history : E.History)
    (zero : M.playerReachProbability base who history.trace = 0) :
    M.runBehavioralFrom
        (Profile.update base who (cfrDCompleteZeroReach M base completion who)) fuel history =
      M.runBehavioralFrom (Profile.update base who (completion who)) fuel history := by
  apply M.runBehavioralFrom_congr
  intro later reaches _ player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    apply cfrDCompleteZeroReach_of_zero
    rw [informationOwnReach_eq_player M hrecall base who later]
    exact cfrD_zero_ownReach_of_reaches M base who reaches zero
  · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]

namespace TypeBeliefSlice

variable {M} {observations : List M.PublicSignal} {who : ι} {T : Type ut}
variable (slice : TypeBeliefSlice M observations who T)
variable [Fintype E.History] [∀ i, Fintype (E.Action i)]

/-- The completion is selected by finite conditional best-response maximization
and remembered-type splicing, not supplied as an assumed optimal policy. -/
def zeroReachBestResponse (fallback : Profile M.strategicSignature) (fuel : Nat)
    (payoff : E.History → ℝ) (base : Profile M.behavioralSignature) : M.BehavioralPolicy who :=
  cfrDCompleteZeroReach M base
    (Profile.update base who (slice.simultaneousResponse fallback fuel payoff base).toBehavioral) who

/-- All original-game laws against arbitrary fixed opponents are unchanged
by this constructed focal completion. No Nash premise is needed for equality. -/
theorem zeroReachBestResponse_run (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat) (payoff : E.History → ℝ)
    (base unknown : Profile M.behavioralSignature) (horizon : Nat) :
    M.runBehavioral (Profile.update unknown who
        (slice.zeroReachBestResponse fallback fuel payoff base)) horizon =
      M.runBehavioral (Profile.update unknown who (base who)) horizon :=
  cfrDCompleteZeroReach_unilateral_run M hrecall base
    (Profile.update base who (slice.simultaneousResponse fallback fuel payoff base).toBehavioral)
    unknown who horizon

/-- On every conditional root kernel with zero original own reach, the
constructed completion attains the canonical maximum over ALL behavioral
responses. This premise concerns reach and support, not a value inequality. -/
theorem zeroReachBestResponse_attains (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat) (payoff : E.History → ℝ)
    (base : Profile M.behavioralSignature) (type : T)
    (offPath : ∀ history ∈ (slice.kernel type).law.support,
      informationOwnReach M base who (M.infoOf who history.trace) = 0) :
    slice.conditionalPayoff base fuel payoff
        (slice.zeroReachBestResponse fallback fuel payoff base) type =
      slice.infoValue fallback fuel payoff base type := by
  let response := (slice.simultaneousResponse fallback fuel payoff base).toBehavioral
  calc
    _ = slice.conditionalPayoff base fuel payoff response type := by
      unfold conditionalPayoff
      apply congrArg (fun law => law.expect payoff)
      apply FinDist.bind_congr
      intro history supported
      have zero : M.playerReachProbability base who history.trace = 0 := by
        simpa only [informationOwnReach_eq_player M hrecall base who history] using
          offPath history supported
      simpa only [zeroReachBestResponse, Profile.update_same] using
        cfrDCompleteZeroReach_continuation M hrecall base
          (Profile.update base who response) who fuel history zero
    _ = _ := slice.simultaneousResponse_attains fallback fuel payoff base type

/-- The same single legal completion dominates every complete behavioral
future deviation on every such zero-own-reach kernel. -/
theorem zeroReachBestResponse_optimal (hrecall : M.PerfectRecall)
    (fallback : Profile M.strategicSignature) (fuel : Nat) (payoff : E.History → ℝ)
    (base : Profile M.behavioralSignature) (type : T)
    (offPath : ∀ history ∈ (slice.kernel type).law.support,
      informationOwnReach M base who (M.infoOf who history.trace) = 0)
    (target : M.BehavioralPolicy who) :
    slice.conditionalPayoff base fuel payoff target type ≤
      slice.conditionalPayoff base fuel payoff
        (slice.zeroReachBestResponse fallback fuel payoff base) type := by
  rw [slice.zeroReachBestResponse_attains hrecall fallback fuel payoff base type offPath]
  exact slice.conditionalPayoff_le_infoValue hrecall fallback fuel payoff base type target

end TypeBeliefSlice
end GameTheory.ReBeL
