/-
# Constructed child sampling in the carried public resolver

The parent's virtual continuation and its actual delayed private draw use
one child table. Their complete outcome laws coincide against every fixed
opponent. This removes the extra replacement-loss premise for this adapter;
it does not assert optimality of an arbitrary supplied child table.
-/

import GameTheory.Analysis.ReBeL.CFRDDelayedSampling
import GameTheory.Analysis.ReBeL.CFRDResolveBelief

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable {K J : Type*}

/-- Stopped execution is the pure current history, not merely equal in payoff. -/
theorem cfrD_run_stopped (profile : Profile M.behavioralSignature)
    (remaining : Nat) (history : E.History)
    (stopped : cfrDCutLive remaining history ≠ true) :
    M.runBehavioralFrom profile remaining history = FinDist.pure history := by
  classical
  by_cases zero : remaining = 0
  · subst remaining
    simp [InformationModel.runBehavioralFrom]
  · have terminal : E.terminal history.state := by
      by_contra not_terminal
      apply stopped
      simp only [cfrDCutLive, decide_eq_true_eq]
      exact ⟨zero, not_terminal⟩
    exact M.runBehavioralFrom_of_terminal profile remaining terminal

/-- The private child table is indexed by the retained parent iteration.
Its policies may depend on information states, but the resolver is not given
an actual hidden history or the unknown opponent. -/
def cfrDChildPublicResolver (clock : ObservationClock M) (cut : Nat)
    (seeds : K → FinDist J) (trunks : K → Profile M.behavioralSignature)
    (children : K → J → Profile M.behavioralSignature) : CarriedPublicResolver M K :=
  fun n _ _ => (seeds n).map (cfrDChildProfiles M clock cut (trunks n) (children n))

/-- Only live states draw a child. Forgetting an unneeded draw at a stopped
state gives the same law, so early terminals and zero fuel remain exact. -/
theorem cfrDChildResolvedTail_eq (clock : ObservationClock M) (cut : Nat)
    (seeds : K → FinDist J) (trunks : K → Profile M.behavioralSignature)
    (children : K → J → Profile M.behavioralSignature)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (remaining : Nat)
    (state : PrivateIterationState M K) :
    carriedResolvedTail M (cfrDChildPublicResolver M clock cut seeds trunks children)
        unknown who remaining state =
      (seeds state.iteration).bind (fun k => M.runBehavioralFrom
        (Profile.update unknown who
          (cfrDChildProfiles M clock cut (trunks state.iteration)
            (children state.iteration) k who)) remaining state.history) := by
  by_cases active : cfrDCutLive remaining state.history = true
  · simp only [carriedResolvedTail, if_pos active, cfrDChildPublicResolver,
      FinDist.map_eq_bind, FinDist.bind_bind, FinDist.pure_bind]
  · simp only [carriedResolvedTail, if_neg active]
    symm
    calc
      _ = (seeds state.iteration).bind (fun _ => FinDist.pure state.history) := by
        apply FinDist.bind_congr
        intro k _
        exact cfrD_run_stopped M _ remaining state.history active
      _ = _ := FinDist.bind_const _ _

variable [Fintype J]

/-- Parent profiles use precisely the own-reach averages of the child tables
that the public resolver will sample, with each parent's trunk preserved. -/
def cfrDChildParentProfiles (clock : ObservationClock M) (cut : Nat)
    (seeds : K → FinDist J) (trunks : K → Profile M.behavioralSignature)
    (children : K → J → Profile M.behavioralSignature) (fallback : (who : Fin 2) → M.Policy who) :
    K → Profile M.behavioralSignature :=
  fun n => cfrDDepthProfile M clock cut (trunks n)
    (cfrDChildAverage M clock cut (seeds n) (trunks n) (children n) fallback)

/-- Exact carried-resolver realization against every seed-blind opponent.
There is no local fixed-opponent comparison, Nash premise, or payoff bound.
The optional model belief remains attached by the canonical carried prefix. -/
theorem cfrDChildResolve_eq (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (rootSeed : FinDist K) (seeds : K → FinDist J)
    (trunks : K → Profile M.behavioralSignature)
    (children : K → J → Profile M.behavioralSignature) (fallback : (who : Fin 2) → M.Policy who)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (cut remaining : Nat) :
    privateCarriedResolve M rootSeed
        (cfrDChildParentProfiles M clock cut seeds trunks children fallback)
        (cfrDChildPublicResolver M clock cut seeds trunks children)
        unknown who cut remaining =
      privateIterationLaw M rootSeed
        (cfrDChildParentProfiles M clock cut seeds trunks children fallback)
        unknown who (cut + remaining) := by
  simp only [privateCarriedResolve, privateCarriedPrefix, privateIterationLaw,
    FinDist.map_eq_bind, FinDist.bind_bind, FinDist.pure_bind,
    cfrDChildResolvedTail_eq, privateIterationState]
  apply FinDist.bind_congr
  intro n _
  have before : ∀ info, clock.depth who info < cut →
      cfrDChildParentProfiles M clock cut seeds trunks children fallback n who info =
        trunks n who info := by
    intro info earlier
    simp only [cfrDChildParentProfiles, cfrDDepthProfile, cfrDDepthTrunk,
      decide_eq_true_eq, if_pos earlier]
  rw [cfrD_run_cut_congr M clock unknown who _ (trunks n who) cut before]
  exact cfrDChild_sampling_eq M clock hrecall cut remaining (seeds n) (trunks n)
    (children n) fallback unknown who

/-- Retaining the newly drawn private profile and propagating its MODEL PBS
from the stored past does not change the established child-sampling law. -/
theorem cfrDChildResolveStep_history (clock : ObservationClock M) (hrecall : M.PerfectRecall)
    (rootSeed : FinDist K) (seeds : K → FinDist J)
    (trunks : K → Profile M.behavioralSignature)
    (children : K → J → Profile M.behavioralSignature) (fallback : (who : Fin 2) → M.Policy who)
    (unknown : Profile M.behavioralSignature) (who : Fin 2) (cut remaining : Nat) :
    (privateCarriedResolveStep M rootSeed
        (cfrDChildParentProfiles M clock cut seeds trunks children fallback)
        (cfrDChildPublicResolver M clock cut seeds trunks children)
        unknown who cut remaining).map (fun state => state.history) =
      privateIterationLaw M rootSeed
        (cfrDChildParentProfiles M clock cut seeds trunks children fallback)
        unknown who (cut + remaining) := by
  rw [privateCarriedResolveStep_history, cfrDChildResolve_eq M clock hrecall]

end GameTheory.ReBeL
