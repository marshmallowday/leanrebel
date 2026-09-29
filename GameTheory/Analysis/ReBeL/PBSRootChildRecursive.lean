/-
# Actual recursive solving inside a rooted child and at its decoded PBS

The internal solve retains its own protocol-dependent noise, fallback and
budget. Decoding preserves its behavior at the actual child law. A separate
fresh original-game solve has its own Nash proof; their scalar values are
close, but their algorithms, policies and private draws need not coincide.
-/

import GameTheory.Analysis.ReBeL.PBSRootChildDecode
import GameTheory.Analysis.ReBeL.PBSRecursiveValueStability

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe u
variable {E : ExecutionProtocol.{0, u, u} (Fin 2)}
variable (M : InformationModel.{0, u, u, u, u, u} E)
variable {outerObs : List M.PublicSignal}
variable (outer : PublicBelief (fullInformation.{0, u, u, u, u, u} M).toInfoSignals outerObs)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- The internal recursive call uses the same finite rooted history carrier
as the parent solver, including all legal off-path histories. -/
local instance rootChildRecursiveHistory : Fintype (pbsRootProtocol outer.law).History :=
  pbsRootHistoryFintype outer.law

/-- Decode the actual recursive call on its existing child posterior.
No new administrative draw is inserted into the execution horizon. -/
def pbsRootChildRecursiveProfile
    (noise : PBSRecursiveDepthNoise.{u}) (cuts : List Nat)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    {observations : List M.PublicSignal} {past : List (Option (List M.PublicSignal))}
    (child : PublicBelief (pbsRootFullInformation M outer.law).toInfoSignals
      (some observations :: past)) (tolerance : ℝ) :
    Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature :=
  pbsRootDecodeProfile M outer.law (outerObs.length - 1)
    (pbsRecursiveDepth noise cuts (pbsRootProtocol outer.law)
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law)
      (pbsRootDepthFallback M outer.law fallback) (pbsRootPayoff outer.law payoff)
      bound child tolerance)

/-- Decode the same finite private draw as the internal child solve.
This is not a draw from a separately recomputed original-game solver. -/
def pbsRootChildRecursiveDraw
    (noise : PBSRecursiveDepthNoise.{u}) (cuts : List Nat)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    {observations : List M.PublicSignal} {past : List (Option (List M.PublicSignal))}
    (child : PublicBelief (pbsRootFullInformation M outer.law).toInfoSignals
      (some observations :: past)) (tolerance : ℝ) :
    FinDist (Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature) :=
  (pbsRecursiveDepthDraw noise cuts
    (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law)
    (pbsRootDepthFallback M outer.law fallback) (pbsRootPayoff outer.law payoff)
    bound child tolerance).map (pbsRootDecodeProfile M outer.law (outerObs.length - 1))

/-- Decode the actual table entry selected by the existing parent, including
its factual posterior and mass-scaled child request. No tolerance is reset. -/
theorem pbsRootChildRecursive_selected
    (noise : PBSRecursiveDepthNoise.{u}) (cuts : List Nat)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (trunk : Profile (pbsRootFullInformation M outer.law).behavioralSignature)
    (cut : Nat) (loss : ℝ)
    (observations : List M.PublicSignal) (past : List (Option (List M.PublicSignal)))
    (possible : CFRDFactualChildPossible
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law)
      trunk cut cuts.sum (some observations :: past)) :
    let child := cfrDFactualChildBelief
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law)
      trunk cut cuts.sum (some observations :: past) possible
    pbsRootDecodeProfile M outer.law (outerObs.length - 1)
      (cfrDComposedChildTable
        (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law) trunk
        (pbsRootDepthFallback M outer.law fallback) cut cuts.sum loss
        (pbsRecursiveDepth noise cuts (pbsRootProtocol outer.law)
          (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law)
          (pbsRootDepthFallback M outer.law fallback) (pbsRootPayoff outer.law payoff) bound)
        (some observations :: past)) =
      pbsRootChildRecursiveProfile M outer noise cuts fallback payoff bound child
        (child.law.positiveMassFloor * loss) := by
  intro child
  simp only [pbsRootChildRecursiveProfile, cfrDComposedChildTable, dif_pos possible]

/-- The parent's actual public splice continues with the decoded selected
recursive child, for all later fuel. The old outer cut still decodes local AOHs. -/
theorem pbsRootChildRecursive_parent_law
    (noise : PBSRecursiveDepthNoise.{u}) (cuts : List Nat)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    (trunk : Profile (pbsRootFullInformation M outer.law).behavioralSignature)
    (cut : Nat) (loss : ℝ)
    (observations : List M.PublicSignal) (past : List (Option (List M.PublicSignal)))
    (possible : CFRDFactualChildPossible
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law)
      trunk cut cuts.sum (some observations :: past)) (steps : Nat) :
    let rootModel := pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law
    let rootFallback := pbsRootDepthFallback M outer.law fallback
    let solve : PBSChildSolve rootModel :=
      pbsRecursiveDepth noise cuts (pbsRootProtocol outer.law) rootModel rootFallback
        (pbsRootPayoff outer.law payoff) bound
    let child := cfrDFactualChildBelief rootModel trunk cut cuts.sum
      (some observations :: past) possible
    (child.law.bind ((pbsRootFullInformation M outer.law).runBehavioralFrom
      (cfrDComposedChildProfile rootModel trunk rootFallback cut cuts.sum loss solve) steps)).map
        History.state =
      ((pbsRootChildBelief M outer.law child).law.bind
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom
          (pbsRootChildRecursiveProfile M outer noise cuts fallback payoff bound child
            (child.law.positiveMassFloor * loss)) steps)).map some := by
  intro rootModel rootFallback solve child
  have law := cfrDComposedChildProfile_beliefLaw rootModel trunk rootFallback
    cut cuts.sum loss solve child
    (cfrDFactualChildBelief_atCut rootModel trunk cut cuts.sum
      (some observations :: past) possible) steps
  have mapped := congrArg
    (fun law : FinDist (pbsRootProtocol outer.law).History => law.map History.state) law
  exact mapped.trans (by
    rw [PublicBelief.continuationLaw, pbsRootChild_continuation_law M outer.law
      (outerObs.length - 1) (pbsRoot_publicBelief_depth M outer),
      pbsRootChildRecursive_selected M outer noise cuts fallback payoff bound trunk
        cut loss observations past possible])

/-- The internal algorithm supplies its Nash guarantee, which transfers to
the decoded child joint law at the unchanged remaining horizon. -/
theorem pbsRootChildRecursiveProfile_isNash
    (noise : PBSRecursiveDepthNoise.{u}) (noiseBound : PBSRecursiveDepthNoiseBound noise)
    (cuts : List Nat) (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h who => payoff who h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ who h, |payoff who h| ≤ bound)
    {observations : List M.PublicSignal} {past : List (Option (List M.PublicSignal))}
    (child : PublicBelief (pbsRootFullInformation M outer.law).toInfoSignals
      (some observations :: past)) (tolerance : ℝ) (positive : 0 < tolerance) :
    IsNash (behavioralBeliefForm (fullInformation.{0, u, u, u, u, u} M)
      (pbsRootChildBelief M outer.law child) cuts.sum)
      (euPreferenceWithin tolerance (fun h who => payoff who h))
      (pbsRootChildRecursiveProfile M outer noise cuts fallback payoff bound child tolerance) := by
  have equilibrium := @pbsRecursiveDepth_isNash.{u} noise noiseBound cuts
    (pbsRootProtocol outer.law)
    (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law)
    inferInstance inferInstance (pbsRootDepthFallback M outer.law fallback)
    (pbsRootPayoff outer.law payoff) (pbsRootPayoff_zeroSum outer.law payoff zeroSum)
    bound nonneg (fun who => pbsRootPayoff_abs_le outer.law payoff who bound nonneg (bounded who))
    (some observations :: past) child tolerance positive
  exact pbsRootChild_isNash M outer.law (outerObs.length - 1)
    (pbsRoot_publicBelief_depth M outer) child _ payoff cuts.sum tolerance equilibrium

/-- The actual decoded private draw realizes the decoded internal average
against every original seed-blind opponent, for arbitrary execution fuel. -/
theorem pbsRootChildRecursiveDraw_law
    (noise : PBSRecursiveDepthNoise.{u}) (cuts : List Nat)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ) (bound : ℝ)
    {observations : List M.PublicSignal} {past : List (Option (List M.PublicSignal))}
    (child : PublicBelief (pbsRootFullInformation M outer.law).toInfoSignals
      (some observations :: past)) (tolerance : ℝ)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (who : Fin 2) (steps : Nat) :
    (pbsRootChildRecursiveDraw M outer noise cuts fallback payoff bound child tolerance).bind
      (fun chosen => (pbsRootChildBelief M outer.law child).law.bind
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom
          (Profile.update unknown who (chosen who)) steps)) =
      (pbsRootChildBelief M outer.law child).law.bind
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom
          (Profile.update unknown who
            (pbsRootChildRecursiveProfile M outer noise cuts fallback payoff bound
              child tolerance who)) steps) := by
  unfold pbsRootChildRecursiveDraw
  rw [FinDist.bind_map]
  have equal := congrArg
    (fun law : FinDist (pbsRootProtocol outer.law).History => law.map History.state)
    (pbsRecursiveDepthDraw_law noise cuts
      (pbsRootInformation (fullInformation.{0, u, u, u, u, u} M) outer.law)
      (pbsRootDepthFallback M outer.law fallback) (pbsRootPayoff outer.law payoff)
      bound child tolerance (pbsRootBehavioralFullProfile M outer.law unknown) who steps)
  rw [FinDist.map_bind] at equal
  simp_rw [pbsRootChild_own_law M outer.law (outerObs.length - 1)
    (pbsRoot_publicBelief_depth M outer) child] at equal
  rw [← FinDist.map_bind] at equal
  apply FinDist.map_injective (Option.some_injective E.History)
  exact equal

/-- The internal finite private solve secures its own decoded model value
with its explicit tolerance against any fixed original opponent. -/
theorem pbsRootChildRecursiveDraw_security
    (noise : PBSRecursiveDepthNoise.{u}) (noiseBound : PBSRecursiveDepthNoiseBound noise)
    (cuts : List Nat) (fallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h who => payoff who h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ who h, |payoff who h| ≤ bound)
    {observations : List M.PublicSignal} {past : List (Option (List M.PublicSignal))}
    (child : PublicBelief (pbsRootFullInformation M outer.law).toInfoSignals
      (some observations :: past)) (tolerance : ℝ) (positive : 0 < tolerance)
    (unknown : Profile (fullInformation.{0, u, u, u, u, u} M).behavioralSignature)
    (who : Fin 2) :
    let decoded := pbsRootChildBelief M outer.law child
    let profile := pbsRootChildRecursiveProfile M outer noise cuts fallback payoff bound
      child tolerance
    (decoded.law.bind
      ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom profile cuts.sum)).expect
        (payoff who) - tolerance ≤
      (pbsRootChildRecursiveDraw M outer noise cuts fallback payoff bound child tolerance).expect
        (fun chosen => (decoded.law.bind
          ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom
            (Profile.update unknown who (chosen who)) cuts.sum)).expect (payoff who)) := by
  intro decoded profile
  have equal := congrArg (fun law : FinDist E.History => law.expect (payoff who))
    (pbsRootChildRecursiveDraw_law M outer noise cuts fallback payoff bound
      child tolerance unknown who cuts.sum)
  rw [FinDist.expect_bind] at equal
  rw [equal]
  exact @behavioralNash_model_security.{u} E (fullInformation.{0, u, u, u, u, u} M)
    observations decoded profile unknown who cuts.sum payoff tolerance zeroSum
    (pbsRootChildRecursiveProfile_isNash M outer noise noiseBound cuts fallback payoff zeroSum
      bound nonneg bounded child tolerance positive)

/-- A fresh original solve need not reproduce the internal rooted computation.
Its scalar value is within the sum of their two independent solve tolerances
on the decoded joint PBS. Only their remaining horizons must agree. -/
theorem pbsRootChildRecursive_fresh_value
    (internalNoise freshNoise : PBSRecursiveDepthNoise.{u})
    (internalNoiseBound : PBSRecursiveDepthNoiseBound internalNoise)
    (freshNoiseBound : PBSRecursiveDepthNoiseBound freshNoise)
    (internalCuts freshCuts : List Nat) (horizon : internalCuts.sum = freshCuts.sum)
    (internalFallback freshFallback : Profile M.strategicSignature)
    (payoff : Fin 2 → E.History → ℝ) (zeroSum : IsZeroSum (fun h who => payoff who h))
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ who h, |payoff who h| ≤ bound)
    {observations : List M.PublicSignal} {past : List (Option (List M.PublicSignal))}
    (child : PublicBelief (pbsRootFullInformation M outer.law).toInfoSignals
      (some observations :: past)) (internalError freshError : ℝ)
    (internalPositive : 0 < internalError) (freshPositive : 0 < freshError) (who : Fin 2) :
    let decoded := pbsRootChildBelief M outer.law child
    let internal := pbsRootChildRecursiveProfile M outer internalNoise internalCuts
      internalFallback payoff bound child internalError
    let fresh := pbsRecursiveDepth freshNoise freshCuts E M freshFallback payoff bound
      decoded freshError
    |(decoded.law.bind
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom internal internalCuts.sum)).expect
        (payoff who) -
      (decoded.law.bind
        ((fullInformation.{0, u, u, u, u, u} M).runBehavioralFrom fresh freshCuts.sum)).expect
        (payoff who)| ≤ internalError + freshError := by
  intro decoded internal fresh
  have internalNash := pbsRootChildRecursiveProfile_isNash M outer internalNoise
    internalNoiseBound internalCuts internalFallback payoff zeroSum bound nonneg bounded
    child internalError internalPositive
  have freshNash := @pbsRecursiveDepth_isNash.{u} freshNoise freshNoiseBound freshCuts E M
    inferInstance inferInstance freshFallback payoff zeroSum bound nonneg bounded
    observations decoded freshError freshPositive
  rw [← horizon] at freshNash
  have estimate := @behavioralNash_crossRoot_value_abs_le.{u} E
    (fullInformation.{0, u, u, u, u, u} M) observations observations decoded decoded
    internal fresh who internalCuts.sum payoff zeroSum internalError freshError 0
    internalNash freshNash
    (fun _ => by simpa only [sub_self, abs_zero] using (le_refl (0 : ℝ)))
  rw [add_zero, horizon] at estimate
  exact estimate

end GameTheory.ReBeL
