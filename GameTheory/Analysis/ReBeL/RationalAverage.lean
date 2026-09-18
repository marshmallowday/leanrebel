/-
# The rational averaged output refines own-reach averaging

Completed rounds, zero denominators and representative-history independence
are included. The correspondence is derived from primitive table certificates,
not an assumed averaging identity. The two-player corollary uses the canonical
approximate-Nash predicate on the actual interpreted numeric output.
-/

import GameTheory.Analysis.ReBeL.RationalIteration
import GameTheory.Analysis.ReBeL.CFRNash

noncomputable section

namespace GameTheory.ReBeL.Rational

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

section WeightedArithmetic

variable {K A : Type*} [Fintype K] [DecidableEq A]

/-- Exact weighted averaging commutes with interpretation, in both the
positive-total branch and the specified zero-total fallback branch. -/
theorem cast_weightedPolicy (fallback : A) (weights : K → ℚ) (laws : K → A → ℚ)
    (semanticWeights : ReachWeights K) (semanticLaws : K → FinDist A)
    (hweights : ∀ k, (weights k : ℝ) = semanticWeights.weight k)
    (hlaws : ∀ k a, (laws k a : ℝ) = (semanticLaws k).prob a) (a : A) :
    (weightedPolicy fallback weights laws a : ℝ) =
      (semanticWeights.average semanticLaws (FinDist.pure fallback)).prob a := by
  have hmass : ((∑ k, weights k : ℚ) : ℝ) = semanticWeights.mass := by
    unfold ReachWeights.mass
    push_cast
    exact Finset.sum_congr rfl fun k _ => hweights k
  have hpos : 0 < semanticWeights.mass ↔ 0 < ∑ k, weights k := by
    rw [← hmass]
    exact Rat.cast_pos
  by_cases positive : 0 < ∑ k, weights k
  · rw [weightedPolicy, if_pos positive,
      ReachWeights.average, dif_pos (hpos.mpr positive),
      FinDist.prob_bind, FinDist.expect_eq_sum]
    simp only [ReachWeights.prob_normalize]
    have hnum : ((∑ k, weights k * laws k a : ℚ) : ℝ) =
        ∑ k, semanticWeights.weight k * (semanticLaws k).prob a := by
      push_cast
      apply Finset.sum_congr rfl
      intro k _
      rw [hweights, hlaws]
    rw [Rat.cast_div, hnum, hmass, div_eq_mul_inv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rw [weightedPolicy, if_neg positive, ReachWeights.average,
      dif_neg (fun hp => positive (hpos.mp hp))]
    exact cast_pointMass fallback a

end WeightedArithmetic

universe ui us ua up uq uk
variable {ι : Type ui} {E : ExecutionProtocol.{ui, us, ua} ι}
variable (M : InformationModel.{ui, us, ua, up, uq, uk} E)

section InformationReach

variable [∀ who, DecidableEq (M.InfoState who)]

/-- The runtime's first enumerated representative has exactly the canonical
information-own-reach coefficient. Unrepresented observations have zero weight. -/
theorem informationReach_eq
    (G : HistoryTable E.History M.InfoState M.Choice)
    (hinfo : G.info = fun who history => M.infoOf who history.trace)
    (hpath : ∀ who history, G.ownPath who history = choicePath M who history.trace)
    (hcomplete : ∀ history, history ∈ G.histories) (hrecall : M.PerfectRecall)
    (numeric : Profile (tableSignature E.History M.InfoState M.Choice))
    (semantic : Profile M.behavioralSignature) (hreal : Realizes M numeric semantic)
    (who : ι) (info : M.InfoState who) :
    (G.informationReach numeric who info : ℝ) = informationOwnReach M semantic who info := by
  classical
  cases hfind : G.histories.find? (fun history => decide (G.info who history = info)) with
  | none =>
      have hnone : ¬ ∃ history : E.History, M.infoOf who history.trace = info := by
        rintro ⟨history, hmatch⟩
        apply (List.find?_eq_none.mp hfind) history (hcomplete history)
        apply decide_eq_true
        rw [congrFun (congrFun hinfo who) history]
        exact hmatch
      simp only [HistoryTable.informationReach, hfind]
      unfold informationOwnReach
      rw [dif_neg hnone]
      exact Rat.cast_zero
  | some history =>
      have hmatch : G.info who history = info :=
        of_decide_eq_true (List.find?_eq_some_iff_append.mp hfind).1
      have hmatch' : M.infoOf who history.trace = info := by
        rw [← congrFun (congrFun hinfo who) history]
        exact hmatch
      rw [HistoryTable.informationReach, hfind,
        ownReach_eq_playerReach M G hpath numeric semantic hreal who history,
        ← informationOwnReach_eq_player M hrecall semantic who history, hmatch']

end InformationReach

section Interpretation

variable [∀ who info, Fintype (M.Choice who info)]

/-- A represented behavioral profile supplies normalization of the exact
rational vectors, without a numerical tolerance or a guessed invariant. -/
theorem realizes_validPolicy
    (numeric : Profile (tableSignature E.History M.InfoState M.Choice))
    (semantic : Profile M.behavioralSignature) (hreal : Realizes M numeric semantic) :
    HistoryTable.ValidPolicy (H := E.History) numeric := by
  intro who info
  constructor
  · intro a
    have h : 0 ≤ (numeric who info a : ℝ) := by
      rw [hreal who info a]
      exact FinDist.prob_nonneg _ _
    exact_mod_cast h
  · have h : (∑ a, (numeric who info a : ℝ)) = 1 := by
      calc
        _ = ∑ a, (semantic who info).prob a :=
          Finset.sum_congr rfl fun a _ => hreal who info a
        _ = 1 := FinDist.sum_prob _
    exact_mod_cast h

/-- Interpret certified exact weights in the single canonical behavioral law. -/
def toBehavioral (numeric : Profile (tableSignature E.History M.InfoState M.Choice))
    (valid : HistoryTable.ValidPolicy (H := E.History) numeric) :
    Profile M.behavioralSignature :=
  fun who info => FinDist.ofWeights (fun a => (numeric who info a : ℝ))
    (fun a => by exact_mod_cast (valid who info).1 a)
    (by exact_mod_cast (valid who info).2)

/-- Pointwise representation determines the entire interpreted law exactly. -/
theorem toBehavioral_eq_of_realizes
    (numeric : Profile (tableSignature E.History M.InfoState M.Choice))
    (semantic : Profile M.behavioralSignature) (hreal : Realizes M numeric semantic)
    (valid : HistoryTable.ValidPolicy (H := E.History) numeric) :
    toBehavioral M numeric valid = semantic := by
  funext who info
  apply FinDist.ext_of_prob
  intro a
  rw [toBehavioral, FinDist.prob_ofWeights]
  exact hreal who info a

end Interpretation

section Average

variable [Fintype ι] [DecidableEq ι] [Fintype E.History]
variable [∀ who, DecidableEq (M.InfoState who)]
variable [∀ who info, Fintype (M.Choice who info)]
variable [∀ who info, DecidableEq (M.Choice who info)]

/-- The actual numeric average is the canonical private own-reach average
of the constructed CFR sequence. Uniform scaling cancels even at zero reach. -/
theorem average_realizes (G : HistoryTable E.History M.InfoState M.Choice)
    (clock : ObservationClock M) (payoff : ι → E.History → ℝ)
    (cert : TableCertificate M G clock payoff) (hrecall : M.PerfectRecall)
    (fallback : (who : ι) → M.Policy who) (horizon rounds : ℕ) [NeZero rounds] :
    Realizes M (G.average fallback horizon rounds)
      (ownReachAverageProfile M (fun _ => cfrIterationLaw rounds)
        (fun round : Fin rounds => cfrPlay M clock fallback payoff horizon round.val)
        fallback) := by
  intro who info choice
  let plays : Fin rounds → Profile M.behavioralSignature :=
    fun round => cfrPlay M clock fallback payoff horizon round.val
  let weights : ReachWeights (Fin rounds) :=
    ⟨fun round => informationOwnReach M (plays round) who info,
      fun round => (informationOwnReach_unitInterval M (plays round) who info).1⟩
  have hscale : 0 < (rounds : ℝ)⁻¹ := by
    apply inv_pos.mpr
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne rounds)
  have hscaled : ownReachWeights M (cfrIterationLaw rounds) plays who info =
      weights.scale (rounds : ℝ)⁻¹ hscale.le := by
    simp only [weights, ownReachWeights, ReachWeights.scale,
      cfrIterationLaw, FinDist.prob_ofWeights]
  calc
    _ = (weights.average (fun round => plays round who info)
          (FinDist.pure (fallback who info))).prob choice := by
      apply cast_weightedPolicy
      · intro round
        exact informationReach_eq M G cert.info_correct cert.path_correct
          cert.histories_complete hrecall _ _
          (play_realizes_cfrPlay M G clock payoff cert fallback horizon round.val) who info
      · intro round a
        exact play_realizes_cfrPlay M G clock payoff cert fallback horizon round.val who info a
    _ = ((weights.scale (rounds : ℝ)⁻¹ hscale.le).average
          (fun round => plays round who info) (FinDist.pure (fallback who info))).prob choice := by
      rw [ReachWeights.average_scale weights _ _ _ hscale]
    _ = _ := by
      rw [← hscaled]
      rfl

end Average

section TwoPlayers

variable {E₂ : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M₂ : InformationModel.{0, us, ua, up, uq, uk} E₂)
variable [Fintype E₂.History]
variable [∀ who, DecidableEq (M₂.InfoState who)]
variable [∀ who info, Fintype (M₂.Choice who info)]
variable [∀ who info, DecidableEq (M₂.Choice who info)]

/-- The interpreted rational solver output satisfies canonical approximate
Nash with the proved CFR error. Primitive table correctness must be discharged
by each concrete encoding; it is not a regret or equilibrium assumption. -/
theorem averagedOutput_isNash (G : HistoryTable E₂.History M₂.InfoState M₂.Choice)
    (clock : ObservationClock M₂) (payoff : Fin 2 → E₂.History → ℝ)
    (cert : TableCertificate M₂ G clock payoff) (hrecall : M₂.PerfectRecall)
    (fallback : (who : Fin 2) → M₂.Policy who)
    (hzero : IsZeroSum (fun history who => payoff who history))
    (bound : Fin 2 → ℝ) (hbound0 : ∀ who, 0 ≤ bound who)
    (hbound : ∀ who history, |payoff who history| ≤ bound who)
    (horizon rounds : ℕ) [NeZero rounds] :
    ∃ valid : HistoryTable.ValidPolicy (H := E₂.History) (G.average fallback horizon rounds),
      IsNash (M₂.toBehavioralGameForm horizon)
        (euPreferenceWithin
          (cfrCumulativeBound M₂ clock horizon 0 (bound 0) rounds / rounds +
            cfrCumulativeBound M₂ clock horizon 1 (bound 1) rounds / rounds)
          (fun history who => payoff who history))
        (toBehavioral M₂ (G.average fallback horizon rounds) valid) := by
  have hreal := average_realizes M₂ G clock payoff cert hrecall fallback horizon rounds
  let valid := realizes_validPolicy M₂ _ _ hreal
  refine ⟨valid, ?_⟩
  rw [toBehavioral_eq_of_realizes M₂ _ _ hreal valid]
  exact cfrAveragedProfile_isNash M₂ clock hrecall fallback payoff hzero
    bound hbound0 hbound horizon rounds

end TwoPlayers

end GameTheory.ReBeL.Rational
