/-
# Best-response objective in Section 3

The opponents are arbitrary fixed legal behavioral policies, not assumed to be
an equilibrium. The objective and deviations are canonical. Characterizing an
attained maximum is not a best-response solver or an equilibrium-existence
claim; those are separate later obligations.
-/

import GameTheory.ReBeL.Payoff
import GameTheory.Core.Response

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol

universe uι us ua
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

/-- An arbitrary candidate is a canonical best response exactly when its value
attains the greatest possible value over all legal replacements. No Nash
assumption, oracle, or hidden-state-access strategy is supplied. -/
theorem isBestResponse_iff_policyValue_greatest [Fintype ι] [DecidableEq ι]
    (M : InformationModel E) (reward : StageReward E) (horizon : Nat)
    (opponents : Profile M.behavioralSignature) (i : ι)
    (candidate : M.BehavioralPolicy i) :
    IsBestResponse (M.toBehavioralGameForm horizon)
        (euPreference (cumulativeUtility reward)) i opponents candidate ↔
      IsGreatest
        (Set.range fun replacement : M.BehavioralPolicy i =>
          policyValue M reward horizon (Profile.update opponents i replacement) i)
        (policyValue M reward horizon (Profile.update opponents i candidate) i) := by
  constructor
  · intro best
    refine ⟨⟨candidate, rfl⟩, ?_⟩
    intro value member
    obtain ⟨replacement, rfl⟩ := member
    exact best replacement
  · intro greatest replacement
    exact greatest.2 ⟨replacement, rfl⟩

end GameTheory.ReBeL
