/-
# Singleton knowledge and full histories

Perfect information means identification of the complete realized history, not
just its final world state. A syntactically impossible AOH has an empty fiber,
so singleton claims below explicitly use a realized observation.
-/

import GameTheory.ReBeL.Information

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol

universe uι us ua
variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

/-- Exact observation of histories is equivalent to having no two histories
in any full-information fiber. This is a criterion, not an assumed certificate. -/
theorem infoOf_injective_iff_fibers_subsingleton (S : InfoSignals E) (i : ι) :
    Function.Injective (fun history : E.History => (fullSignals S).infoOf i history.trace) ↔
      ∀ info, Subsingleton (InformationFiber S i info) := by
  constructor
  · intro injective info
    refine ⟨?_⟩
    intro first second
    apply Subtype.ext
    exact injective (first.2.trans second.2.symm)
  · intro fibers first second equal
    have same := (fibers ((fullSignals S).infoOf i first.trace)).elim
      (⟨first, rfl⟩ : InformationFiber S i ((fullSignals S).infoOf i first.trace))
      (⟨second, equal.symm⟩ : InformationFiber S i ((fullSignals S).infoOf i first.trace))
    exact congrArg Subtype.val same

/-- At a realized observation, injectivity gives exactly one compatible history,
not merely a subsingleton that could be empty. -/
theorem existsUnique_history_of_injective (S : InfoSignals E) (i : ι)
    (injective : Function.Injective
      (fun history : E.History => (fullSignals S).infoOf i history.trace))
    (history : E.History) :
    ∃! other : E.History,
      (fullSignals S).infoOf i other.trace = (fullSignals S).infoOf i history.trace :=
  ⟨history, rfl, fun _ equal => injective equal⟩

end GameTheory.ReBeL
