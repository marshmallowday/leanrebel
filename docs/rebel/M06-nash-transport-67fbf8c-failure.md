# Nash transport 67fbf8c — failed, not accepted

Candidate: 67fbf8c81259c980ef71aced53a23fdfa6730d5a.
Original batch: 481c5ab492be7326b82b3238bb2deb2dbbfd7418.
Last fully accepted dependency: 7f5526ca40282dd11a42301e5d12cad9ac3eb37e.

## Exact-SHA evidence

| Run | Job | Result |
| --- | --- | --- |
| [CI36437007977](https://github.com/marshmallowday/leanrebel/actions/runs/36437007977) | 108977417577 | failure |
| [checks36437008209](https://github.com/marshmallowday/leanrebel/actions/runs/36437008209) | 108977418562 | failure |
| [target36437008002](https://github.com/marshmallowday/leanrebel/actions/runs/36437008002) | 108977418085 | failure |
| [inventory36437007856](https://github.com/marshmallowday/leanrebel/actions/runs/36437007856) | 108977417046 | success |

Read all four complete decoded logs through the GitHub plugin. CI and target
still report the original universe constraint at PBSRecursiveNashTransport:101
and its two dependent diagnostics. The previous repair did NOT resolve it.
checks failed earlier, at the unchanged static architecture gate:
LIBRARY_LINES_OVER_100=0 and TRANSPORT_ANALYSIS_SOURCE=1 (expected 0).
The previous repair introduced the counted tactic in the Analysis tree.
Its audit pattern explicitly counts cast/HEq/change/selected Eq recursors.
No permission or audit exception is requested; the offending tactic is removed.

Inventory passed all 215 Python tests in 9.192s. checks never reached its Python
suite, rational runtime or Lean compiler. Do not report their previous-SHA
success as this candidate's result. Full build, all downstream consumers,
normal/slow lint and transitive axioms remain unaccepted. No axiom records
were produced by the failed validation jobs.

Artifact metadata checked: target10976023031, global10975514067,
source10975693957. CI/inventory have none. All artifact metadata pins this SHA.
ZIP contents were not read; the complete decoded logs are the evidence.

## Complete CI/target compiler diagnostics

```text
error: GameTheory/Analysis/ReBeL/PBSRecursiveNashTransport.lean:101:0: stuck at solving universe constraint
  max (max ?u.146 ?u.147) ?u.148 =?= u
while trying to unify
  InformationModel.{0, max (max ?u.146 (max ?u.148 ?u.146) ?u.147) (max (max ?u.148 ?u.146) ?u.147) ?u.146,
      max (max ?u.146 (max ?u.148 ?u.146) ?u.147) (max (max ?u.148 ?u.146) ?u.147) ?u.146, u,
      max (max (max ?u.148 ?u.146) ?u.147) ?u.146, max (max ?u.148 ?u.146) ?u.147}
    E : Type
    (max
        (max
            (max (max (max (max ?u.146 (max ?u.148 ?u.146) ?u.147) (max (max ?u.148 ?u.146) ?u.147) ?u.146) (u + 1))
                ((max (max (max ?u.148 ?u.146) ?u.147) ?u.146) + 1))
            ((max (max ?u.148 ?u.146) ?u.147) + 1))
        0)
with
  InformationModel E : Type (u + 1)
error: GameTheory/Analysis/ReBeL/PBSRecursiveNashTransport.lean:147:19: Unknown identifier `pbsRecursiveDepth_replacement_le`
error: GameTheory/Analysis/ReBeL/PBSRecursiveNashTransport.lean:145:19: unsolved goals
E : ExecutionProtocol (Fin 2)
M : InformationModel E
inst✝¹ : Fintype E.History
inst✝ : (who : Fin 2) → Fintype (E.Action who)
noise : PBSRecursiveDepthNoise
noiseBound : PBSRecursiveDepthNoiseBound noise
cuts : List ℕ
fallback : Profile M.strategicSignature
payoff : Fin 2 → E.History → ℝ
zeroSum : IsZeroSum fun h player ↦ payoff player h
bound : ℝ
nonneg : 0 ≤ bound
bounded : ∀ (player : Fin 2) (h : E.History), |payoff player h| ≤ bound
observations : List M.PublicSignal
belief : PublicBelief (fullInformation M).toInfoSignals observations
tolerance : ℝ
positive : 0 < tolerance
old : Profile (fullInformation M).behavioralSignature
who : Fin 2
fresh : Profile (fullInformation M).behavioralSignature :=
  pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance
⊢ recursivePolicyValueChange M old fresh fresh who cuts.sum belief.law (payoff who) ≤ tolerance
```

## Combined repair and type review

The prior body-only universe annotations left the declaration's model
applications implicit. This repair also explicitly supplies all six universe
arguments to fullInformation in both recursive theorem signatures, including
the Nash-transport RHS. It specifies the transport universe/protocol there and
at the native envelope's same-shaped use. The generic helper and actual solver
theorem are applied with explicit implicit arguments: protocol, model, finite
instances and observation index. This avoids recovering the original model's
carrier universes from the max-universe full-AOH result.
The compiler reports the whole declaration, not a subexpression trace; the
effect of these annotations remains to be confirmed by the next Actions run.

The signed-value proof unfolds recursivePolicyValueChange directly and uses
expect_sub/expect_bind. It introduces no cast or new equality premise. The
forbidden tactic is gone; the existing architecture audit is unchanged.

Re-read the actual fullInformation/fullSignals and behavioralBeliefForm
definitions, pbsRecursiveDepth_isNash's complete argument order, signed-value
definition, native recomputed loss/budget, and all new downstream consumers.
Checked the same uniform u for E and M; exact full-information PublicBelief
index; explicit observation argument; unchanged History/action finite instances;
old-minus-new payoff direction; cuts.sum and all stage/remaining/late fuel;
dependent E/K/payoff arguments in the native loss rewrite; tail alignment
induction over the native full-state next-law. Re-read the concrete
three-level/model-opponent and two-stage examples: total fuel 3, second cuts
[1,1], and the old [1] schedule's negative alignment control are preserved.

The theorem propositions and runtime definitions are unchanged except for
explicit universe/implicit-argument spelling. All new core lines are within
100 columns. The changed sources have zero matches of the existing transport
pattern after removing comments. This is a static source check, not execution
of phase2-audit or a Lean compilation. The next same-SHA Actions must establish
full compilation, normal/slow lint, architecture and complete axiom acceptance.

No workflow, audit criterion, heartbeat bound, test, solver behavior, accepted
source pin or frozen coverage.json was changed. M06 and the remaining
SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 obligations remain incomplete.
