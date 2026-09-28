# Nash transport 481c5ab — failed, not accepted

Candidate: 481c5ab492be7326b82b3238bb2deb2dbbfd7418.
Last fully accepted dependency: 7f5526ca40282dd11a42301e5d12cad9ac3eb37e.
The accepted parent evidence does not validate this candidate.

## Exact-SHA Actions evidence

| Run | Job | Result |
| --- | --- | --- |
| [CI36429841350](https://github.com/marshmallowday/leanrebel/actions/runs/36429841350) | 108952888310 | failure |
| [checks36429842278](https://github.com/marshmallowday/leanrebel/actions/runs/36429842278) | 108952891557 | failure |
| [target36429841986](https://github.com/marshmallowday/leanrebel/actions/runs/36429841986) | 108952891103 | failure |
| [inventory36429841632](https://github.com/marshmallowday/leanrebel/actions/runs/36429841632) | 108952888938 | success |

Read all four complete decoded job logs through the GitHub plugin.
All three Lean jobs report the same primary universe constraint at
PBSRecursiveNashTransport.lean:101, followed by an unknown declaration at
137 and an unclosed dependent consumer at 135. No additional Lean diagnostics
were present. Full build, downstream budget/examples, full normal/slow lint
and transitive axiom acceptance were not reached. No axiom record was emitted.

checks has LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0,
RATIONAL_RUNTIME_PASS and 215 Python tests in 9.419s. Inventory independently
passed 215 tests in 10.226s. These do not establish Lean acceptance.

Artifact metadata inspected: target10973795279, global10974480936,
source10973008281, all pinning this candidate SHA. CI and inventory have no
artifacts. ZIP contents were not read; evidence is the complete decoded logs.

## Complete common compiler diagnostic

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
error: GameTheory/Analysis/ReBeL/PBSRecursiveNashTransport.lean:137:19: Unknown identifier `pbsRecursiveDepth_replacement_le`
error: GameTheory/Analysis/ReBeL/PBSRecursiveNashTransport.lean:135:19: unsolved goals
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

## Repair and precommit type review

The theorem body left a max-universe constraint unresolved while connecting
the recursive solver, the full-information model and the generic Nash bound.
The previous static review checked the declared uniform carrier but failed to
eliminate this elaboration ambiguity. The diagnostic does not pinpoint a
single subexpression inside that theorem, so this repair addresses both the
helper instantiation and the expectation conversion rather than claiming an
unverified precise elaborator trace.

The replacement proof now gives the solver's equilibrium its full expected
IsNash type, fixes both helpers at universe u and protocol E, and explicitly
changes the signed-value goal to its two history expectations before rewriting
expect_sub/expect_bind. It no longer asks simp to instantiate the
full-information signed-value definition against an inferred carrier.
The model-law specialization and downstream native-envelope application also
fix the recursive theorem's universe and E. The downstream signed-value
identity now supplies E, K and the payoff argument explicitly.

Re-read the actual pbsRecursiveDepth_isNash signature, recursivePolicyValueChange,
recomputed loss identity/budget/security and all three new-module consumers.
Checked original versus fullInformation model, dependent saved-belief index,
profile and own-policy argument order, old-minus-new direction, full fuel
cuts.sum = stage + remaining, native next-state law, tail alignment induction,
finite History/action instances and concrete three-level/two-stage examples.
The example's total fuel remains 3; the deliberately misaligned old schedule
remains a negative control. Definitions, theorem statements and mathematical
premises are unchanged. The two edited Lean cores stay within 100 columns.

This is static type review, NOT Lean compilation. New-SHA Actions must establish
that the explicit instantiations resolve the constraint and that all consumers,
normal/slow lint and complete axiom records pass. No workflow, audit criterion,
heartbeat bound, solver definition, test or pinned accepted source is changed.
M06 and SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 remain incomplete.
