# Query-cost candidate fb27d899: compiler feedback and proof repair

Candidate: fb27d899a6f74359cdb28d1bed9790f16934d6cf.
Accepted dependency remains f51ac5a306943bcaf4203a2b5e564b3f3f307d76.
M06 and the query-cost batch remain unaccepted pending the repair SHA.

## Same-SHA evidence

All four workflow head SHAs were checked. CI36488890248/job109152430323,
checks36488890157/job109152429832 and target36488890162/job109152429835
failed with the identical complete diagnostic block below.
Inventory36488890193/job109152429770 and source snapshot109152430088 succeeded.
The complete decoded job logs were obtained, not just annotation excerpts.
No axiom records were reached in the three compiler logs.

FinDistRangeError compiled in CI2.4s/checks2.2s/target2.3s.
Checks reported LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0,
RATIONAL_RUNTIME_PASS and230 tests in10.193s. Inventory ran230 tests in10.535s.
These do not accept downstream security/examples, full lint or axioms.

Artifact metadata: target11001381193 (5219 bytes),
global11000904085 (21363 bytes), source11000900658 (2915299 bytes).
CI and inventory have no artifacts. ZIP contents were not read; full
decoded logs are the diagnostic evidence. No workflow was stopped or rerun.

## Repair and complete consumer review

Only two proof expressions in pbsRecursiveReplacement_inactive change.
The some branch's rw [stored] rewrote the dependent saved Option but left
(some _belief).isSome=true. Explicit rfl closes its definitional Boolean
equality. In the none branch, cases already specialized the resolver input;
the compiler reports stored unused in simp only, so that argument is removed.
The linter stays enabled. The previous static review incorrectly assumed
rw would finish the Boolean equality and failed to detect the redundant simp
argument; both failures are recorded rather than described as type success.

Actual resolver/configStage and selected-late expectation signatures were
rechecked. The Option payload remains the PBS indexed by this state's full
public trace. No cast, original/full carrier substitution, new instance or
assumption is introduced. Uniform protocol universes and independent memory
universe remain intact. The stored proof has the same state and Option carrier.

All downstream query-mass, native-visit induction, initial inheritance,
finite-parent and whole-chain min consumers, and all four examples were
re-read. They preserve OLD-NEW direction, lower/upper interval order,
same native next-state law, tail fuel and Fin t parent plays. Both concrete
parent horizons remain3; zero stage fuel still retains late2. There are
no other stored/isSome proof branches in the new consumers needing this
repair. Definitions, theorem signatures, instances, other proofs, examples,
tests, registration, workflows, heartbeat limits and audit rules are unchanged.
Reverse replacement of the two edited expressions reproduces the parent
Lean file exactly. Core line widths remain at most100. This is static
review, not Lean compilation or execution of the audit/Python suite.

Expected validation surface remains190 targets,152 targeted/292 global
modules,230 tests. All gates must pass on the new identical SHA before
acceptance. Frozen historical coverage and paper acceptance pins are unchanged.

## Complete common decoded diagnostics

```text
error: GameTheory/Analysis/ReBeL/PBSRecursiveQueryCost.lean:58:42: unsolved goals
E : ExecutionProtocol (Fin 2)
M : InformationModel E
K : Type v
inst✝¹ : Fintype E.History
inst✝ : (who : Fin 2) → Fintype (E.Action who)
fallback : Profile M.strategicSignature
payoff : Fin 2 → E.History → ℝ
bound : ℝ
initial : K → Profile (fullInformation M).behavioralSignature
unknown : Profile (fullInformation M).behavioralSignature
who : Fin 2
config : PBSRecursiveResolveConfig
remaining : ℕ
state : PrivateIterationState (fullInformation M) (CarriedResolveMemory (fullInformation M) K)
inactive : state ∉ pbsRecursiveQueryEvent M config.fuel
value : E.History → ℝ
live : cfrDCutLive config.fuel state.history = true
stageLive : cfrDCutLive (pbsRecursiveConfigStage M fallback payoff bound initial config).fuel state.history = true
_belief :
  PublicBelief (fullInformation M).toInfoSignals (publicTrace (fullInformation M).toInfoSignals state.history.trace)
stored : state.belief = some _belief
⊢ (some _belief).isSome = true
error: GameTheory/Analysis/ReBeL/PBSRecursiveQueryCost.lean:56:37: This simp argument is unused:
  stored

Hint: Omit it from the simp argument list.
  [apply] simp only [pbsRecursiveConfigStage, pbsRecursiveDepthStage, pbsRecursiveDepthResolver, FinDist.expect_pure,
    carriedSelectedTail, sub_self]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```
