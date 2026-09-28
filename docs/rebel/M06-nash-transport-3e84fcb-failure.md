# Nash transport 3e84fcb — failed, not accepted

Candidate: 3e84fcbf0fec06e3a054f899b85208b36a42432c.
Original batch: 481c5ab492be7326b82b3238bb2deb2dbbfd7418.
Last fully accepted dependency: 7f5526ca40282dd11a42301e5d12cad9ac3eb37e.

## Exact-SHA evidence

| Run | Job | Result |
| --- | --- | --- |
| [CI36444326613](https://github.com/marshmallowday/leanrebel/actions/runs/36444326613) | 109002569475 | failure |
| [checks36444326452](https://github.com/marshmallowday/leanrebel/actions/runs/36444326452) | 109002569549 | failure |
| [target36444326569](https://github.com/marshmallowday/leanrebel/actions/runs/36444326569) | 109002569479 | failure |
| [inventory36444326767](https://github.com/marshmallowday/leanrebel/actions/runs/36444326767) | 109002569972 | success |

Read all four complete decoded job logs through the GitHub plugin. All three
Lean jobs now contain only the common diagnostic below. The previous universe
constraint and unknown-declaration diagnostics are absent; the general
recursive replacement theorem is available to the specialization. This does
not establish full compilation of the module or its consumers.

checks: LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0,
RATIONAL_RUNTIME_PASS, 215 Python tests in 9.460s. Thus the earlier architecture
violation is resolved with the unchanged audit. Inventory independently passed
215 tests in 11.435s. Full build, downstream native-budget/example compilation,
all normal/slow lint and transitive axiom acceptance were not reached.
No axiom records were emitted by these failed jobs.

Artifact metadata inspected: target10980426150, global10982110082,
source10979564604. All pin this candidate; CI/inventory have no artifacts.
ZIP contents were not read. Complete decoded logs are the diagnostic evidence.

## Complete common diagnostic

```text
error: GameTheory/Analysis/ReBeL/PBSRecursiveNashTransport.lean:144:2: Type mismatch: After simplification, term
  estimate
 has type
  recursivePolicyValueChange M old (pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance) fresh who
      cuts.sum belief.law (payoff who) ≤
    tolerance +
      bound *
        nashReplacementTransport (fullInformation M) old
          (pbsRecursiveDepth noise cuts E M fallback payoff bound belief tolerance) fresh who cuts.sum belief.law
          belief.law
but is expected to have type
  recursivePolicyValueChange M old fresh fresh who cuts.sum belief.law (payoff who) ≤ tolerance
```

## Repair and precommit type review

In the model-opponent specialization, estimate retained the solver expression
as its second profile while its opponent argument used the local let-name
fresh. The zero-transport simplification did not match those two presentations.
The repair assigns estimate its complete intended type with fresh in both
coordinates. Lean's ordinary definitional equality connects the solver result
to that local abbreviation before simplification. A fully instantiated
nashReplacementTransport_same equality then rewrites that exact expression to
zero; mul_zero/add_zero finish. No new policy-equality assumption is introduced.

Checked the actual helper signatures and the complete argument order:
uniform u, original E/M, fullInformation's six explicit universes, same
observation-indexed belief, old policy, fresh policy/opponent, player,
cuts.sum and belief.law in both root positions. Re-read the entire native
envelope, horizon-aligned budget induction, signed-loss and initial-security
consumers and the concrete model-opponent/two-stage examples. They retain the
actual saved-PBS indices, E/K/payoff arguments, native forward law, total fuel 3
and negative horizon control. No other same-profile zero-transport
simplification occurs in these new consumers.

Only this theorem's proof changes. All theorem signatures, definitions,
instances, mathematical premises, examples and tests remain byte-for-byte
unchanged. The edited core has no lines over 100 columns or counted transport
tokens after removing comments. Workflows, architecture/audit criteria,
heartbeat bounds, solver behavior and accepted source pins remain unchanged.
This review is static: it is not a Lean compilation or execution of the audits.
New-SHA Actions must verify the repair and all previously unreached consumers.

M06 remains incomplete. Computed root/opponent/support budgets are not a
general small fresh-chain rate; SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 remain
pending. The accepted 7f5526c evidence is not reused for the candidate.
