# Stored-child proof failure at d71d661

Source d71d6610b477620378a2c0290d7b677f9c20020d on
rebel/m06-kernel-value-repair-20260927 was re-read before repair.
Plugin login marshmallowday has admin/push access; default main remains
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. Continue the current unfinished
M06 branch, without replacing any concurrent update or committing to main.

## Same-source Actions evidence

| Workflow | Run / job | Result |
| --- | --- | --- |
| CI | [36378489170](https://github.com/marshmallowday/leanrebel/actions/runs/36378489170) / 108789098943 | build failed |
| ReBeL checks | [36378489177](https://github.com/marshmallowday/leanrebel/actions/runs/36378489177) / 108789098854 | build failed |
| M06 targeted | [36378489157](https://github.com/marshmallowday/leanrebel/actions/runs/36378489157) / 108789099027 | build failed |
| Source inventory | [36378489171](https://github.com/marshmallowday/leanrebel/actions/runs/36378489171) / 108789098888 | success |

All runs have the exact source SHA above. Complete decoded job logs have the
same single compiler diagnostic. Earlier condition? inference, posterior index
and reserved-prefix parser errors are absent. The explicit trace-induction
helper itself produces no diagnostic.

Checks passed LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0,
RATIONAL_RUNTIME_PASS and 200 Python tests in 9.171s.
Inventory passed 200 tests in 8.465s. Downstream consumer/example builds and
complete normal/slow lint/transitive axiom acceptance remain unverified.

Artifact metadata was inspected, without claiming ZIP extraction:
target 10952092341, sha256 e18c8b89ae81b0637db94770a30551b4ecbf57bb01da923fec64fa280642d5b4;
global 10951609515, sha256 f97013cb341f605da017f220f45abc81c92e38f57cfc29f8490f3418760324dd;
source 10952111595, sha256 08cfe3c256e8972b9bb9ff32a17ebb98fe62e740ec6a3e17f1c7f3ab75eca091.
The source snapshot job 108789098998 succeeded; CI/inventory expose no artifacts.

## Diagnosis and repair

The simplifier did not infer the original model parameter in the private
public-trace equality through fullInformation/fullSignals. The goal still
contained refined traces instead of original traces:

```text
error: GameTheory/Analysis/ReBeL/CFRDStoredChild.lean:99:4: Type mismatch: After simplification, term
  Eq.trans same (Eq.symm member.left)
 has type
  publicTrace.{0, us, ua, uk, uq, max (max ua uk) uq} (fullSignals M.toInfoSignals) history.trace =
    publicTrace (fullSignals M.toInfoSignals) first.trace
but is expected to have type
  publicTrace.{0, us, ua, uk, uq, up} M.toInfoSignals history.trace = publicTrace M.toInfoSignals first.trace
```

Replace this one simpa with explicit instances of
storedChild_publicTrace_full M history.trace and
storedChild_publicTrace_full M first.trace. Compose the inverse of the first
with the known refined-trace equality and then the second. This supplies all
model/history arguments, so no higher-order simplifier matching is required.

The helper proof, public statements, model definitions and semantic hypotheses
are unchanged. Workflow, audit rules, tests, 172 targets and 134/276 audit
modules remain unchanged. The repair and evidence are one commit.
No local Lean/Python execution or completed M06 claim is made.

The repaired source requires its own three Lean workflows plus inventory.
The previous full acceptance at 8bf7814 cannot be reused as its validation.
