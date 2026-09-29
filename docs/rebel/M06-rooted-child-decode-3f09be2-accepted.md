# Rooted-child decoding accepted at 3f09be2

Exact source: 3f09be2d2b6bbb5e222e6b189f5bc409362ad148.
Branch: rebel/m06-kernel-value-repair-20260927.
This accepts the fee60dd/3246e17/3f09be2 batch and repairs only, not M06 or
SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3.

| Workflow | Run | Job | Conclusion |
| --- | --- | --- | --- |
| CI | [36524194641](https://github.com/marshmallowday/leanrebel/actions/runs/36524194641) | 109263472969 | success |
| ReBeL checks | [36524194648](https://github.com/marshmallowday/leanrebel/actions/runs/36524194648) | 109263472992 | success |
| Targeted | [36524194642](https://github.com/marshmallowday/leanrebel/actions/runs/36524194642) | 109263472785 | success |
| Inventory | [36524194628](https://github.com/marshmallowday/leanrebel/actions/runs/36524194628) | 109263472915 | success |

Source job109263473515 also succeeded. Every run's head_sha matched.
Complete decoded logs were read and parsed. All 2489 targeted and 5623 global
axiom records are unique and contain only propext, Classical.choice, Quot.sound
(or no axioms). Final audit markers match those counts.

All 161 targeted and 301 global lint modules passed, with final validation
markers. Their exact sets matched MODULES in audit_exact_leaf.py and
proof_modules() over the Git tree; no required modules were omitted. Both
normal and slow lint are requested by the unchanged auditors.
CI full build4328/lintbuild4098 and all three architecture VERIFIED markers
passed. Static LIBRARY_LINES_OVER_100 and TRANSPORT_ANALYSIS_SOURCE were zero.
RATIONAL_RUNTIME_PASS and 245 Python tests (checks9.410s/inventory6.268s) passed.
There were 199 declared build targets.

Artifact metadata was inspected; ZIP contents were not:
- CI11014388113,6219bytes,
  sha256 4ab3b052d4366322b33fb7dee98457e84b9c7b1df1d7b76c569468424a90d97a.
- Global11015850273,141277bytes,
  sha256 0b6e15c4fc9e75ddeff4250187e8594e9ca3e21e45fca53f96de142d939dea06.
- Target11014682812,58268bytes,
  sha256 ae8168255884a87ce9b9a817732300701b6da5b139ba4cbf224428ef4bc219d9.
- Source11014051608,3064631bytes,
  sha256 78b9a7f68c7e59e5eea90f4b6e2a129a45332aae18f0fed18588e50cda6e85b1.
- Inventory has no artifact.

Semantic review: the existing rooted noninitial child joint law is pushed
forward, not reset to outer roots. Complete continuation/deviation laws preserve
the child fuel; outer AOH reconstruction depth is separate. Internal recursive
Nash/private laws derive from the actual solver. The parent table and splice
retain positiveMassFloor*loss. Independent original-game solves compare scalar
values only at equal remaining horizon, with both errors; no policy/kernel/
vector/algorithm equality follows. The five real hidden-type consumers and
independent finite controls cover root retention, private draw, actual splice
and zero continuation. Unknown factual calibration and the native whole-chain
small-rate bound remain open. Prediction, finite-T and child loss stay separate.

This closes the dependent Trace endpoint, selected definitional equality and
one-sided horizon rewrite repair loop. It does not validate any later SHA.
