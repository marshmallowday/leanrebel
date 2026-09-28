# Nash transport accepted at e590b4f

Validated source: `e590b4f805a2ec90f84c66e75d66e586fc27fa91`.
Branch: `rebel/m06-kernel-value-repair-20260927`.
This closes the 481c5ab/67fbf8c/3e84fcb/e590b4f repair loop for this dependency.
It does not accept SEARCH-CFRD, SEARCH-ERROR or SAFE-THEOREM3.

| Workflow | Run | Complete job log |
| --- | --- | --- |
| CI | [36451061294](https://github.com/marshmallowday/leanrebel/actions/runs/36451061294) | 109025632565 |
| ReBeL checks | [36451061358](https://github.com/marshmallowday/leanrebel/actions/runs/36451061358) | 109025632233 |
| M06 targeted proof feedback | [36451061397](https://github.com/marshmallowday/leanrebel/actions/runs/36451061397) | 109025632613 |
| ReBeL source inventory | [36451061654](https://github.com/marshmallowday/leanrebel/actions/runs/36451061654) | 109025632840 |

All four run head SHAs equal the validated source, with completed/success status.
GitHub plugin reads returned complete decoded job logs. No local Lean/Python
execution or plugin-side compiler execution is claimed.

- Full build 4310 jobs and lint build 4080 jobs passed.
- Architecture audits reported all three VERIFIED checks.
- Static LIBRARY_LINES_OVER_100=0 and TRANSPORT_ANALYSIS_SOURCE=0.
- Rational runtime passed.
- Python: 215 tests, checks 9.309s and inventory 10.935s.
- All 143 targeted and 284 global module lint passes, including the configured
  normal/slow checks. Targeted and global audit completion markers passed.
- Parsed complete transitive axiom output: 2328 unique targeted declarations,
  5464 unique global declarations. Every reported axiom belongs to
  propext/Classical.choice/Quot.sound; no prohibited axiom was found.
- New transport, native budget, concrete consumers and umbrella compiled.

Artifact metadata was inspected; ZIP payloads were not read. Decoded logs,
not a claim about unread ZIPs, are the validation evidence:

| Artifact | ID | SHA256 digest |
| --- | --- | --- |
| CI audits | 10984124365 | 5871b7caf01e99cb7a96d39c3b2f20a054f30cd3d556f43e975520eb0499a0ff |
| global | 10985001992 | 00d4dfd8f89a363ca0760c6a069739e038d3b3ce692cfe18edf6e3498f20441f |
| targeted | 10984074614 | cdf3cbc2aa7df891132c5afdd13e93c0ed08338b0709aa2e0e7e7f79ab00dbfb |
| source snapshot | 10983821630 | 26cbe85e623d1578713fa93c800253de087f12e5c74b263f2a30132ac3ffb9a0 |

The separate inventory run has no artifacts. See workflow metadata for the
artifact names and lifecycle. Source blobs:
PBSRecursiveNashTransport ce72245aa8752b6967cb4ccecf46abc7d63202be;
PBSRecursiveNashBudget 6cb5cb3259efe196bb6896a251aaa383b1149e9d;
Examples/PBSRecursiveNashTransport 60a45cd2b0e9f5b45f5e7afa330f28e7416bbe55.

Semantic review: actual finite recursive solver tolerance controls replacement
only after charging root-law and both opposing-policy execution discrepancies.
The model-law/computed-opponent specialization removes these charges and permits
arbitrary old own policy. Full native stage-plus-late horizons are checked.
Actual unsupported-state mass remains charged. The stored selected MODEL
posterior is not identified with the fresh averaged opponent or the unknown
opponent's factual posterior. Neither a general small-rate bound for the
native chain nor rooted/original solver equivalence follows.

These accepted source results are not reused as compilation evidence for
the subsequent CFRDRecursiveSecurity integration.
