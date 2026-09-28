# Fixed-trace average-limit acceptance at ba26c02

Commit: ba26c0250ee255aeeee1b80365b5f0693c9eeb5f. Branch:
rebel/m06-kernel-value-repair-20260927. Reviewed through the GitHub plugin.
All listed runs report exactly this head SHA and completed/success.

| Workflow | Run | Job |
| --- | --- | --- |
| CI | [36365999282](https://github.com/marshmallowday/leanrebel/actions/runs/36365999282) | 108752407529 |
| ReBeL checks | [36365999338](https://github.com/marshmallowday/leanrebel/actions/runs/36365999338) | 108752407844 |
| M06 targeted | [36365999348](https://github.com/marshmallowday/leanrebel/actions/runs/36365999348) | 108752407579 |
| Source inventory | [36365999284](https://github.com/marshmallowday/leanrebel/actions/runs/36365999284) | 108752407410 |

Complete decoded job logs, not excerpts or old-SHA results, were inspected.
All 2130 targeted and 5271 global unique transitive axiom records were parsed,
including multiline records. Record-start counts equal parsed counts.
Only propext, Classical.choice and Quot.sound occur; empty lists also pass.
All 128 targeted and 270 global module normal/slow lint passes were checked.
Full umbrella build, repository lint, architecture and rational runtime passed.
Both static indicators LIBRARY_LINES_OVER_100 and TRANSPORT_ANALYSIS_SOURCE
are zero. ReBeL checks ran 190 Python tests in 9.135 seconds; inventory ran
190 in 10.049 seconds, both OK. The manifest contains 166 build targets.

Artifact metadata: CI10947901146, global10948646587, targeted10947802446,
source10947303234 (snapshot job108752407640); no inventory artifacts.
This records metadata, not a claim to have downloaded archive contents.
Complete axiom evidence comes from decoded job logs.

Exact accepted source blobs:
- CFRDAverageLimit.lean: ed4c5ffe2502c9e10d80552c4f30e184702031a3
- PBSAverageLimit.lean: c48eb855b3a3c44a8bcfee213cf472ed4973e304
- Examples/CFRDAverageLimit.lean: e652ad88cebafd6a8631da7597c427e575821231

The three addition-orientation repairs pass. See M06-average-accepted.md for
source scope, and M06-average-limit-batch.md for mathematical details.
Acceptance is specific to ba26c02 and its unchanged blobs. New replay code
requires new-SHA Actions. M06 as a whole remains incomplete.
