# Randomized resolver support validation history

## Candidate checkpoints

- 9894e45bbc0505debd44957a4a7446302d2b7902: seven new definitions/theorems
  and explicit scope documents. Target run 36280503612, job 108511290081,
  was still compiling before the controls successor advanced the same branch.
  No target pass is asserted for that candidate.
- 63aa262540b7dc633ea511c6cc727aaa49bde585: four additional Lean controls
  and eight exact Fraction tests, with all previous tests retained.
  Target run 36280700975 / job 108512019610 was still compiling at inspection.
  Inventory run 36280700991 / job 108511831808 completed successfully.
  Full CI run 36280700955 / job 108511890830 was still in progress.
  Global ReBeL run 36280700956 / job 108511831794 failed before Lean setup:
  the unchanged architecture gate observed TRANSPORT_ANALYSIS_SOURCE=2,
  expected 0. The two authored `change` steps were in the new generic proof.
  Its line-width precheck had LIBRARY_LINES_OVER_100=0.

The repair normalizes the stopped-state predicate directly and uses the
existing definitional equality of the memory event without a transport step.
No theorem statement, hypothesis, goal, support event or probability law changes.
No transport budget, lint rule, audit script, action pin or expected count is
edited. The successor still needs its own compiler/lint/axiom output; replacing
a proof script does not itself establish a pass.

## Exact local source review through plugin artifacts

63aa source run 36280700956 / snapshot job 108511831703 succeeded.
Source artifact 10919085356 was downloaded through the GitHub plugin; its
SHA-256 matches `0f743519de1595f52fed5be8a9feadd6e8a712f13a1a993961b29a24a59c2cda`.
The source-commit marker identifies exactly 63aa. The original support module
was preserved byte-for-byte except replacing its import of CFRDResolveBelief
with the stronger CFRDRecursivePlay dependency and appending new declarations.
All original example lines were retained. Original coverage.json, target and
axiom lists, umbrella, architecture and workflow gates, Lean toolchain and
lake-manifest were compared byte-for-byte with the b833 snapshot and unchanged.

The local exact-snapshot command
`python -W error -m unittest discover -s scripts/rebel/tests -v`
passed all 120 tests. These are Python fixture results, not Lean compilation.
The new eight-test file matches the separately tested local copy byte-for-byte;
its SHA-256 is `3368db020d85fa3802e6c19f81f46b9b35980f8f03af3ca6b2610b3373218260`.
The two edited Lean modules had maximum line widths 100 and 97 respectively.
The local environment has no Lean/Lake; kernel validation is via unchanged CI.
No local git operation or direct GitHub HTTP request was used.

## Baseline check completed, new evidence still required

The inherited b833 global run has now succeeded and all 4,939 transitive axiom
records plus all 253 module lint passes were actually inspected. See
M06-support-rates-b833-global-validation.md for artifact/log hashes and scope.
That pass is strictly baseline evidence, not evidence for the repaired new code.

Keep M06 and SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR, SAFE-THEOREM3 open.
Resume from the latest resolver-support branch SHA and inspect the successor's
jobs/logs before rerunning completed stages or adding later implementation.
