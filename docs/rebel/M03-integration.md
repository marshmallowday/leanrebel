# M03 integration: canonical reach belongs below Analysis

This records an integration repair, not an advance declaration of acceptance.
The inspected implementation checkpoint is
`5576151cfc97945a9a958c8a5eee54d4d5599343`.

## Evidence and failed boundary

ReBeL run `35273484942`, job `105378294574`, passed compilation, all 31
normal/slow module lints, and transitive axiom checking of 1282 declarations.
Only propext, Classical.choice, and Quot.sound were admitted. The full CI run
`35273484821`, job `105378421803`, passed the full build and Phase 1, but
failed Phase 2; later gates were skipped. It is not an all-gates-passing SHA.

Source inspection identifies the authored reverse import in
`GameTheory/ReBeL/ReachFactorization.lean` of
`GameTheory.Analysis.Protocol.CounterfactualReach`. The unchanged Phase 2
rule requires `ANALYSIS_IMPORTED_OUTSIDE_ROOT = 0`; that import violates it.
A conversational explanation involving empty Markdown headings was incorrect:
the checked M03 document has bodies, and Phase 2 does not implement that test.
The correction is a dependency-layer repair, not a document or threshold fix.

## Focused extraction without a second reach semantics

The original reach module has only one authored import,
`GameTheory.Protocol.BehavioralAssessment`. Its definitions and proofs concern
canonical histories, legal local choices, finite behavioral execution, and
own/opponent/chance reach factors. It contains no equilibrium, optimization,
regret, topology, or solver definition. Its lowest sufficient layer is Protocol,
consistent with the adopted D0 stratification.

The complete source blob
`c142130058deb2d2f43229f7fa5505db72289863` is moved UNCHANGED to
`GameTheory/Protocol/BehavioralReach.lean`. Every definition and proof remains
single and retains its public qualified name. The Analysis entry point now
imports this module and defines no aliases or duplicate implementation.
ReBeL imports the same canonical facts directly from Protocol. Neither
`GameTheory.lean` nor `GameTheory/Protocol.lean` gains an import, so the basic
public root is not broadened. Counterfactual regret and solver analysis remain
in Analysis. No frozen source inventory or dependency pin is changed.

## Verification discipline

No audit regex, expected count, allowlist or deep reachability probe is changed.
The source move adds no transport token. The foundation and Analysis entry
point are explicitly added to the ReBeL compilation, full/slow lint and
transitive axiom selection, so moving a declaration does not hide it from
verification. The explicit surface now has 33 modules; its actual declaration
count must be read from the new Actions log, not predicted from the old count.

The existing static Phase 2 check also runs early in the ReBeL workflow, before
expensive compilation. Full CI still runs the unchanged complete build,
compiler-resolved reuse signatures, all three architecture gates including
all deep probes, and full-library lint. Its audit and lint output is now also
saved as an artifact for exact inspection after interruptions. Failures remain
fatal; all action SHAs, read-only permissions and timeouts are retained.

The final accepted implementation SHA and gate evidence will be recorded only
after those actual jobs pass. The earlier compiler/lint success alone does not
close this integration obligation.

## Renewed candidate-source review

At `a31cca8fbaf8b11e618b2117005766c957a518c0`, ReBeL run `35276195454`,
job `105387307916`, the static Phase 2 audit passed with
`ANALYSIS_IMPORTED_OUTSIDE_ROOT=0` and `VERIFIED=1`. The inventory guard then
correctly rejected the changed candidate module hash before compiling Lean.
That failed run is not accepted as implementation evidence.

The reuse inventory now retains the complete previous candidate row in
`previous_review`. Its current Analysis entry point and the unchanged
Protocol definition each have a full SHA-256 and exact source span. The
checker still rejects any wrapper drift and additionally rejects drift in
the defining source or its reviewed span, or a reexport pointing to a
different module even when the wrapper is rehashed. All 23 candidate
qualified names and their stated premises are unchanged. The original
paper/official ledgers and source identities are untouched. Three hostile
fixtures exercise the added checks; the actual `#check` probes still run in
Actions. This is a renewed premise/location review, not removal of the
candidate-hash guard or a new assumed theorem.
