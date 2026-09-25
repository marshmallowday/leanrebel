# M06 joint-query architecture repair checkpoint

Initial implementation: `ada439cebe48ad3c522afd95c61c2efe32412bde` on
`rebel/m06-joint-query-20260925`. Repair branch:
`rebel/m06-joint-query-repair-20260925`. Preserve the initial source and its
independent target/full-CI runs for exact attribution; no history is rewritten.

## Observed failure and minimal repair

Initial ReBeL run `36148111604`, job `108114530207`, failed the static Phase 2
architecture step before Lean installation. Its line-width step passed.
The actual architecture artifact `10869982853` has ZIP SHA-256
`8cd2b867189d3bb65faa0d1dc893cae9be967ad0258e8506f7ccfe6f5fdbf42c`.
It reports TRANSPORT_ANALYSIS_SOURCE=2, whereas the unchanged gate expects 0.

The initial main proof introduced a local hypothesis named `change` and used
that hypothesis once. The unchanged lexical source-transport pattern counts
both standalone occurrences, including identifier occurrences. The repair
renames that hypothesis and its use to `jointDensity`. No theorem statement,
proof step, module, expected count or architecture policy is removed or weakened.
The two occurrences were not invocations of the transport tactic.

Initial target run `36148111692`, job `108114248701`, and full CI
`36148111593`, job `108114532199`, were still compiling when this repair was
prepared. Their eventual results must be attributed to ada439c, not to this
renamed source. No new-source compiler or axiom success is asserted here.

## Added finite-law regression diagnostics

scripts/rebel/tests/test_joint_native_query.py adds four Python tests. They
check the sharp correlated diagonal factor-two case and equal marginals,
19,200 exact rational nonnegative-loss cases over seed-dependent kernels,
rejection of unsupported actual mass, and the four native/joint modules'
compiler/umbrella/targeted-auditor wiring. All four were executed successfully
locally before this checkpoint. The earlier 83-test suite also passed locally.
These are executable finite-law and wiring diagnostics, not a Lean proof or a
claim that a diagnostic loss table is an actual CFR iterate-gap table.

The exact initial source snapshot `10869349614` was downloaded through the
GitHub plugin. Its embedded commit is ada439cebe48ad3c522afd95c61c2efe32412bde;
ZIP SHA-256 is `26075561d036b2eb8cf158c4a6573836e002818c6a64dad25227f186229a162c`
and tar SHA-256 is
`594fd1ac545f3abc9c58096e5ebc118abf9fa6c6d3e002f5bcacef95aeff4ec9`.
The exported proof wiring, original examples and auditor match the locally
inspected source. Static enumeration finds 249 global modules, 104 targeted
auditor modules and 580 public Lean files with no over-100 UTF-16-unit line.
Enumeration is not successful compilation or transitive-axiom validation.

## Resume requirement

Read the repair branch's current head and its M06 targeted, ReBeL and full-CI
runs. Inspect actual compiler/lint/axiom logs, fix any diagnostics without
weakening gates, and retain exact source/run IDs in a further checkpoint.
The complete M06 and Theorem 3 obligations remain pending as described in
M06-joint-query.md. The verified e651 native predecessor is not re-proved.
