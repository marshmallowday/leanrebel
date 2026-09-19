# M05 validation checkpoints

## Validated repaired implementation

Source: `44cd2d674b5b94713407c450a8bfd0d6f6a0e191`.

- ReBeL run [35410325950](https://github.com/marshmallowday/leanrebel/actions/runs/35410325950),
  diagnostic job `105808567589`: all required steps **success**, tracked files clean.
- Full CI run [35410325967](https://github.com/marshmallowday/leanrebel/actions/runs/35410325967),
  job `105808562997`: build, compiler-resolved inventory, Phase 1/2/3 architecture
  checks, deep reachability probes, complete public-library lint and cleanliness
  **success**.
- Saved ReBeL log SHA-256:
  `013fce26d9aaa47454ceb1fde339ff9a966f45e3cd9007a0f8bf64017127797a`.
- Compiler emitted `REBEL_AXIOM_AUDIT_PASS declarations=2541` and
  `REBEL_VALIDATION_PASS modules=105`. Build and explicit normal/slow lint
  surfaces each contain the same 105 modules.
- The permitted transitive kernel axioms remain exactly `propext`,
  `Classical.choice`, `Quot.sound`. No `sorryAx` or new allowance was added.

The original failed `18d11b3` run stopped on the missing documentation string
for the local `valueHistoryFintype` instance. The correction does not change
its type, any proof, any theorem statement or any dependency.

`M05-compiler-log.txt` preserves selected complete lines of the successful
44cd2d6 log. It is explicitly an excerpt, not a replacement for the full log.
The read-only transport run
[35411825818](https://github.com/marshmallowday/leanrebel/actions/runs/35411825818)
read the already-saved artifact and exposed audit text in job metadata. Its
success is NOT compiler evidence; the original source run above is authoritative.
Some longer audit entries wrap across physical lines and are not included in
the selected excerpt unless their entire dependency list was read.

## Additional proof source and acceptance candidate

The additional radial-versus-normal counterexample is committed at
`b1b557b7e3c9471e5f774c7fc400c1665742a614`. Its ReBeL run is
[35411381522](https://github.com/marshmallowday/leanrebel/actions/runs/35411381522)
and full CI run is
[35411381563](https://github.com/marshmallowday/leanrebel/actions/runs/35411381563).
At this checkpoint their final result has not yet been accepted.

`coverage-updates/M05.json.candidate` proposes 43 source-row dispositions but
is deliberately NOT a live ledger input. The test suite validates its exact
M05 membership, unchanged source identity, preserved earlier evidence, source
blob pins and declaration names in an isolated temporary ledger. Those tests
are metadata checks, not a replacement for the pending exact-source Lean gate.
The candidate may be renamed to `M05.json` only after its source is accepted;
the test suite also requires the accepted-source record in this report.

M05 is not declared complete by this validation checkpoint. Existing M00-M04
acceptance remains intact; the live M05 records are still pending.
