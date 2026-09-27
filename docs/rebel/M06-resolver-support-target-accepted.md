# Native resolver support: exact 3dfa target accepted

Source: `3dfa8c78375218bae5a323803f889b06342aecc2` on
`rebel/m06-resolver-support-20260927`. Review starts from latest checkpoint
`f3cda937012b9c72e7e03b8aa6b7e9d9176f0093`; main is not the M06 head.
This evidence commit preserves that checkpoint and changes no Lean source.

## Completed target evidence

Run 36281726973, job 108514712577 completed successfully. Both the declared
M06 compilation step and the subsequent normal/slow lint and transitive-axiom
validation step succeeded. Artifact 10919486265 was downloaded through the
GitHub connector and its COMPLETE `m06-targeted.log` was inspected, rather
than relying on job status, a compiler-step result or a truncated log excerpt.

- Artifact name: `m06-targeted-3dfa8c78375218bae5a323803f889b06342aecc2`.
- ZIP SHA-256: `7beecfe797d01b7756c19f90acc75803cc7ec528888352bbd043384c42370044`.
- Log SHA-256: `abd98e6528d0c7f48d7aab0a9f62d106402911a5a8d36a7f5fb3575c4775b012`.
- First log line is the exact source SHA. Lean is 4.33.1, compiler commit
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- All 1,797 axiom-record starts have COMPLETE closing-bracket records, including
  multiline lists. Declaration names are unique. Every set is contained in
  `{propext, Classical.choice, Quot.sound}`.
- There are 110 per-module axiom passes and the same 110 normal/slow lint
  passes. Their per-module declaration counts sum to 1,797. The final markers
  are `EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1797` and
  `EXACT_LEAF_VALIDATION_PASS modules=110`.
- All seven support declarations and all four named controls in
  M06-resolver-support-coverage.json occur in the complete allowlisted records.
  No error or warning lines were found.

Core blob `76df5514e9e878fde6e8ff4691c2ec341d88bf35` and example blob
`f440ce96ada7fb34f13caa0929a7d6d6cf06d309` are unchanged from the previously
recorded compiler checkpoint. The source snapshot was independently obtained
from run 36281726986, artifact 10918982673. Local extraction and log checks
perform no git operations and no direct GitHub access.

## Semantic review and limits

M06-resolver-support.md and M06-resolver-support-controls.md describe the
statements and hostile controls; their original pending observations remain
historical, superseded for TARGET validation by this exact-source evidence.
The actual randomized draw keeps each model paired with its resulting history.
The retained-state support event detects missing beliefs, arbitrary correlated
incoming laws remain allowed, and a supported point history incurs no charge
merely because its model probability differs. Primitive support dominance is
explicit and only conditional; arbitrary unknown opponents need not satisfy it.

The source's GLOBAL run 36281726986 / job 108514756082 was still in its
compiler/lint/axiom step when checked in this review. Its earlier static,
fixture and runtime steps succeeded; its snapshot job succeeded. This target
pass is NOT a global or full-CI pass. Check those independently. The inherited
b833 global audit is already complete and must not be repeated.

Next: compose native support charges over a finite schedule, preserving actual
prefix weights and distinguishing first-hit probability from visit count.
Small primitive leakage and signed native/late value/security bounds remain
open. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending;
M06 is incomplete. No theorem is weakened and no learner-convergence premise
is used to bypass test-time safety.
