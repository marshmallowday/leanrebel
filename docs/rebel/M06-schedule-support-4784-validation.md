# Exact 4784 source: reproducibility and pending Lean review

Implementation: `4784d83b41c644c043557ac1080fa2df1991be18` on
`rebel/m06-schedule-support-review-20260927`. The evidence checkpoint is kept on
`rebel/m06-schedule-support-checkpoint-20260927` so recording results does not
cancel the implementation branch's target or global checks. No Lean source is
changed by this evidence checkpoint.

## Actual exact-source checks completed

Source snapshot run 36284548923 / job 108522699098 succeeded. Artifact
10920061478 was obtained through the GitHub connector, unpacked without git
operations, and its source-commit.txt and archive hash independently checked.

- ZIP SHA-256: `f5069b02ed5f2f6af5f04ec86aa623b2632c669292c21eec2ae8ba3e5a29ebbb`.
- Tracked-source TAR SHA-256:
  `95f705149e37535a01c04df0c2d52d352bf183c20b9b0ee845c2e4fa764ece43`.
- Core blob: `ff5bf151d7e8bb146c02a5eeb1749972a77e42a9`, matching the committed
  and locally reviewed module byte for byte.
- On this EXACT unmodified extracted source, check_coverage.py and
  check_inventory.py succeeded, and Python -W error unittest discovery passed
  all 127 tests. These were run in the exact 4784 directory, not just on the
  earlier 3dfa-plus-edits work area.
- All five advertised core declarations and four control names are present;
  the opt-in root, M06 target list, exact audit consumer (111 modules), and
  dynamic global consumer (254 modules) all include the new module.
- The seven new Fraction fixtures retain SHA-256
  `8757a730be9e4dc0c27d6bfc5cf300d8306ec0cd77ef6462df53142ceed3cfeb`.

These are structural/arithmetic checks, not Lean compiler or kernel evidence.
The fixtures independently enumerate paths and forward charges, including
2,187 inhomogeneous three-stage combinations. Their exact-next-defect charge
witness tests composition algebra, not a separate implementation of the
primitive native resolver support theorem. Earlier native resolver controls
remain enabled and unchanged.

## Independent remote checks and exact next checks

TARGET run 36284548964 / job 108522796260 was in the declared-target compiler
step when reviewed. Normal/slow lint and the complete transitive-axiom audit
were pending. Inspect its final m06-targeted artifact and every complete record
(including multiline dependency lists), all 111 module lint passes, all named
new declarations/controls, and final pass markers before accepting this slice.

GLOBAL run 36284548923 / job 108522699001 separately passed the real unchanged
static architecture gate, line widths, ledger/fixture checks and rational
runtime steps; it was in the compiler/lint/axiom step when reviewed. This
metadata confirms the earlier static defect was repaired but is NOT a complete
global pass or an inspection of the eventual global archive.

Full CI run 36284548898 / job 108522802089 was in progress independently.
Do not replace any of these exact-source checks with 3dfa or b833 results.
The earlier compiler/architecture failures remain in the two validation-history
notes and the owning coverage JSON. All new-source Lean acceptance remains
pending at this checkpoint. The committed semantic review explains actual
prefix laws, private pairing, the fixed unknown opponent, last-output boundary,
and why the charge and sampling comparison do not establish unilateral safety.

M06 is incomplete. Small primitive leakage, changed-PBS native/late signed
value rates and constructed CarriedResolveStepBounds remain open. The four
original paper obligations remain pending. No background monitoring is implied.
