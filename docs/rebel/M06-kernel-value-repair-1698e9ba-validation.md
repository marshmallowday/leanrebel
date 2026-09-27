# Exact-source 1698e9ba feedback and remaining observable-bound repair

Source: 1698e9ba212f4082cd7d601c13f3d0350e170bdf on
rebel/m06-kernel-value-repair-20260927. TARGET 36293359962 / job 108547527220
failed; its full artifact 10923455928 was downloaded through the GitHub plugin.
ZIP SHA-256: 89bce85225b385d2ffaac1e07d252d1cebedb7f7bc42f8194eb32b5675e338b6.
The 22,519-byte m06-targeted.log identifies that exact SHA and Lean 4.33.1;
SHA-256: f7df110991b22a98df36c6949c6a98f02e0ab6f509a1a980dc728b9981729e42.

The generic kernel-value module and actual depth-parent integration both built.
Only the example's observable-bound proof failed: splitting history.state first
left the outer match unreduced, so the next split selected that match rather
than the inner Boolean conditional. The sharp-discrepancy proof now elaborated
without its earlier error. Lint and transitive axiom validation were skipped.

The next repair directly splits the observable's outer match, then its inner
conditional. All control statements and definitions are unchanged. Core and
integration remain at their successfully compiled 1698e9ba blobs. No architecture
counter, theorem assumption, target, audit, import, toolchain or workflow changes.
The exact new source still requires its own compiler/lint/axiom acceptance.

## Exact-source checks

GLOBAL 36293359964 / snapshot job 108547527291 supplied source artifact
10922962048. The plugin-downloaded archive identifies the source above.
ZIP SHA-256: db0b7342fcbdb8f8dd8bd4c3ee69943a2a5829e63cd807b164903976c5dab446.
Verified enclosed TAR SHA-256:
959b1d6e1ea353d78b800060c1df0594af122cafaf49faee0b567b889d258b7b.
All seven source/consumer blob pins match the owner ledger. Comparing exact
6b7865 and 1698e9ba snapshots finds only the three intended Lean files changed
outside docs; all eleven theorem headers are identical. All three modules remain
in the public umbrella, 154-entry build manifest, 116-target and 259-global audits.

On exact 1698e9ba source, coverage and inventory structure checks and all 149
Python tests passed, including the eight changed-kernel fixtures and 4,050
exhaustive Fraction cases. Commands: python scripts/rebel/check_coverage.py;
python scripts/rebel/check_inventory.py; python -W error -m unittest discover
-s scripts/rebel/tests -v. Log SHA-256 values, respectively:
757e4bed6b6ef8dc9fd69d61b96bef8af8b62992e0c057676f74eef8f590ad82;
582841a04146972ffca4a9bcc2f325a2132b16efa727b508f20fe0c355f1f509;
38d53246c5441feb39a5f03bd34392e8bcbe3e976f0828f83201f294c15aa754.
These local checks used no git or direct GitHub access and are not Lean validation.

INVENTORY 36293359957 succeeded. GLOBAL job 108547527375 passed the unchanged
static architecture gate, source/toolchain identification, ledger/fixtures and
rational-runtime checks; its compiler/lint/axiom step was still in progress at
last inspection. FULL CI 36293359963 / job 108547649612 had no inspected final
result. Neither is accepted here, and a new source push may supersede them.
M06 and the parent SEARCH/SAFE obligations remain incomplete.
