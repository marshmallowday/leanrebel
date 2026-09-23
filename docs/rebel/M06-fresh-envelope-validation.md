# M06 fresh-child source validation

## Immutable source and inspected Actions evidence

Source commit: dd66907138cf052a52435d8c31dcb3ecaea5703e.
Parent checkpoint: b037b0c700b4eb549c4f8a7e78281a82fc1f238f.
Source tree: accef783049fd404d56671175d47e52542693610.
Branch: rebel/m06-recursive-envelope-20260923.
The following documentation checkpoint changes no Lean, target, audit or pin.

M06 targeted proof feedback SUCCESS:
https://github.com/marshmallowday/leanrebel/actions/runs/35828662651/job/107075968088

The GitHub plugin downloaded artifact 10735963541:
`m06-targeted-dd66907138cf052a52435d8c31dcb3ecaea5703e`.
Archive SHA256:
`0a2f6aaf1394abc96704d117bd2067260bd645fa888d222822b43039cf64e667`.
Decoded UTF-8 log SHA256:
`65c8e0a8ea930509d9b3722b19fcc0e228f3162d66b1cca1a433f42c0f6d0989`.
The log starts with the exact source SHA and Lean 4.33.1 compiler identity.
Its full 370129-byte text was inspected programmatically: all 731 logged
transitive axiom sets are subsets of {propext, Classical.choice, Quot.sound}.
The 61-module normal/slow Batteries lint audit succeeds, including each of the
three new modules. M06-fresh-envelope-compiler.txt is an explicitly labelled
summary excerpt, not a substitute for or a claim to reproduce the full log.

Executed workflow commands include:

    lake build $(cat scripts/rebel/m06-targets.txt)
    python3 scripts/rebel/audit_exact_leaf.py

The unchanged auditor builds every named module, generates its all-declaration
Lean.collectAxioms checker under .lake, and runs Batteries with --no-build
--trace for each module. No source declaration, private helper, linter or allowed
axiom policy was excluded to make this pass.

## Exact new modules

| Module (under GameTheory.Analysis.ReBeL) | Blob | Declarations |
| --- | --- | --- |
| CFRDFreshValueDrift | ed1c73c613f124811b27714e80e936b8e2e4c207 | 14 |
| CFRDFreshResolve | a85105f512b48d68fd2c380f802373b123ca3a18 | 9 |
| Examples.CFRDFreshResolve | e9adc68f96218bf103f953c0014e223d617b4feb | 20 |

The counts include generated proof helpers, not just named theorems.
Source-line counts are 218, 202 and 163. The original analytic root, target
list and supplemental auditor only gain these three modules. No existing Lean
source is changed except the three added analytic-root import lines.

## Additional feedback, not substituted for Actions

Previously downloaded offline artifacts contained the pinned Lean 4.33.1
compiler and matching dependency manifest. Their four part hashes and combined
archive hash were checked before extraction. Changed project dependencies were
rebuilt directly from the e630 snapshot, with no Git invocation or dependency
network fetch. New source bytes were checked against the three blob identifiers.
The direct compiler, 43-declaration axiom audit, and single-importer normal/slow
Batteries lint passed. An earlier combined interpreter lint process was killed
with exit -9 and is NOT counted as a pass; the independent Actions per-module
lint is the definitive 61-module validation above.

## Integration gate status at recording

Source inventory 35828662685/job 107075968266 succeeded. ReBeL checks
35828662704/job 107075968786 passed widths, static architecture, ledger,
adversarial tests and rational runtime; repository-wide compiler/lint/axiom
processing was still running at the last check. Full CI 35828662759/job
107075968744 was also still running. A later documentation push can supersede
these in-progress runs. Check the current HEAD before claiming integration.
Main is unchanged; no full milestone acceptance or upstream mutation occurred.

## Semantic review and remaining scope

The exact declarations, eight theorem controls, and source coverage map are
in M06-fresh-envelope.md. Local optimality and reference-law preservation are
derived from the concrete information-set child solver and its completion.
The new model value drift is a computed finite maximum, not supplied safety.
The theorem retains this drift in addition to prediction, finite-T and old/new
child errors. It is one fresh public-cut solve with a finite-plan realization
of a newly computed average, not the source's later carried-PBS recursion or
actual child-iterate sampling. A source-dependent drift-rate and the full
recursive connection remain open proof obligations; source rows stay pending.
