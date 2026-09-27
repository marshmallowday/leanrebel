# Exact changed-kernel source checkpoint, no Lean acceptance yet

Implementation: 3ef56a217e22903aba945f1c3417e4810d468e73 on
rebel/m06-kernel-value-transport-20260927. Its parent372 preserves the original
latest0285 checkpoint and the independent exact51d5 target evidence.

The complete source artifact10922865720 was obtained via the GitHub connector.
Its source-commit.txt identifies3ef5 and its recorded tar checksum agrees with
the bytes. The snapshot was extracted without any local git command.
ZIP SHA-256: adeb3798943899f9907c58710d0cc87095d3e64cfcc78fea45269adafa7d9a7c.
Tar SHA-256: bd16032e4ac5b9d57999863dd1793b5f3ba88ad6f3f74a408511921a6043aeaf.
All seven submitted source/consumer/fixture blobs match the prepared files
byte-for-byte. No inherited import, target or auditor module was removed.

All149 Python tests pass on this exact unmodified source with warnings as errors,
including8 new fixtures and4050 exhaustive cases. Test-log SHA-256:
52ccab9a1d54089bd85923c0b2fd99230392b6b55a93bcaf48f1f8919bfb1ddd.
Ledger/inventory structural checks also pass. These are arithmetic/static
checks, not Lean compilation, complete semantic verification or paper acceptance.

TARGET run36292013486 / job108543785041 was in declared-target compilation.
GLOBAL run36292013600 / job108543785374 passed widths, the actual unchanged
static gate, ledger/inventory/fixtures and rational runtime, and was in its
compiler/lint/axiom step. Snapshot job108543785470 completed successfully.
FULL CI36292013455 has not yet been separately accepted. All observations are
source-specific; final artifacts must be read before claiming success.
The expected targeted/global module counts are116/259. Next inspect the full
target log, repair actual compiler/linter issues without weakening statements
or gates, then verify every complete transitive-axiom record and named control.

Inherited51d5 global acceptance is separately recorded in
M06-depth-native-gap-global-accepted.md. It is NOT evidence for3ef5.
All limitations in M06-kernel-value-transport.md remain in force. M06 is incomplete.
