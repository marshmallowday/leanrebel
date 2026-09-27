# 2f6e certain-event control: exact compiler failure and repair

Source 2f6e8c44f507324e0900a2ac1ee6b4341fbeaa19 on
rebel/m06-depth-native-gap-20260927 compiled the complete core module
PBSDepthNativeGap, including its repaired native tag-law proof. The target
still failed the example module at Examples/PBSDepthNativeGap.lean:99:2.
The final target run 36289474910 / job 108536659316 is a failure, not acceptance.
Normal/slow lint and transitive-axiom validation did not run.

Artifact 10921592602 was actually downloaded and the complete log inspected.
ZIP SHA-256: 65d49176cf62250e3da3b779f36b4989476fbf1ca56d7b24e39e4bc688044796.
Log SHA-256: caa85061fe8cf90100ab47fa8a3f1e2f3486ec9539b4e546ec1f257a32d9cb16.
It starts with the exact source SHA and pinned Lean 4.33.1.
The certain-event control had proved unitMass about the local let-bound
execution, while the applied generic theorem exposed the expanded execution
expression. Its restricted simp did not rewrite the denominator to one.

The focused repair unfolds ONLY this local abbreviation in unitMass before
rewriting. The theorem statement, all four controls, all nine core declarations,
all consumers, noise/child/finite-time budgets and actual event semantics remain
unchanged. No library transport, hidden premise or warning suppression is added.
Old example blob: 3cfd217c981817ca416daaccc6bb98db86a67c80.
New example blob: 97477d7f65c122f80c8f14653b74513d85fc766a.
The unchanged core blob is 29a19748709fdc1269728ee423656f48433b5e00.
The repaired source requires its own successful compiler and complete audits.

The exact unmodified 2f6e source archive 10921823300 was downloaded and checked.
ZIP SHA-256: a93814744499af5b5424ffd100902571a723ac337335da19f95dffa87be6405d.
Tar SHA-256: 1bed8ce3d072c7bd3e61ccd44b246baf9550b310ba6c7b046f9442739c1f6a1a.
All 141 Python fixtures plus ledger/inventory checks passed on that extraction.
Test log SHA-256: 4d53ab007e3ceebf241464acd1d94bea6d93d8529ec39c69c42c667a2f909a99.
Source and consumer byte identities were checked; 113 explicit target modules
and 256 global modules retain both new modules and all original consumers.
Arithmetic and structural checks are not Lean acceptance.

2f6e GLOBAL 36289474899 / job 108536845843 passed static architecture, width,
fixtures and runtime, but was still in compiler/lint/axioms when checked.
Snapshot job 108536845785 succeeded. Full CI 36289474886 / job 108536768333
was in its Lean action step. No final acceptance is asserted for either run.
All d15f failure history and completed inherited 35d0 audits remain preserved.
