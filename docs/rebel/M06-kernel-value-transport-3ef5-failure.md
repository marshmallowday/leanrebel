# 3ef5 compiler failure and lexical repair

Source3ef56a217e22903aba945f1c3417e4810d468e73 failed TARGET run36292013486,
job108543785041. The completed artifact10922611596 was downloaded and inspected.
ZIP SHA-256: ce03828d5993b839c8f2b716452bd0e7a841dfceb1862b28d01c6cb502eb66b1.
Log23712 bytes, SHA-256:
c81d2fb6267edcd993c0b6414b51cdf2343c377771b99b28aa0934d00f6f6754.

The first diagnostic is PBSKernelValueTransport.lean:51:56, unexpected token
'recall'; it is parsed as a command keyword rather than a binder. The same
binder occurs at79:56 and99:56, producing cascading unknown fallback/command
errors. The repair renames that binder and its uses to hrecall, and changes
nothing in the hypotheses, conclusions, imports, controls, numerical constants
or gates. Old core blob: c968c342409328e91e572a02b813ba4c671f5c67.
Repaired core blob: c7508cf0204cc2c81ac967a622534c198a1c57c2.

No successful target compilation, normal/slow lint or axiom audit is claimed
for3ef5. Its earlier in-progress snapshot observation is retained in the
3ef5-validation note. The actual failed log supersedes that observation.
The repair descends from latest dac8bd9 checkpoint, retaining the independent
51d5 global acceptance. Exact repaired-source CI remains required.
