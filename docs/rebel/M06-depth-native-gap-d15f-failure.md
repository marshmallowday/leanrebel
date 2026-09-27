# d15f compiler failure and focused repair

Exact failed source: d15f68b5ca4377f06a69aa5e71c76013770ed766.
Target run 36288920528 / job 108535044752 produced artifact 10921403474.
The complete m06-targeted.log was downloaded through the GitHub connector.
ZIP SHA-256: aae0d971a04f947810c7df841dc91a20438a7a2981edc9f67ea12e0e7ad409b5.
Log SHA-256: 2c2ec761f8aa92565a515a6e383cd06c99b8e3070eb72d6f4d071885b62d6958.
The exact SHA and pinned Lean 4.33.1 appear at the beginning of the log.

PBSDepthNativeGap.lean:215:92 left the nested conditional root-law bind to a
constant pure tag unsimplified. The unused bind_pure simp argument at 217:42
was also correctly rejected as an error. Other new declarations did not report
compiler errors, but the example module could not compile behind the failed core
and the target's normal/slow lint/transitive-axiom step never ran. Therefore
neither core nor examples are accepted from this failed target.

The repair adds the existing public FinDist.bind_const lemma to the tag-law
proof before bind_pure. The constant inner root-law bind is normalized before
the outer monadic identity. No statement, parameter, source semantics, control,
warning option, architecture budget, audit consumer or dependency is changed.
Failed core blob: 1fa95b074eb7ee9bbeac252cc6d9204e76fd2223.
Repaired core blob: 29a19748709fdc1269728ee423656f48433b5e00.
New exact-source compilation and complete lint/axiom review are required.

The exact d15f source snapshot was separately downloaded (artifact 10921517832).
ZIP SHA-256: 3ed3c6c04f82743f30296ed5f8e16cd5b588e6909e18a0f6aff87f4625774cbd.
Tar SHA-256: c9703e4b6338017f7fc311fd2fe59db1302fb77bb2e1c9fdcddca3967f62766c.
All source blobs and added consumer entries were checked, and all 141 Python
fixtures plus ledger/inventory checks passed on the unmodified extraction.
Python log SHA-256: 2e3d7589a71b80563d7158c2eee01929dbecbfcb1cb1d5213fab7672ecab8df7.
The committed core contains a corrected closing parenthesis relative to the
prepared local draft; this byte difference was explicitly inspected, not silently
reported as equality. The arithmetic tests are not Lean validation.
