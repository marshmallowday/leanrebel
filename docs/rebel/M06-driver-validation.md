# M06 constructed driver: validation, semantic review and restart evidence

This is a verified dependency slice, not acceptance of the whole M06 milestone.
The exact proof source is 0b6d3f3689b3d94a75f5da29d2c2a6879e65c130.
Restart from rebel/m06-driver-checkpoint-20260920 and read its remote HEAD.
The evidence change contains no Lean source or dependency change.

## Saved stages and inherited recovery

The remote source at entry was 067ca5fe9a6da94197ef87eb86326cb250c88d99,
not the much older 8ab23b4b named by an earlier chat. All subsequent changes
are descendants, without force updates, history rewriting or main integration.

| Commit | Actual stage |
|---|---|
| 6b7cd96915ee4a46c01581e78a40654227fe31ae | First attempted repair of a dependent reference-kernel rewrite; compiler rejected it. |
| 7166f79de7f14ade853d5d7f96a6e2adf7e07018 | Compare supported/unsupported kernel laws before rebuilding dependent beliefs. All inherited targets compiled. |
| c09549c9dc9d98cf933da0798d035701a72f5af3 | Add generic trunk restoration and the constructed exact continuation in the actual CFR-D recurrence. |
| 3ec0f0b4dc77ef1524bd4165bba22082ab772b22 | Add finite-T Nash/security and six controls; fix the reserved binder and audit counter types. Target, axiom audit and lint passed. |
| 0b6d3f3689b3d94a75f5da29d2c2a6879e65c130 | Add bounded numerical prediction error for its own recurrence and three additional controls. Target, axiom audit and lint passed. |

The source branch at each major stage is retained. The earlier STATUS is
preserved in M06-status-before-exact-driver.md. Main remains
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098, accepted through M05.

## Exact-source successful compiler/lint/axiom loop

Pinned toolchain: Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
Commands: lake build $(cat scripts/rebel/m06-targets.txt), followed by
python3 scripts/rebel/audit_exact_leaf.py. Full workflow gates remain separate.

| Source | Run / job | Target and supplemental result |
|---|---|---|
| 3ec0f0b4 | 35502961705 / 106057880329 | SUCCESS; 47 targets; 3,296 Lake jobs; 74 transitive declaration audits; nine modules normal/slow lint. |
| 0b6d3f36 | 35503252402 / 106058633996 | SUCCESS; 48 targets; 3,297 Lake jobs; 87 transitive declaration audits; ten modules normal/slow lint. |

Latest log: artifact 10602982590, m06-targeted-0b6d3f3689b3d94a75f5da29d2c2a6879e65c130.
ZIP SHA256: 48b7b1580f4f2794df63c0338b5b600d0bce3e0bac18c206899e5272888720e6.
Full raw log SHA256: 462679377b59f502576b5c0fb82b655b973f609a6fb5257e5eeae1cd3f6cfd3d.
The log includes all 87 complete axiom records and all ten lint pass markers;
no error: or warning: records occur. Each axiom set is a subset of
[propext, Classical.choice, Quot.sound]. M06-driver-axioms.txt is explicitly
a selected normalized excerpt, not a replacement for the full-log hash.

Earlier successful exact-driver log: artifact 10603395494.
ZIP SHA256: e266afbfd6eeed915527616f76629ca359d2667b9fcd05960647738b1dd48e31.
Full raw log SHA256: 4a4c81f1444b305e1857a6210947834fffa2e7586504931d373618c39ed59928.

At this evidence commit, full CI 35503252425/job 106058634035 and full ReBeL
35503252397/job 106058634054 on 0b6d3f36 remain in progress. This supplemental
slice success is not mislabeled as full-workflow success or M06 acceptance.

## Observed failures, preserved rather than hidden

067ca5fe failed run 35494541092/job 106035094438 on dependent kernel rewriting.
6b7cd969 failed 35502165000/job 106055742412 because simplification still left
a dependent support condition. 7166f79d fixed it and compiled in
35502452287/job 106056533668, but its additional audit generator failed:
untyped numeric counters were inferred as MessageData. Both counters now have
explicit Nat types; allowed axioms and audited declarations were not relaxed.
At c09549c9, run 35502572377/job 106056851149 rejected the reserved binder
prefix in the clamp lemma. Renaming it prefixLaw retained its mathematical type.
Both repairs were then exercised by the two completely successful target runs.

## Reproducible source and offline checks

Snapshot artifact 10602793067 from run 35503252397 identifies exact source 0b6d3f36.
Snapshot ZIP SHA256: 1b9d9d9729a53ddc5c0879a8761eaa47dc5330ac1d951702f063ad9b21617c82.
All changed proof files, the import root, target list and supplemental auditor
were compared byte-for-byte with the retrieved snapshot. Offline processing
used only plugin-downloaded data, no local git or direct GitHub access.

All 76 existing Python tests passed with warnings-as-errors. Coverage and
inventory structure checks passed with all 3,054 original expanded rows intact.
They remain 64 verified, 41 qualified, five refuted, 406 context-indexed,
one empirical record and 2,537 pending; these are not a completion percentage.
No width violations occurred in 486 non-Experimental Lean files. The full
ReBeL audit enumerates 161 modules; enumeration is not a completed full audit.

| Changed proof | SHA256 |
|---|---|
| CFRDFactualMixture | e943bf35357e2c974517b6ce77bc928e4ae3830bd9c993d7be01599097c37668 |
| CFRDClamp | 4e934a4215e0a7fc8650e20d97a38c6ba3ec40f5a78b0af10193172f8a245a5e |
| CFRDExactDriver | 8dce32fe7f7ed276beedde7520e4b2b70f5f8cc296935fcef1cbe0a04a017a70 |
| CFRDExactSafety | 8ff2327733dd9f00a3c70bfe87f4be23276ed27171f41a22e15e9c2fde270a27 |
| CFRDNoisyDriver | 6be99b6170b94e9c9be9dbb295e7db08a841f686c183e01ae5a41c4ad61f5bc8 |
| Examples/CFRDExactDriver | adf8dbfae000029caaf203ec42f961c535db89720f54a8a36e8223014d88eb79 |

## Semantic scope and declarations

The finite model uses full AOH, finite legal histories/actions, a legal fallback,
canonical continuation laws, and full information-local behavioral deviations.
Perfect recall and the clock are constructed by the full-AOH interface.
Nash/security additionally use two players, real zero-sum bounded utilities,
and positive outer iteration count. The hidden history is never a policy input.

cfrDDepthProfile_leafOptimal transports any local loss through trunk restoration
using an equal unilateral prefix law and the proved cut-root conditional laws.
The equality is not global profile equality; the negative control refutes that.
cfrDConstructedExactOracle_accurate and _leafOptimal derive the two actual-round
contracts from the already constructed factual child Nash and counterfactual
response. cfrDConstructedExactOracle_isNash and _carried_security consume them.

cfrDConstructedNoisyOracle_accurate and _leafOptimal instead use the perturbed
oracle's actual cfrDState recurrence. Numerical perturbations can alter future
trunks; no unperturbed trace is assumed. Its _carried_security concludes the
corrected A*error+B/sqrt(T) bound with explicit existing constants. The error
bound is still an explicit numerical assumption, not a proof about a network.
The original-game comparison equilibrium only names the reference value;
no child equilibrium, query equality or local quality inequality is supplied.

Nine compiled controls cover live exact accuracy/optimality/Nash, legal
zero-own-reach deviation continuation, zero remaining fuel, false global
profile equality, perturbed accuracy and child optimality, and nonzero 1/4
prediction difference. The bias example does not claim the learning trace must
change. Existing seed/average, replacement and zero-joint-only controls remain.

## Remaining boundary

Exact child solves are noncomputable Nash selections. Finite-T child CFR with
an information-conditioned loss contract is not constructed here. Root
approximate Nash alone cannot be substituted for that uniform typewise claim.
privateCarriedContinue retains the selected complete policy; fresh recursive
re-solving at later carried PBSs needs its own construction and transfer proof.
Preserve numerical error, child loss and outer finite-T error separately, and
the printed versus corrected Theorem 3 statements. The original M06 coverage
parents remain pending until those obligations and full acceptance are closed.
