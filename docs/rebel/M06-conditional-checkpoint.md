# M06 conditional-oracle checkpoint

Restarted from `b400dc5763ed671e7092eab033b826257a8ab0fe`, not from main.
The existing frontier target passed run `35448400485`; its source-inventory
run `35448400558` passed. Full ReBeL run `35448400564` was cancelled and is
not acceptance evidence. Main remains `6a6cbdaa`.

The 63-file baseline document review recorded in M06-checkpoint.md is retained;
the two later M06 checkpoint documents and the actual frontier code were read.
The published supplemental Theorem 3 and its proof on printed pages 21-22,
and Burch et al. arXiv:1303.4441v4 Theorem 2 and the counterfactual-best-response
qualification, were checked again. The original finite-T error formula remains
separate from a corrected result.

New `ConditionalOracle.lean` disintegrates arbitrary joint leaf laws into
information fibers, derives exact/approximate and information-weighted backup
identities, connects the exact values to the same canonical continuation
profile, and constructs iteration-specific joint public-belief queries.
This addresses why a value-vector oracle does not supply hidden-history values.
It does NOT yet assert the complete CFR-D regret or recursive test-time safety
theorem. In particular, the counterfactual reweighting and off-path contracts
must not be replaced by ordinary on-path Nash or by a stored root-regret bound.

Compilation of this new slice is pending at commit creation; use the declared
M06 target workflow and its exact-SHA artifact. No coverage row is promoted.
Large compiler-artifact materialization again produced local tool transport
timeouts. Further proof feedback uses the GitHub Actions compiler loop rather
than making local GitHub connections. All repository changes use the connector.
