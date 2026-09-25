# M06 native-gap global gate resolved

Validated source: `e65152038f6a9068be68aff28ad6845f74097e94`, from
`rebel/m06-native-gap-checkpoint-20260925`. This source preserves the native
proofs from `b11dbaffbc58c53ad048929ccb2a4d418b522d19`. This record supersedes
only the pending global-audit observation in M06-native-gap-validation.md;
it neither rewrites that historical observation nor accepts all of M06.

The GitHub plugin returned completed SUCCESS for ReBeL run `36131219015`,
proof job `108058664709`, and full repository CI `36131219021`, job
`108058665488`. The latter reports successful build, configured lint,
compiler-resolved reuse signatures, all three architecture gates and tracked
cleanliness. The former additionally reports successful ledger, inventory,
adversarial fixtures and rational-runtime checks.

The actual ReBeL artifact `10863686029` was downloaded through the GitHub
plugin and inspected. Its ZIP SHA-256 is
`b6753723bdff3d11a00906f7a642bf30ea43d1dd57baf1b514ae7457876a6f40`.
The complete rebel-validation.log SHA-256 is
`6443e1c09a672a713099915db69f1891abcecfffdeee65682af446d878c78b80`.
Its first line is the exact source above. It reports
`REBEL_AXIOM_AUDIT_PASS declarations=4799` and
`REBEL_VALIDATION_PASS modules=247`.

Both PBSNativeConditionalGap and Examples.PBSNativeConditionalGap have their
own REBEL_LINT_PASS entries, including the configured normal and slow linters.
The actual collected axiom lists for the seven main declarations are:

- pbsInformationCFR_conditional_sampling_value: [propext, Classical.choice, Quot.sound]
- pbsInformationCFRConditionalDrawGap: [propext, Classical.choice, Quot.sound]
- pbsInformationCFRConditionalDrawGap_nonneg: [propext, Classical.choice, Quot.sound]
- pbsInformationCFRConditionalDrawGap_mean_abs: [propext, Classical.choice, Quot.sound]
- pbsInformationCFR_native_query_mean_abs_le: [propext, Classical.choice, Quot.sound]
- pbsInformationCFR_native_mean_abs_le: [propext, Classical.choice, Quot.sound]
- pbsInformationBudget_native_mean_abs_le: [propext, Classical.choice, Quot.sound]

All names above are under GameTheory.ReBeL. The three controls
Examples.HiddenTypes.pbsNativeConditionalGap_live_type,
Examples.HiddenTypes.pbsNativeConditionalGap_live_budget and
Examples.ConditionalValueStability.nativeConditionalGap_changed_opponent_control
have the same complete allowed axiom list in that actual log. This is global
auditor evidence, not an inference from the earlier 100-module targeted audit.

The exact source snapshot artifact `10861639047`, from source job
`108058664947`, was also inspected. Its ZIP SHA-256 is
`d32ce4ebf06b58602c9c14a8f9c4031fba761a993ee134ee97c1f7f5ed8430c1`;
its tar SHA-256 is
`c1702a22662061fcd3e1479ed839990600a47cd4c93b1ecf6608a0507b64ad19`.
The embedded commit equals the validated source. Export extraction and log
inspection used no local Git or direct GitHub network access. No local Lean
compiler execution is claimed.

The semantic restrictions in M06-native-conditional-gap.md still apply:
fixed opponents, fixed compatible conditional-history kernels, the real
uniform own-iteration sampler and a PRODUCT query law. An actual later query
can be correlated with the retained seed. Separate marginal domination does
not justify reusing the product-law mean bound. The next slice addresses an
explicit JOINT density contract, not an unproved actual-carried-law rate.

Main was re-read at `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098` and was not
advanced. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain
pending in the live source ledger. No original source row is closed here.
