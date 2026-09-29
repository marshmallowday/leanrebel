# ReBeL status — cross-query values pending Actions; M06 incomplete

Branch: rebel/m06-kernel-value-repair-20260927.
Parent and accepted dependency:ffab72bcee96bd262a0a1c5f3966a5e96b41aed7.
Default main:6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.
Chat baseline:9457c198126f3c8b7cb1045bbed2e0053788636f.
Account marshmallowday has push/admin permission.

Exact ffab72b passed CI36500385539, checks36500385536,
target36500385608 and inventory36500385571. Complete logs yielded
2437/5571 unique targeted/global axiom records, only the3 permitted axioms;
all155/295 lint modules matched the registered sets and final markers.
Full build4322/lintbuild4092, architecture3VERIFIED, static2metrics0,
rational runtime and235tests (checks9.688s/inventory10.078s) passed.
See M06-security-potential-ffab72b-accepted.md. Artifact metadata was read;
ZIP contents were not. These results do not validate the new source.

New PBSRecursiveValueStability compares two ACTUAL recursive solver outputs
on different PBSs, using cross deviations and one uniform fixed-profile
root error. Both Nash premises are supplied by the independent computations.
Noise, cut partition, fallback and tolerance may differ; protocol, payoff
and total horizon agree. A concrete bound is the sum of both tolerances
plus bound*L1(root laws). The second finite private draw secures the first
computed model value with firstTolerance+2*secondTolerance+rootError against
any fixed unknown opponent, on the second model law.

CFRDStoredSolveValue applies the accepted fixed-kernel stopped-mass bound
BEFORE the Nash comparison, so independently recomputed public/live self-play
values differ by at most both tolerances plus2*bound*stoppedMass/publicReach.
The actual public posterior is not silently filtered. A real noisy-parent
example keeps the stored-state equality and proves zero stopped mass from
this game's public termination property. Other consumers compare [1,1,1]
and[3] searches, including the actual private draw.

Five independent Fraction controls cover729 cross-root/profile combinations,
public/live rare reach and sharp denominator, scalar/typewise/policy
distinctions, private security with separate solver errors, mismatched
horizon, resampled late draws and lost conditional correlation.
They are not executions of CFR. Expected surface:196 build targets,
158 targeted/298 global audit modules,240 Python tests. New-SHA Actions required.

See M06-cross-query-value-batch.md for actual signatures, type review and
batch boundary. The static review includes full-information universe/index
alignment, explicit condition S, observation-dependent PBSs, independent
solver arguments, fuel equations and every concrete consumer. It caught a
keyword binder before commit. Static review is not compiler success.

Remaining: new-SHA validation; useful small native conditional-root/support
and incumbent/potential differences across actual successive queries;
internal chance-rooted/fresh-original correspondence with noise/fallback/
budget/clock/root encoding; full recursive small-rate safety and
SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 source acceptance.
Same-horizon scalar stability is not conditional vector equality or solver
identity. Fresh self-play is not an asserted exact game value or network
target. No prior reset, posterior calibration or policy closeness is assumed.

All accepted source journals/pins remain unchanged. Frozen coverage.json:
2fc8cc9ad6607d61bfe397707fb96ac322fbb800. Previous owner ledger preserved
at M06-kernel-value-transport-coverage-at-ffab72b.json, original blob
14c8922307cd48a3af1b099ba22c8ab9433301c7. Theorem3 interpretation remains
in M06-theorem3-interpretation.md; finite-T and child loss stay independent.

Main agent only; review types before each commit, batch related work and
fixes, confirm separate same-SHA runs, schedule one check about50minutes
after push in JST. If still running, check once and defer about10minutes.
Never cancel active workflows. Full M06 remains incomplete.
