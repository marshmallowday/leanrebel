# ReBeL status — M06 in progress; M05 accepted

## Active restart

Continue on `rebel/m06-bounded-refresh-20260921`; re-read its remote HEAD.
The base is `a39599e3b47b1e50ca78d5a6385aa24035d25738`, including repaired
finite-child proof source f4671e42. Both full repository CI and full ReBeL
validation of a39599e3 succeeded. The downloaded log ends with 173 modules
and 3,544 transitive declaration checks. See M06-bounded-refresh-restart.md.
Main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098; no history is rewritten.
The preceding STATUS is archived byte-for-byte in M06-status-before-bounded-refresh.md.

## New compiler checkpoint

CFRDRefreshMix composes one real carried-memory step with its retained-policy
continuation, preserving the private selection and Bayesian state bookkeeping.
It constructs a private mixture of a fresh resolver and the currently retained
profile and derives a stage loss of at most 2*bound*rate from bounded utility.
No local replacement comparison or recursive safety conclusion is supplied.
Terminal and zero-fuel branches retain the canonical no-query behavior.
The new module is a targeted compiler input, NOT yet a validated result.
Add the concrete finite-PBS refresh schedule, umbrella/audit registration,
nontrivial controls and exact-source validation before accepting the slice.

The inherited finite normal-form child constructor remains unchanged. A fresh
solve at each carried PBS and its recursive loss transfer are the next task.
This bounded-refresh variant explicitly pays replacement loss. It is NOT a
claim of lossless independent equilibrium replacement or the paper's fixed-T
information-set child CFR. Retain the existing counterexamples and distinguish
prediction error, child loss, outer regret and refresh allowance.

Coverage: SEARCH-CFRD and SEARCH-ERROR gain only an unvalidated candidate here.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 parent obligations
remain pending; no M06 acceptance or main integration is claimed.
