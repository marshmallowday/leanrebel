# M06 finite-plan child solver: implementation restart

Base: c16beb4d0325f487a25e902a68c47d7d7db01ca7. Main remains the accepted
M05 source 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098. No force updates.
Work branch: rebel/m06-finite-plan-rm-20260920. Read its actual remote HEAD.

The old full ReBeL runs at af8b6328 and c16beb4d ended cancelled, not passed.
The c16beb4d job lasted approximately the configured 30-minute limit.
23cebffa6447c332434cfa3ea86aa5073ee0d90f changes only that limit to 60;
it retains every audit, dependency/action pin, permission and failure gate.
Its independent branch retains the previous proof source for revalidation.

FinitePlanLearning now defines structural simultaneous regret matching over
complete finite plans. Its all-action regret bound uses canonical external
regret and the existing Blackwell matcher. This is a distinct normal-form
reference variant, not an assertion that the information-set CFR algorithm
has been implemented for arbitrary PBS roots, and not a numeric executable.

This is an unvalidated implementation checkpoint. It is in the M06 target
list and is automatically enumerated by the full ReBeL compiler/lint/axiom
scanner. Add the public umbrella and supplemental audit registrations with
the downstream PBS instantiation before accepting the slice.

Next: compile this recurrence; construct its two-player independent average
and canonical PBS realization; derive a finite iteration budget for supported
conditional types. Fresh recursive carried re-solving remains separate.
SEARCH-CFRD and SEARCH-ERROR are advanced but their original coverage rows,
SEARCH-FRONTIER and SAFE-THEOREM3 remain pending. No milestone promotion.
