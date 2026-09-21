# M06 actual retained iterations at parent private/live queries

## Construction checkpoint

Source extends the lint repair `2f4037460bf95104c723f6cdba87ddc2ad9a8227`.
The repair's exact M06 compile run `35578223051`, job `106264814990`, succeeded.
Its full CI `35578223118` and ReBeL audit `35578223045` must be checked separately;
they are not claimed successful by the targeted result.

The new definitions and theorems are in the already registered and audited
`GameTheory.Analysis.ReBeL.CFRDInformationSampling` module. The existing
`PBSSupportedSampling` proof is imported, not duplicated or treated as a new result.

- `CFRDInformationQueryFactual` records actual private/live observation support.
- `cfrDInformationQueryLaw` is the parent's canonical unilateral reference
  conditional. It remains a correlated history law, not a fabricated private PBS.
- `cfrDInformationQuery_possible` derives the live public posterior witness.
- `cfrDInformationQuery_support` derives query domination by that posterior from
  the existing factual/reference conditional equality. No supplied domination,
  posterior-identity, positive-mass-floor or conditional-value premise is added.
- `cfrDInformationChildProfile_sampling_supported` connects the rootwise law to
  the existing public-prefix splice at every supported original root.
- `cfrDInformationFactualQuerySample` draws from the actual finite child recurrence
  with the unchanged public-posterior-dependent count and retains the private index.
  Its law and every history observable equal the parent-spliced child against
  arbitrary fixed behavioral opponents.

This source is a compiler candidate until its own target-SHA checks are inspected.
Do not promote original coverage from candidate source alone. No dependency,
axiom allowlist, linter or architecture gate is weakened.

## Boundary and next step

The query-law theorem assumes factual private/live support. This is an explicit
branch condition, not the whole remaining M06 theorem. A zero-factual-mass query
must use the existing zero-own-reach response completion; it must not condition
an impossible public posterior or cancel a zero root probability. Connect both
branches to the existing `CFRDLeafOptimal` consumer next, then address independently
re-solved recursive carried-PBS play with finite outer-T and prediction losses.

Original `SEARCH-FRONTIER`, `SEARCH-CFRD`, `SEARCH-ERROR`, and `SAFE-THEOREM3`
remain pending. These query identities do not prove M06 or numerical refinement.
