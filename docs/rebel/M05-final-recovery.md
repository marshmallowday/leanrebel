# M05 final recovery checkpoint

## Preserved remote state

Resume from `20cbe32f11fdd1618110ed0e4a7d7359e78a4d6b` on
`rebel/m05-evidence`. This is four commits ahead of the proof source
`b1b557b7e3c9471e5f774c7fc400c1665742a614`, with documentation and metadata-test
changes only. The repaired `44cd2d6` and earlier `18d11b3` work are ancestors;
do not replay them or diagnose the superseded failing run as the current state.

The following exact-source runs were observed completed successfully:

| Source | Gate | Run |
|---|---|---|
| b1b557b7e3c9471e5f774c7fc400c1665742a614 | ReBeL compiler/lint/axioms | 35411381522 |
| b1b557b7e3c9471e5f774c7fc400c1665742a614 | Full repository CI | 35411381563 |
| 20cbe32f11fdd1618110ed0e4a7d7359e78a4d6b | ReBeL compiler/lint/axioms | 35412423210 |
| 20cbe32f11fdd1618110ed0e4a7d7359e78a4d6b | Full repository CI | 35412423211 |
| 20cbe32f11fdd1618110ed0e4a7d7359e78a4d6b | Source inventory | 35412423259 |

The source snapshot was retrieved through the GitHub plugin from artifact
`10573958456`; its tar SHA-256 is
`5d6c94a43140d65206928c1f969ac902be3b34944367a5dccccb1c0a3a3f4dde`.
The validation artifact is `10574842255`. Local processing of these delivered
files is offline; no local Git or HTTP access to GitHub is used.

## Remaining acceptance work

Inspect the actual proof/axiom output, source-row dispositions, canonical PBS
entry points and all documentation changes. Then atomically activate the
M05 acceptance journal with its accepted-source marker and update STATUS.
Preserve all original obligations and the distinction between qualified,
verified and refuted source claims. Do not claim that the radial extension
is the corrected concave extension, or that the entire ReBeL framework is done.

This checkpoint does not activate the candidate ledger or change main.
After the acceptance commit passes the required workflows, re-read branch
heads and integrate without a force update. Keep earlier checkpoint branches.
