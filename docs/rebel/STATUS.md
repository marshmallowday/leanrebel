# ReBeL status — M06 in progress; M05 accepted

## Active restart point

Continue on `rebel/m06-conditional-loss-20260920`; read its actual remote HEAD.
This work descends from b5e15493d6efdc4fa641aeb690e40b24a0764d11 without replaying
older stages. Main remains 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.
M06-status-before-conditional-loss.md preserves the preceding STATUS byte-for-byte.

## Inherited verification now resolved

At b5e15493, ReBeL full run 35503671838/job 106059741567 PASSED. The downloaded
artifact 10602644467 reports REBEL_AXIOM_AUDIT_PASS declarations=3394 and
REBEL_VALIDATION_PASS modules=161. Every transitive set uses only propext,
Classical.choice and Quot.sound. ZIP SHA256:
2569715f99adaec69c23fba2b4940309b23302d7e902d4f0cde06548a4b1ecfc.
The earlier 0b6d3f36 full CI 35503252425/job 106058634035 passed; its ReBeL run
35503252397 was cancelled. The later b5e15493 success is separate exact-source
evidence, not a relabeling of that cancellation.

## Current dependency slice

PBSApproximateOptimality derives the mean and probability-weighted conditional
best-response gaps from canonical approximate PBS Nash and the existing legal
typewise response. A supported type yields error / type probability; an
explicit mass-proportional root budget yields the desired conditional loss.
Zero probability is not divided away or treated as conditional optimality.
The new source has its own pending compiler/lint/axiom and example obligations.
See M06-conditional-loss.md for scope and the coverage journal.

## Remaining M06 work

Connect the approximate estimate to joint off-path completion and the actual
CFRDLeafOptimal contract. Then construct finite-iteration child solves with
the needed budgets, and connect fresh recursive carried execution. The current
exact/noisy drivers retain their noncomputable exact-child scope. Root epsilon
Nash alone is not a probability-independent conditional guarantee.
Keep numerical prediction error, child loss and outer finite-T error separate.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain open; no main
integration, dependency update, test deletion or acceptance promotion is made.
