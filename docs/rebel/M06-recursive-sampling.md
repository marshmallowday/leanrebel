# Recursive solver sampling and compiler recovery — candidate

Branch: rebel/m06-recursive-solver-20260924.
This checkpoint follows f375294fa122dcca803319d3466d0a96925e6ce5. Its target
35952776340/job107484869406 was inspected in full: all predecessor targets and
the budgeted parent compiled, while the new recursive module's equation binder
was shifted by automatic insertion of its implicit protocol. Make protocol E
explicit in PBSRecursiveDepthFamily and PBSRecursiveDepthNoise so recursive
calls actually range over newly constructed protocols. Retain the strictly
shorter-list recursion and induction theorem, with no child-Nash certificate.
Use let rather than letI in proof goals as required by the existing style gate.
Do not respond to this elaboration failure by raising heartbeat limits.

PBSComposedDepth now also defines its actual parent iterate, uniform retained
private draw, and exact original-history law transfer. Its proof uses canonical
run_unilateral_average and PBS own-AOH decoding; it assumes neither per-iterate
Nash nor zero numerical error. The selected iteration is fixed throughout the
continuation, not reselected independently at every action.

PBSRecursiveDepthDraw installs the actual structural tail solver into those
parent iterations and uses the same computed nonempty budget as the average.
Its all-history law and arbitrary-observable expectation agree with the actual
recursive average against each fixed unknown opponent. Empty cut lists have a
pure legal fallback rather than an invalid uniform draw over zero iterations.

PBSRecursiveDepthResolver consumes only incoming joint MODEL PBS and public
observations; actual hidden state and unknown opponent are not query inputs.
The step_some law keeps the selected profile and its own propagated model PBS
paired inside the canonical carried state. The stage installs it in the existing
finite memory runner. No-PBS and zero-execution-fuel branches retain existing
fallback/stopping semantics. This does NOT assert equality between model and
actual posteriors, independent posterior averaging, or arbitrary repeated-solve
safety. Source-level drift/support-rate obligations remain separate.

Examples retain all prior candidate controls and add the 3-level private-sampling
history law against arbitrary fixed opponents, no-PBS fallback for every public
observation, and zero-execution-fuel history preservation. Existing source
coverage, targets, audit entries, pins and lint/axiom gates are unchanged.
All new declarations are inside the three already registered modules; expected
supplemental validation count is 92. Acceptance requires this exact source's
compiler/lint/axiom CI, not the validated 751ad17a repair run.
