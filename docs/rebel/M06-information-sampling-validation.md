# M06 actual information-set iteration sampling: validation evidence

## Exact source and preserved ancestry

Inherited checkpoint: af6f600727b0c50906155c54f23a26e7529426fd.
Current proof source: 72a837daf5f5e295b38e3da67765b3f7f4278425.
Proof tree: 0334cde0807015217f4dec7a2417b717eaa25be7.
Source branch: rebel/m06-supported-sampling-20260921.
Document checkpoint: rebel/m06-sampling-checkpoint-20260921.
Main: 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098, unchanged and not integrated.

The GitHub compare reports six commits ahead and zero behind the inherited
checkpoint. The only modified pre-existing source files are the three
validation consumers, each with five additions and zero deletions. Five new
Lean modules and two work notes are added. No dependency pin, workflow,
architecture rule, allowed-axiom set, theorem statement, counterexample or
content-hashed coverage row is modified or removed. The status snapshot in
this checkpoint reuses the inherited STATUS blob without editing its bytes.

## Exact-source job observations

The target run is 35564914972, job 106224764818. Its declared-target compile
step has completed SUCCESS. The supplementary compiler/lint/axiom step is
still running at the initial recording point; it is not counted as a pass.
There are 93 declared targets and 55 supplementary modules, including all
five new modules. Each new module appears in the public Analysis umbrella,
the M06 target list and scripts/rebel/audit_exact_leaf.py.

Full CI: run 35564914904, job 106224769688, currently running.
Full ReBeL: run 35564914948, job 106224766262, currently running.
The full ReBeL width, static architecture, ledger/inventory/adversarial
fixtures and existing rational Lean solver/runtime checks have succeeded.
Its final all-module compiler/lint/axiom and cleanliness gates have not yet
completed. Intermediate steps do not substitute for those final results.

The GitHub source snapshot artifact is 10624021228, named
rebel-source-72a837daf5f5e295b38e3da67765b3f7f4278425. Its server-reported
SHA256 is 46a0d64a1b960cefac6c21e61aba52c97770a40ab6f650d57d4703c97b2def71.
This digest is reported by GitHub, not independently recomputed locally.
No local final compiler execution, Python suite or final archive comparison
is claimed. Source inspection and exact job reads use the GitHub plugin.

## Repair provenance

c4fee1dbb01520be898fce5a888c6edcf6a43228 first constructed the actual sampler.
1abea3d7c81810e1d0429f22fe1b1a25ea02d70a connected the parent's actual table
and public-prefix splice and registered the first seven controls.
c60f3b20d333557adb39509399b92029e64f005e supplied the original-history type
to Option.some_injective. It compiled, with 614 allowed-axiom audit records,
but supplementary lint rejected two undocumented compiler-generated proofs
under pbsRootCFRIterate. That intermediate commit is not lint-accepted.
cbed62b5592554e011f78db3130ae939e227049e added the supported-root extension
and five additional controls. Its declared-target compilation succeeded;
its supplementary run was cancelled by the following repair, not accepted.
72a837daf5f5e295b38e3da67765b3f7f4278425 separates the internal native
instantiation from the documented public iterate function. The recurrence
and every public law statement are unchanged. All private declarations
continue to be audited. No documentation or proof check is disabled.

A contents-API update using a stale file hash was rejected with HTTP 409.
The file was re-read and the unchanged remote contents reconciled before
retrying with its current blob hash. No force update or external edit was
silently overwritten.

## Semantic coverage and remaining acceptance

New public general theorems: 14; private proof helpers: three; example
theorems: twelve. Generated declarations and their transitive-axiom records
are counted separately and must be obtained from the final audit log.

The accepted inference sought here is actual-iteration law equality, first
at the model PBS, then at every supported root and any supported reweighting.
It does not assert the model posterior is the unknown opponent's true law.
No common T across arbitrary posteriors, zero-model-mass cancellation,
individual-iterate Nash, shared-index two-player equality or fresh independent
recursive safety is claimed. Existing omitted-type completion remains a
separate requirement. Original SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and
SAFE-THEOREM3 rows remain pending. Read final results before accepting this
slice; completing this slice does not complete M06.
