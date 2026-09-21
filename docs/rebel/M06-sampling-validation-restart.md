# M06 sampling validation restart

This work continues from the exact remote source
c60f3b20d333557adb39509399b92029e64f005e on
rebel/m06-information-sampling-20260921.
The validation work branch is rebel/m06-sampling-validation-20260921.
The inherited source and its history are retained; no force update or main
integration is performed.

Target workflow 35563998496, job 106222156622, compiled its declared targets
but failed its supplemental validation. Compilation alone is not acceptance.
The job log contains unused-argument and unused-Fintype diagnostics in the
sampling proof slice. Resolve these at the declaration/proof boundary without
turning off linters, changing allowed axioms, or replacing the actual CFR
iteration family by an unrelated sampler. Re-read exact-source diagnostics
and authoritative source before applying each repair.

The desired guarantee remains equality of complete continuation laws for one
retained, private, uniform index drawn from the actual child CFR iterations,
against independently selected behavioral opponents. Preserve the supplied
joint PBS, finite-T errors, zero-reach cases, and the distinction between
aggregate sampling safety and safety of an individual sampled iterate.
Do not identify independent per-player sampling with a shared diagonal draw.

Original M06 acceptance remains pending. A successful one-PBS correspondence
is not yet a proof of independently re-solved recursive play. Coverage and
STATUS must distinguish this validation checkpoint from accepted completion.
