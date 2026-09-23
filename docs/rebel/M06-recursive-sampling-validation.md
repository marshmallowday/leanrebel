# M06 recursive-sampling compiler checkpoints

Implementation33a2eba88a3a558fbc6ff9b7d5ecfd2ba5bf4613 ran M06 target
35841049671/job107115903923. The inherited modules compiled. The new
FinDistSequentialError failed on reserved token `prefix` used as a binder,
and a line break following `simp ... at` (lines35 and68). Its dependent two
new modules were not validated. No theorem statement was weakened.

Repair e257a705044756a1d48688ea5c6fb8dc4863055b renamed append binders to
before/after and separated hypothesis and goal simplification commands.
Target35842290923/job107119977537 then reported the remaining append proof
obligation: its pointwise induction hypothesis did not rewrite an unapplied
kernel under bind. The hybrid error theorem itself produced no diagnostics.
ReBeL35842290765/job107119977489 also reported six lines of width102; the
configured limit is100. Both failures are retained, not bypassed.

The next repair explicitly applies bind_congr before the pointwise induction
hypothesis, uses the same method for the runner/append consumers, and wraps
the six overlong lines. All theorem statements and audit conditions are unchanged.
Check the repair commit's own CI. No success is inferred from source editing.

Failed target artifact10741169836 has GitHub-reported SHA256
7f1dc107c43a986f799fc2183d827a123cd3cb38609fc9c27899329cddbdb4d3.
Failed target artifact10742305829 has GitHub-reported SHA256
6270ca71f9b6cdccf85a24d5e7c864f30631c7779f321e976a9be3b00deaf34a.
The validated predecessor6c541fca and its full CI evidence are documented in
M06-recursive-sampling.md. STATUS.md states the remaining semantic obligations.
