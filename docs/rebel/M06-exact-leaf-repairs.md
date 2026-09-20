# M06 exact-leaf compiler and audit repair checkpoint

Parent f99c67b1572f58c655a96119292c7f7a2ed2d6c7 had two remaining compiler
issues in CFRDFactualMixture: an unused DecidableEq section variable and a
reference-kernel dependent conditional whose predicate was not rewritten.
The repair scopes the instance to the operations that need it and explicitly
splits supported versus unsupported reference queries, preserving the theorem.

ReBeL run 35493770557/job 106033080096 correctly rejected five library output
commands under the unchanged architecture policy. Those commands are moved
out of library sources. No theorem or example is removed. The supplemental
scripts/rebel/audit_exact_leaf.py generates its inspection file only in .lake.
It checks every declaration (including private declarations and transitive
axiom dependencies) in the five new modules, fails on unapproved axioms, and
runs the existing Batteries normal/slow linter for each of those modules.

The supplemental step is added to the M06 targeted workflow. The original
43-target build and repository-wide build/lint/architecture/axiom workflows
remain required and unmodified in scope. This is additional exact-source
feedback, not an acceptance shortcut. All action pins, permissions and audit
allowances remain unchanged. Inspect the new SHA's actual results; the
presence of this script is not a successful compiler, lint or axiom audit.
