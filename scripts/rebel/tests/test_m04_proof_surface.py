"""M04's analytic proof surface must not escape the production consumers."""
import unittest
from pathlib import Path
from audit_axioms import AUDITOR, ROOT, proof_modules


class M04ProofSurfaceTests(unittest.TestCase):
    def test_every_basic_and_analytic_module_is_compiled_and_linted(self):
        modules = set(proof_modules())
        for stem in ('GameTheory/ReBeL', 'GameTheory/Analysis/ReBeL'):
            umbrella = (ROOT / (stem + '.lean')).read_text(encoding='utf-8')
            root_module = stem.replace('/', '.')
            self.assertIn(root_module, modules)
            for path in (ROOT / stem).rglob('*.lean'):
                module = path.relative_to(ROOT).with_suffix('').as_posix().replace('/', '.')
                with self.subTest(module=module):
                    self.assertIn(module, modules)
                    self.assertIn('import ' + module, umbrella)

    def test_axiom_audit_selects_both_defining_module_prefixes(self):
        # A declaration outside the advertised namespace is still checked:
        # selection is by defining module, not declaration spelling.
        self.assertIn('`GameTheory.Analysis.ReBeL', AUDITOR)
        self.assertIn('analysisPrefix.isPrefixOf modName', AUDITOR)
        self.assertIn('modulePrefix.isPrefixOf modName', AUDITOR)
        self.assertIn('Lean.collectAxioms name', AUDITOR)

    def test_ci_dependency_closure_uses_the_same_consumer(self):
        workflow = (ROOT / '.github/workflows/rebel.yml').read_text(encoding='utf-8')
        self.assertIn('from audit_axioms import proof_modules', workflow)
        self.assertIn('pending = proof_modules()', workflow)
        self.assertIn('python3 scripts/rebel/audit_axioms.py', workflow)
        lint_root = (ROOT / 'lint/GameTheory/LintAll.lean').read_text(encoding='utf-8')
        self.assertIn('import GameTheory.Analysis.ReBeL', lint_root)


if __name__ == '__main__':
    unittest.main()
