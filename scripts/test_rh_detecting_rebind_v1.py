"""Regression tests for the fail-closed replay harness, not mathematical proofs."""
import hashlib
import subprocess
import sys
from pathlib import Path
import unittest
try:
    import rh_detecting_rebind_v1 as m
except ModuleNotFoundError:
    m = None


class ReplayTests(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(m, 'Replay harness is not implemented')

    def test_header_nested_comments(self):
        src = '/- import Bad /- nested -/ -/\nimport Foo Bar -- import Nope\n\nnamespace A\n'
        self.assertEqual(m.imports(src), ['Init', 'Foo', 'Bar'])

    def test_public_meta_import(self):
        self.assertEqual(m.imports('module\npublic meta import all Mathlib.Foo\npublic section\n'),
                         ['Init', 'Mathlib.Foo'])

    def test_prelude(self):
        self.assertEqual(m.imports('prelude\nimport Init.Prelude\n'), ['Init.Prelude'])

    def test_comment_does_not_hide_import(self):
        self.assertEqual(m.imports('import Foo /- x\ny -/\nimport Bar\ndef x := 0\n'),
                         ['Init', 'Foo', 'Bar'])

    def test_import_in_string_is_not_header(self):
        self.assertEqual(m.imports('import Foo\ndef s := "import Forged"\n'), ['Init', 'Foo'])

    def test_reject_unsupported_import(self):
        with self.assertRaises(ValueError):
            m.imports('import Foo; import Forged\n')

    def test_reject_unclosed_header_comment(self):
        with self.assertRaises(ValueError):
            m.imports('/- unterminated')

    def test_long_body_declaration_does_not_backtrack(self):
        code = ("import sys; sys.path.insert(0, " + repr(str(Path(m.__file__).parent)) + "); "
                "import rh_detecting_rebind_v1 as m; "
                "assert m.imports('import Foo\\ndef LongLongLongLongLongLongLongLongName : Nat := 0\\n') == ['Init', 'Foo']")
        subprocess.run([sys.executable, '-c', code], check=True, timeout=3)

    def test_git_blob(self):
        self.assertEqual(m.blob(b'hello\n'), hashlib.sha1(b'blob 6\0hello\n').hexdigest())

    def test_topological_closure(self):
        graph = {'R': ['A', 'B'], 'A': ['B'], 'B': []}
        self.assertEqual(m.closure(['R'], lambda n: graph[n]), ['B', 'A', 'R'])

    def test_cycle_rejected(self):
        with self.assertRaises(ValueError):
            m.closure(['A'], lambda n: {'A': ['B'], 'B': ['A']}[n])

    def test_unknown_dependency_rejected(self):
        with self.assertRaises(KeyError):
            m.closure(['R'], lambda n: {'R': ['Missing']}[n])

    def test_multiline_axioms(self):
        log = "'A' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
        self.assertEqual(set(m.audit(log, ['A'])['A']), m.ALLOWED_AXIOMS)

    def test_missing_probe_rejected(self):
        with self.assertRaises(ValueError):
            m.audit("'A' depends on axioms: [propext]", ['A', 'B'])

    def test_sorry_rejected(self):
        with self.assertRaises(ValueError):
            m.audit("'A' depends on axioms: [sorryAx]", ['A'])

    def test_custom_axiom_rejected(self):
        with self.assertRaises(ValueError):
            m.audit("'A' depends on axioms: [Forged]", ['A'])

    def test_duplicate_probe_rejected(self):
        with self.assertRaises(ValueError):
            m.audit("'A' depends on axioms: [propext]\n" * 2, ['A'])

    def test_error_rejected(self):
        with self.assertRaises(ValueError):
            m.audit("error: invalid\n'A' depends on axioms: [propext]", ['A'])

    def test_explicit_supplement_only(self):
        m.admit_supplement('WeilMomentAnnihilatorV1',
                           '0fe118c9a62b240beb3469805d50fb3ec1dccb4e', False)

    def test_supplement_cannot_shadow_current(self):
        with self.assertRaises(ValueError):
            m.admit_supplement('WeilMomentAnnihilatorV1',
                               '0fe118c9a62b240beb3469805d50fb3ec1dccb4e', True)

    def test_unknown_supplement_rejected(self):
        with self.assertRaises(ValueError):
            m.admit_supplement('HiddenDependency', '0' * 40, False)

    def test_supplement_blob_drift_rejected(self):
        with self.assertRaises(ValueError):
            m.admit_supplement('WeilMomentAnnihilatorV1', '0' * 40, False)

    def test_no_axiom_probe(self):
        self.assertEqual(m.audit("'A' does not depend on any axioms", ['A']), {'A': []})


if __name__ == '__main__':
    unittest.main()
