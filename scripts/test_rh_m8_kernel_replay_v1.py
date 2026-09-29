import unittest
from replay_rh_m8_kernel_v1 import imports, audit, patched_correction

class ReplayTests(unittest.TestCase):
    def test_imports(self):
        self.assertEqual(imports('import Mathlib\npublic import A.X B\n'), ['Mathlib','A.X','B'])
    def test_nested_comments(self):
        self.assertEqual(imports('/- import Wrong\n/- import Bad -/ -/\nimport Good -- import Bad\n'), ['Good'])
    def test_strings(self):
        self.assertEqual(imports('def s := "import Wrong"\nimport Good\n'), ['Good'])
    def test_long_whitespace(self):
        self.assertEqual(imports(' '*100000+'import Good\n'), ['Good'])
    def test_audit(self):
        self.assertEqual(audit('#print axioms A\n', "'A' depends on axioms: [propext,\n Classical.choice, Quot.sound]"), {'A':['Classical.choice','Quot.sound','propext']})
    def test_axiom_free(self):
        self.assertEqual(audit('#print axioms A\n', "'A' does not depend on any axioms"), {'A':[]})
    def test_missing(self):
        with self.assertRaises(ValueError): audit('#print axioms A\n', '')
    def test_sorry(self):
        with self.assertRaises(ValueError): audit('#print axioms A\n', "'A' depends on axioms: [sorryAx]")
    def test_custom(self):
        with self.assertRaises(ValueError): audit('#print axioms A\n', "'A' depends on axioms: [Foo]")
    def test_error(self):
        with self.assertRaises(ValueError): audit('#print axioms A\n', "error: failed\n'A' depends on axioms: [propext]")
    def test_duplicate_probe(self):
        with self.assertRaises(ValueError): audit('#print axioms A\n#print axioms A\n', "'A' depends on axioms: [propext]")
    def test_duplicate_output(self):
        with self.assertRaises(ValueError): audit('#print axioms A\n', "'A' depends on axioms: [propext]\n'A' depends on axioms: [propext]")
    def test_unexpected_probe(self):
        with self.assertRaises(ValueError): audit('#print axioms A\n', "'A' depends on axioms: []\n'B' depends on axioms: []")
    def test_patch_rejects_unknown(self):
        with self.assertRaises(ValueError): patched_correction(b'not the pinned file')

if __name__ == '__main__': unittest.main()
