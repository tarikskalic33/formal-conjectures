# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
import importlib.util, tempfile, unittest
from pathlib import Path
SCRIPT = Path(__file__).with_name("rh_theorem_inventory.py")
SPEC = importlib.util.spec_from_file_location("rh_theorem_inventory", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC and SPEC.loader
SPEC.loader.exec_module(MODULE)

class TheoremInventoryTests(unittest.TestCase):
    def test_captures_unannotated_theorems_and_namespaces(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            p = root / "AegisRH" / "SmallWindow" / "Example.lean"
            p.parent.mkdir(parents=True)
            p.write_text("import Mathlib\nnamespace Demo\ntheorem first : True := by trivial\nlemma second : True := by trivial\nend Demo\n", encoding="utf-8")
            rec = MODULE.scan(p, root)
            self.assertEqual([d["name"] for d in rec["declarations"]], ["Demo.first", "Demo.second"])
            self.assertEqual(rec["imports"], ["Mathlib"])
            self.assertEqual(len(rec["sha256"]), 64)

    def test_skips_comments_and_records_axioms_and_defs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            p = root / "Example.lean"
            p.write_text("/- theorem fake : False := by sorry -/\naxiom premise : True\ndef helper : Nat := 1\n", encoding="utf-8")
            rec = MODULE.scan(p, root)
            self.assertEqual([d["name"] for d in rec["declarations"]], ["premise", "helper"])

if __name__ == "__main__":
    unittest.main()
