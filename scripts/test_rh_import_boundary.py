# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Regression tests for the RH target's legacy AEGIS replay import boundary."""

from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "FormalConjectures/Millennium/RiemannHypothesis.lean"
IMPORT_PREBUILD = ROOT / "scripts/rh_pr63_import_prebuild.sh"
WINDOW_PREBUILD = ROOT / "scripts/rh_pr63_proved_window_prebuild.sh"


class RHImportBoundaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.target = TARGET.read_text(encoding="utf-8")
        cls.import_prebuild = IMPORT_PREBUILD.read_text(encoding="utf-8")
        cls.window_prebuild = WINDOW_PREBUILD.read_text(encoding="utf-8")

    def test_formal_conjectures_copyright_header_is_preserved(self):
        self.assertTrue(
            self.target.startswith(
                "/-\nCopyright 2026 The Formal Conjectures Authors.\n"
            )
        )
        self.assertIn("https://www.apache.org/licenses/LICENSE-2.0", self.target)
        self.assertIn("limitations under the License.", self.target)

    def test_legacy_replay_artifacts_are_not_imported_from_module_mode(self):
        # Both AEGIS prebuild scripts emit legacy (non-module) .olean files.
        # A module-style target rejects those artifacts with Lean's
        # "cannot import non-module ... from module" error.
        self.assertNotIn("\nmodule\n", self.target)
        self.assertNotIn("@[expose] public section", self.target)
        self.assertIn("import RHRestrictedWeilCriterionV13", self.target)
        self.assertIn("import RHSmallWindowCanonicalJoinV1", self.target)
        self.assertIn('lean -o "$OUT/$mod.olean" "$file"', self.import_prebuild)

    def test_small_window_join_uses_its_declared_namespace(self):
        self.assertIn(
            "AEGIS.RHSmallWindowCanonicalJoinV1."
            "riemannHypothesis_of_above_693_over_2000_v1",
            self.target,
        )
        self.assertIn('lean -o "$OUT/$name.olean" "$file"', self.window_prebuild)


if ( __name__ == "__main__" ):
    unittest.main()
