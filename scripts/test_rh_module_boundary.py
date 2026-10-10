# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Guard the official RH target against mixing Lean module and legacy imports.

The currently pinned RH V13 and small-window producer objects use legacy Lean
import mode. The official target must not switch to the modern `module` mode
without first migrating and replaying the imported producer modules.
"""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "FormalConjectures" / "Millennium" / "RiemannHypothesis.lean"
LEGACY_PRODUCERS = frozenset({
    "RHRestrictedWeilCriterionV13",
    "RHSmallWindowCanonicalJoinV1",
})


def mismatched_legacy_imports(source: str) -> set[str]:
    before_imports = source.split("\nimport ", 1)[0]
    modern_mode = bool(re.search(r"(?m)^\s*module\s*$", before_imports))
    if not modern_mode:
        return set()
    imports = set(re.findall(r"(?m)^import\s+([A-Za-z0-9_.]+)\s*$", source))
    return imports & LEGACY_PRODUCERS


class RHModuleBoundaryTests(unittest.TestCase):
    def test_official_target_respects_pinned_legacy_imports(self):
        self.assertTrue(TARGET.is_file(), f"official RH target missing: {TARGET}")
        mismatches = mismatched_legacy_imports(TARGET.read_text(encoding="utf-8"))
        self.assertEqual(
            set(),
            mismatches,
            f"modern 'module' cannot import pinned legacy RH producers: {sorted(mismatches)}",
        )

    def test_catches_actual_regression_without_blocking_legacy_mode(self):
        legacy = (
            "import FormalConjecturesUtil\n"
            "import RHRestrictedWeilCriterionV13\n"
            "import RHSmallWindowCanonicalJoinV1\n"
        )
        self.assertEqual(set(), mismatched_legacy_imports(legacy))
        self.assertEqual(
            set(LEGACY_PRODUCERS),
            mismatched_legacy_imports("module\n\n" + legacy),
        )


if __name__ == "__main__":
    unittest.main()
