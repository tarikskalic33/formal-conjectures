# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Reject copyright-only local Lean source shadows before costly RH replay."""

from pathlib import Path
import unittest


PR606_LOCAL = Path(__file__).resolve().parents[1] / "AegisRH" / "PR606"


def is_header_only_lean(content: str) -> bool:
    """Recognize the license-only placeholder used by the local PR606 overlay."""
    text = content.lstrip("\ufeff \t\r\n")
    if not text.startswith("/-"):
        return not text.strip()
    end = text.find("-/", 2)
    if end < 0:
        return False  # malformed Lean source is caught by the compiler
    return not text[end + 2 :].strip()


class PR606LocalSourceTests(unittest.TestCase):
    def test_local_overlay_contains_no_header_only_sources(self):
        self.assertTrue(PR606_LOCAL.is_dir(), f"missing PR606 source directory: {PR606_LOCAL}")
        offenders = sorted(
            p.name
            for p in PR606_LOCAL.glob("*.lean")
            if is_header_only_lean(p.read_text(encoding="utf-8"))
        )
        self.assertEqual([], offenders, f"empty local Lean modules shadow real producers: {offenders}")

    def test_detects_placeholder_and_accepts_real_module(self):
        header = "/-\nCopyright 2026 Authors\n-/\n\n"
        self.assertTrue(is_header_only_lean(header))
        self.assertFalse(is_header_only_lean(header + "import Mathlib.Tactic\n"))
        self.assertFalse(is_header_only_lean(header + "namespace AEGIS\nend AEGIS\n"))


if __name__ == "__main__":
    unittest.main()
