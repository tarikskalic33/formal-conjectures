# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Regression gate for the structural issues in DeepMind PR #7031's review.

This checks upstream-submission hygiene, NOT a proof of the Riemann Hypothesis.
A genuine RH proof still needs an unconditional Lake build and axiom audit.
"""

from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
RH_TARGET = ROOT / "FormalConjectures/Millennium/RiemannHypothesis.lean"
STANDARD_BUILD = ROOT / ".github/workflows/build-and-docs.yml"
REJECTED_ROOTS = ("AegisRH", "AEGISOverlay", "research/rh")
REJECTED_WORKFLOW_PREFIXES = ("aegis-", "rh-")
REJECTED_EXTERNAL_BUILD_MARKERS = (
    "Checkout pinned AEGIS RH base",
    "rh_pr63_import_prebuild.sh",
    "rh_pr63_proved_window_prebuild.sh",
    ".aegis-base/",
    ".port-source/",
    "Aegis-Omega/AEGIS-OMEGA",
    "nicholasbulka/li-criterion-rh-equivalence-lean",
)


def rh_proof_body(source: str) -> str:
    match = re.search(
        r"(?m)^theorem riemannHypothesis\s*:\s*RiemannHypothesis\s*:=\s*by\s*$",
        source,
    )
    if match is None:
        raise ValueError("official RH declaration was removed or changed")
    tail = source[match.end():]
    end = re.search(r"(?m)^end RiemannHypothesis\s*$", tail)
    if end is None:
        raise ValueError("official RH namespace ending is missing")
    return tail[:end.start()]


class Review7031SubmissionContract(unittest.TestCase):
    def test_official_theorem_is_still_native_to_formal_conjectures(self):
        source = RH_TARGET.read_text(encoding="utf-8")
        self.assertRegex(source, r"(?m)^module\s*$")
        self.assertIn("public import FormalConjecturesUtil", source)
        self.assertNotRegex(source, r"(?m)^\s*import\s+(?:RHRestrictedWeilCriterionV13|RHSmallWindowCanonicalJoinV1)\s*$")
        body = rh_proof_body(source)
        self.assertNotRegex(body, r"(?m)^\s*apply\s+AEGIS\.")
        # An open conjecture stays declared open. If a future unconditional
        # proof replaces 'sorry', review its category and axiom dependencies.
        if not re.search(r"\bsorry\b", body):
            before = source[:source.index("theorem riemannHypothesis")]
            self.assertNotRegex(before[-150:], r"\bcategory\s+research\s+open\b")

    def test_standard_lake_build_does_not_compile_external_repositories(self):
        workflow = STANDARD_BUILD.read_text(encoding="utf-8")
        for marker in REJECTED_EXTERNAL_BUILD_MARKERS:
            with self.subTest(marker=marker):
                self.assertNotIn(marker, workflow)
        self.assertIn("lake --wfail build", workflow)

    def test_upstream_candidate_is_not_a_research_tree_dump(self):
        for root in REJECTED_ROOTS:
            with self.subTest(root=root):
                self.assertFalse((ROOT / root).exists())
        self.assertFalse((ROOT / "FormalConjectures/Millennium/RHSnowflakeLog23.lean").exists())
        workflows = ROOT / ".github/workflows"
        for file in workflows.glob("*.yml"):
            self.assertFalse(
                file.name.startswith(REJECTED_WORKFLOW_PREFIXES),
                f"research-only workflow must not be included upstream: {file.name}",
            )

    def test_contract_recognizes_open_and_conditional_rh(self):
        open_source = (
            "namespace RiemannHypothesis\n"
            "theorem riemannHypothesis : RiemannHypothesis := by\n"
            "  sorry\n"
            "end RiemannHypothesis\n"
        )
        conditional = open_source.replace(
            "  sorry", "  apply AEGIS.UnprovedReduction"
        )
        self.assertIn("sorry", rh_proof_body(open_source))
        self.assertIn("apply AEGIS.", rh_proof_body(conditional))


if __name__ == "__main__":
    unittest.main()
