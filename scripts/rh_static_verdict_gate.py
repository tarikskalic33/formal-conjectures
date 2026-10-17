# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Reject pre-scripted negative *RH proof admission* verdicts in active code.

Historical exact-source archives are deliberately excluded: they are immutable
evidence and do not determine current proof admission.
Only a pinned Lean proof-term/type and axiom audit may emit a positive verdict.
"""
from __future__ import annotations

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ACTIVE_PREFIXES = (
    ".github/workflows/",
    "scripts/",
    "research/rh/assembly/",
    "research/rh/integration/",
    "research/rh/pattern_phase2/",
    "research/rh/producer_census_v2/",
)
ACTIVE_EXACT = {
    "research/rh/AEGIS_DIRICHLET_QUASI_BRIDGE_V1.json",
    "research/rh/AEGIS_DIRICHLET_QUASI_BRIDGE_V1.md",
}
EXTENSIONS = {".json", ".py", ".md", ".yml", ".yaml", ".sh", ".txt"}
# Count ONLY unconditional-RH admission fields; not real test assertions,
# historical research findings, or meaningful runtime negative test results.
KEY = (
    r"(?:rh_proven_unconditionally|rh_unconditionally_proven|"
    r"unconditional_rh_proven|rh_unconditional_claim|"
    r"unconditional_rh_claim|rh_proven|rh_unconditional)"
)
NEGATIVE_DEFAULT = re.compile(
    r"(?i)(?<![A-Za-z_])['\"]?" + KEY
    + r"['\"]?\s*[:=]\s*['\"]?(?:false|not_claimed|not_proven)\b"
)


def main() -> int:
    names = subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT)
    active = [
        name.decode("utf-8")
        for name in names.split(b"\0")
        if name and (
            name.decode("utf-8").startswith(ACTIVE_PREFIXES)
            or name.decode("utf-8") in ACTIVE_EXACT
        )
        and Path(name.decode("utf-8")).suffix in EXTENSIONS
    ]
    offenders: list[str] = []
    for path in active:
        lines = (ROOT / path).read_text(encoding="utf-8").splitlines()
        for number, line in enumerate(lines, 1):
            if NEGATIVE_DEFAULT.search(line):
                offenders.append(f"{path}:{number}: {line.strip()[:180]}")
    if offenders:
        print("RH_STATIC_VERDICT_AUDIT=FAIL")
        print("\n".join(offenders))
        return 1
    print(f"RH_STATIC_VERDICT_AUDIT=PASS scanned={len(active)} static_negative_defaults=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
