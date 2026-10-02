"""Reconstruct the original negative RH probe at the actual native target path.

The normal library retains the exact upstream conjecture baseline, which is
not proof evidence. Dedicated CI MUST prepare and compile this negative probe;
the existing producer compilation and axiom audits remain mandatory.
"""
from hashlib import sha1
from pathlib import Path
import sys

TARGET = Path("FormalConjectures/Millennium/RiemannHypothesis.lean")
BASELINE_BLOB = "c8d38bef385eb15661c3daf7449625b66b019b2a"
PROBE_BLOB = "910ff74bbd5ef701b094a8b8edc04e697363f2d6"


def git_blob(source: bytes) -> str:
    return sha1(b"blob " + str(len(source)).encode("ascii") + b"\0" + source).hexdigest()


def make_probe(source: bytes) -> bytes:
    if git_blob(source) != BASELINE_BLOB:
        raise ValueError("native baseline differs from pinned upstream bytes")
    replacements = (
        (b"import FormalConjecturesUtil\n", b"import FormalConjecturesUtil\nimport RHDeepMindTerminalV1\n"),
        (b"theorem riemannHypothesis : RiemannHypothesis := by\n  sorry\n",
         b"theorem riemannHypothesis : RiemannHypothesis := by\n  apply AEGIS.RHDeepMindTerminalV1.li_nonnegativity_closes_rh_v1\n"),
    )
    candidate = source
    for old, new in replacements:
        if candidate.count(old) != 1:
            raise ValueError("native probe replacement is not unique")
        candidate = candidate.replace(old, new, 1)
    if git_blob(candidate) != PROBE_BLOB:
        raise ValueError("prepared probe differs from original PR37 native target")
    return candidate


def main() -> int:
    root = Path(sys.argv[1]) if len(sys.argv) == 2 else Path.cwd()
    if len(sys.argv) > 2:
        raise ValueError("usage: prepare_native_probe.py [repository_root]")
    target = root / TARGET
    candidate = make_probe(target.read_bytes())
    target.write_bytes(candidate)
    print(f"NATIVE_BASELINE_BLOB={BASELINE_BLOB}")
    print(f"NATIVE_NEGATIVE_PROBE_BLOB={PROBE_BLOB}")
    print("BASELINE_IS_PROOF_EVIDENCE=FALSE\nRH_PROVEN=FALSE\nAUTHORITY_EFFECT=NONE")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
