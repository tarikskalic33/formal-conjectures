#!/usr/bin/env python3
"""AEGIS Ω PR721 exact-source migration, with fail-closed identity and optional Lean replay.

Verified source SHA: fb983fdc84a6bbeec6960c0e0c54b9695beba837
No mutation of existing Lean modules, protected main, or mathlib pins.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "research/rh/aegis_pr721_fb983fd/source_manifest.json"
SOURCE_HEAD = "fb983fdc84a6bbeec6960c0e0c54b9695beba837"
SMOKE_TARGETS = ("RHNineBlockComparisonV1", "RHTenBlockComparisonV1", "RHElevenBlockComparisonV1")
ACTUAL_BRIDGE_TARGETS = ("RHTenBlockActualBridgeV1", "RHElevenBlockActualBridgeV1")
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def git_blob_hash(payload: bytes) -> str:
    header = b"blob " + str(len(payload)).encode("ascii") + b"\x00"
    return hashlib.sha1(header + payload).hexdigest()

def fail(reason: str) -> None:
    raise RuntimeError(reason)

def validate(out: Path) -> dict:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if manifest.get("source_head") != SOURCE_HEAD:
        fail("SOURCE_COMMIT_DRIFT")
    rows = manifest.get("files")
    if not isinstance(rows, list) or len(rows) != 183:
        fail("EXPECTED_183_SOURCES")
    names, paths, items = set(), set(), []
    stage = out / "source"
    if stage.exists() and any(stage.iterdir()):
        fail("NONEMPTY_STAGING_DIRECTORY")
    for row in rows:
        name, rel, expected = row["module"], Path(row["archive"]), row["sha"]
        if not re.fullmatch(r"[A-Za-z0-9_]+", name) or name in names:
            fail("DUPLICATE_OR_UNSAFE_MODULE " + name)
        if rel.is_absolute() or ".." in rel.parts or not str(rel).endswith(".lean.src"):
            fail("UNSAFE_ARCHIVE_PATH " + str(rel))
        if str(rel) in paths:
            fail("DUPLICATE_ARCHIVE_PATH " + str(rel))
        names.add(name)
        paths.add(str(rel))
        payload = (ROOT / rel).read_bytes()
        actual = git_blob_hash(payload)
        if actual != expected:
            fail("EXACT_BLOB_MISMATCH " + name + " " + actual)
        items.append({"module": name, "sha": expected, "archive": str(rel),
                      "size": len(payload), "bytes": payload})
    if len([x for x in items if x["archive"].startswith("research/rh/aegis_pr721_fb983fd/lean/")]) != 20:
        fail("EXPECTED_20_NEW_SOURCES")
    stage.mkdir(parents=True)
    for x in items:
        (stage / (x["module"] + ".lean")).write_bytes(x["bytes"])
        del x["bytes"]
    return {"source_head": SOURCE_HEAD, "source_subtree": manifest["source_subtree"],
            "fork_base_head": manifest["base_head"],
            "manifest_git_hash": git_blob_hash(MANIFEST.read_bytes()),
            "count": len(items), "new_blobs": 20,
            "source_identity": "PASS", "compiled": [], "kernel": "NOT_RUN",
            "files": items}

def compile_smoke(out: Path, receipt: dict) -> None:
    """Kernel-check exact SOS sources, then their strongest actual-Weil consumers.

    Stage imported comparison .olean files in the standard Lake library path;
    keeping outputs only in /tmp does NOT make Lean imports discoverable.
    Every generated .olean is hashed into the outside-worktree receipt.
    """
    olean_dir = ROOT / ".lake" / "build" / "lib" / "lean"
    olean_dir.mkdir(parents=True, exist_ok=True)
    receipt["actual_bridge"] = "NOT_RUN"
    # Lean 4.33 refuses sources outside the Lake project root. The temporary
    # source copies use the original SHA-verified bytes, never edited copies.
    with tempfile.TemporaryDirectory(prefix=".rh-pr721-smoke-", dir=ROOT) as work:
        local = Path(work)
        for mod in SMOKE_TARGETS + ACTUAL_BRIDGE_TARGETS:
            payload = (out / "source" / (mod + ".lean")).read_bytes()
            source = local / (mod + ".lean")
            source.write_bytes(payload)
            output = olean_dir / (mod + ".olean")
            # Delete cached output to make stale-module acceptance impossible.
            output.unlink(missing_ok=True)
            log = out / (mod + ".compile.log")
            with log.open("w", encoding="utf-8") as fh:
                p = subprocess.run(
                    ["lake", "env", "lean", "-o", str(output), str(source.relative_to(ROOT))],
                    cwd=ROOT, text=True, stdout=fh, stderr=subprocess.STDOUT)
            if p.returncode != 0 or not output.is_file():
                receipt["kernel"] = "FAILED"
                receipt["failed_module"] = mod
                fail("LEAN_COMPILE_FAILED " + mod)
            text = log.read_text(encoding="utf-8")
            if "sorryAx" in text or "error:" in text or "unsolved goals" in text:
                receipt["kernel"] = "FAILED"
                receipt["failed_module"] = mod
                fail("LEAN_AX_OR_ERROR " + mod)
            reports = re.findall(
                r"'[^']+' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
                text)
            expected = 4 if mod in SMOKE_TARGETS else 2
            if len(reports) != expected:
                receipt["kernel"] = "FAILED"
                receipt["failed_module"] = mod
                fail("INCOMPLETE_AXIOM_AUDIT " + mod)
            for axioms in reports:
                found = {a.strip() for a in axioms.split(",") if a.strip()}
                if not found.issubset(STANDARD_AXIOMS):
                    receipt["kernel"] = "FAILED"
                    receipt["failed_module"] = mod
                    fail("NONSTANDARD_AXIOMS " + mod + ": " + repr(found))
            receipt["compiled"].append({"module": mod, "printed_axioms": len(reports),
                                        "olean_sha256": hashlib.sha256(output.read_bytes()).hexdigest()})
    receipt["actual_bridge"] = "TEN_ELEVEN_ACTUAL_KERNEL_PASS"
    receipt["kernel"] = "THREE_SOS_MODULES_PASS"

def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", default="/tmp/aegis-pr721-source-receipt")
    parser.add_argument("--compile-smoke", action="store_true")
    args = parser.parse_args()
    out = Path(args.out).resolve()
    if out == ROOT or ROOT in out.parents:
        fail("STAGING_MUST_BE_OUTSIDE_FORK_WORKTREE")
    out.mkdir(parents=True, exist_ok=True)
    receipt = {"source_identity": "NOT_RUN", "kernel": "NOT_RUN"}
    try:
        receipt = validate(out)
        if args.compile_smoke:
            compile_smoke(out, receipt)
        returncode = 0
    except Exception as e:
        receipt["failure"] = str(e)
        if receipt.get("source_identity") == "NOT_RUN":
            receipt["source_identity"] = "FAILED"
        returncode = 1
    finally:
        (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
        print(json.dumps({k: v for k, v in receipt.items() if k != "files"}, indent=2),
              file=sys.stderr if returncode else sys.stdout)
    return returncode

if __name__ == "__main__":
    sys.exit(main())
