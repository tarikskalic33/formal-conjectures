#!/usr/bin/env python3
"""Restore only transitive source-identical and SHA256-verified Lean oleans.

All final targets and every theorem with an exact-head axiom log are recompiled.
No source change can inherit a proof from an earlier, different import closure.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_blob(path: Path) -> str:
    return subprocess.check_output(
        ["git", "hash-object", str(path)], text=True
    ).strip()


def verified_cache(cache: Path) -> dict[str, str]:
    if not cache.exists():
        return {}
    sources = cache / "source-blobs.txt"
    hashes = cache / "oleans.sha256"
    if not sources.is_file() or not hashes.is_file():
        raise RuntimeError("KREIN_CHECKPOINT_INCOMPLETE")
    blobs: dict[str, str] = {}
    for line in sources.read_text().splitlines():
        pair = line.split()
        if len(pair) != 2 or not re.fullmatch("[0-9a-f]{40}", pair[1]):
            raise RuntimeError("KREIN_CHECKPOINT_BAD_SOURCE_BLOB")
        module, blob = pair
        if module in blobs:
            raise RuntimeError("KREIN_CHECKPOINT_DUPLICATE_MODULE")
        blobs[module] = blob
    expected: set[str] = set()
    for line in hashes.read_text().splitlines():
        match = re.fullmatch(
            r"([0-9a-f]{64})\s+\*?(oleans/[A-Za-z0-9_.-]+\.olean)",
            line,
        )
        if match is None:
            raise RuntimeError("KREIN_CHECKPOINT_BAD_SHA256_MANIFEST")
        digest, rel = match.groups()
        if rel in expected:
            raise RuntimeError("KREIN_CHECKPOINT_DUPLICATE_OLEAN")
        file = cache / rel
        if not file.is_file() or sha256(file) != digest:
            raise RuntimeError("KREIN_CHECKPOINT_HASH_MISMATCH " + rel)
        expected.add(rel)
    actual = {
        x.relative_to(cache).as_posix()
        for x in (cache / "oleans").rglob("*.olean")
    }
    if not blobs or not expected or actual != expected:
        raise RuntimeError("KREIN_CHECKPOINT_FILE_SET_MISMATCH")
    return blobs


def imports(path: Path) -> set[str]:
    names: set[str] = set()
    for line in path.read_text().splitlines():
        line = line.strip()
        if line.startswith("import "):
            names.update(line[7:].split())
    return names


def audit_modules(workflow: Path, available: set[str]) -> set[str]:
    workflow_source = workflow.read_text()
    match = re.search(r"targets=(\[[^\n]+\])", workflow_source)
    if match is None:
        raise RuntimeError("MISSING_COFINAL_TARGETS")
    targets = ast.literal_eval(match.group(1))
    if not isinstance(targets, list) or not all(
        isinstance(x, str) for x in targets
    ):
        raise RuntimeError("INVALID_COFINAL_TARGETS")
    explicit_logs = {
        x for x in available
        if "compile-" + x.replace(".", "_") + ".log" in workflow_source
    }
    return explicit_logs | set(targets)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", default="evidence-cofinal/source-manifest.json")
    ap.add_argument("--cache", default=".rh-krein-full")
    ap.add_argument("--build", default=".lake/build/lib/lean")
    ap.add_argument("--output", default="evidence-cofinal/reused-modules.txt")
    ap.add_argument("--workflow", default=".github/workflows/rh-cofinal-actual-schur-v1.yml")
    args = ap.parse_args()
    rows = json.loads(Path(args.manifest).read_text())
    if not isinstance(rows, list) or not rows:
        raise RuntimeError("BAD_COFINAL_SOURCE_MANIFEST")
    names = [row["module"] for row in rows]
    if len(names) != len(set(names)):
        raise RuntimeError("DUPLICATE_SOURCE_MODULE")
    available = set(names)
    always_recompile = audit_modules(Path(args.workflow), available)
    cache = Path(args.cache)
    old_blobs = verified_cache(cache)
    trusted: dict[str, bool] = {}
    reused: list[str] = []
    receipts = []
    for row in rows:
        module = row["module"]
        src = Path(row["source"])
        if not src.is_file() or sha256(src) != row["sha256"]:
            raise RuntimeError("CURRENT_SOURCE_DRIFT " + module)
        local_deps = imports(src) & available
        if not local_deps <= trusted.keys():
            raise RuntimeError("NOT_TOPOLOGICAL " + module)
        old_olean = cache / "oleans" / (module + ".olean")
        source_identical = old_blobs.get(module) == source_blob(src)
        valid = (
            source_identical
            and all(trusted[dep] for dep in local_deps)
            and old_olean.is_file()
        )
        trusted[module] = valid
        skip = valid and module not in always_recompile
        if skip:
            dst = Path(args.build) / (module.replace(".", "/") + ".olean")
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(old_olean, dst)
            reused.append(module)
        receipts.append({
            "module": module, "source_closed": valid,
            "reused": skip, "axiom_audit_recompiled": module in always_recompile,
        })
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("".join(module + "\n" for module in reused))
    output.with_suffix(".json").write_text(json.dumps({
        "schema": "aegis.rh.source_bound_olean_reuse.v1",
        "cache_source_count": len(old_blobs),
        "verified_closure": sum(trusted.values()),
        "reused_count": len(reused),
        "audited_recompiled": len(always_recompile & available),
        "modules": receipts,
        "rh_proven_unconditionally": None,
        "rh_proof_admission_source": "Not assessed by source-bound olean cache restoration; require exact-head kernel theorem type and axiom audit",
    }, indent=2) + "\n")
    print(
        "EXACT_SOURCE_BOUND_OLEAN_REUSE",
        f"cache={len(old_blobs)} verified={sum(trusted.values())}",
        f"skipped={len(reused)} audited={len(always_recompile & available)}",
        flush=True,
    )


if __name__ == "__main__":
    main()
