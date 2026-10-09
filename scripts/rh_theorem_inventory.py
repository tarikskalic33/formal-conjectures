#!/usr/bin/env python3
# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Inventory Lean theorem-like declarations and imports across the checked-out corpus.

This is a source inventory, not a substitute for Lean elaboration or #print axioms.
Every record carries a source hash so CI can bind the inventory to exact files.
"""
from __future__ import annotations
import argparse, hashlib, json, re, sys
from pathlib import Path

SKIP_DIRS = {".git", ".lake", "node_modules", ".venv", "__pycache__"}
DECL = re.compile(r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial|meta|opaque)\s+)*(theorem|lemma|axiom|opaque|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_'.]*)")
NAMESPACE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*(?:--.*)?$")
END = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*(?:--.*)?$")
IMPORT = re.compile(r"^\s*(?:public\s+)?import\s+(.+?)\s*(?:--.*)?$")

def source_files(root: Path):
    for path in sorted(root.rglob("*.lean")):
        if not any(part in SKIP_DIRS for part in path.parts):
            yield path

def scan(path: Path, root: Path):
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    namespace_stack, imports, declarations = [], [], []
    in_block_comment = 0
    for line_no, original in enumerate(text.splitlines(), 1):
        line, out, i = original, [], 0
        while i < len(line):
            if in_block_comment:
                if line.startswith("/-", i):
                    in_block_comment += 1; i += 2
                elif line.startswith("-/", i):
                    in_block_comment -= 1; i += 2
                else: i += 1
            elif line.startswith("--", i): break
            elif line.startswith("/-", i):
                in_block_comment = 1; i += 2
            else:
                out.append(line[i]); i += 1
        code = "".join(out)
        if not code.strip(): continue
        m = IMPORT.match(code)
        if m:
            imports.extend(m.group(1).split()); continue
        m = NAMESPACE.match(code)
        if m:
            namespace_stack.append(m.group(1)); continue
        m = END.match(code)
        if m:
            if namespace_stack:
                target = m.group(1)
                if target:
                    while namespace_stack:
                        popped = namespace_stack.pop()
                        if popped.split(".")[-1] == target.split(".")[-1] or popped == target:
                            break
                else: namespace_stack.pop()
            continue
        m = DECL.match(code)
        if m:
            local = m.group(2)
            full = ".".join(namespace_stack + [local]) if namespace_stack else local
            declarations.append({"name": full, "kind": m.group(1), "line": str(line_no)})
    return {"path": path.relative_to(root).as_posix(),
            "sha256": hashlib.sha256(raw).hexdigest(),
            "imports": sorted(set(imports)), "declarations": declarations}

def main(argv=None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--output", type=Path, default=None)
    parser.add_argument("--require", action="append", default=[],
                        help="require a declaration name to occur (repeatable)")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    records = [scan(path, root) for path in source_files(root)]
    declarations = [{"name": d["name"], "kind": d["kind"], "line": int(d["line"]),
                     "path": record["path"], "source_sha256": record["sha256"]}
                    for record in records for d in record["declarations"]]
    names = {d["name"] for d in declarations}
    missing = sorted(set(args.require) - names)
    payload = {"schema_version": 1, "inventory_kind": "source_scan_not_compiler_proof",
               "root": ".", "lean_files": len(records), "declaration_count": len(declarations),
               "files": records, "declarations": declarations,
               "required_declarations_missing": missing}
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    else: sys.stdout.write(rendered)
    print(f"RH_THEOREM_INVENTORY_FILES={len(records)} DECLARATIONS={len(declarations)}", file=sys.stderr)
    if missing:
        print("RH_THEOREM_INVENTORY_MISSING=" + ",".join(missing), file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
