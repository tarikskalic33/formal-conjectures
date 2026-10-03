"""Prepare reviewed Git objects only; NEVER move a PR branch or assert RH.

This temporary-branch utility preserves the production workflow except for
source-local compatibility repairs and explicit PR-head checkout binding.
"""
from __future__ import annotations

import base64
import difflib
import hashlib
import json
import os
import re
import sys
import tempfile
import textwrap
import urllib.parse
import urllib.request
from pathlib import Path

REPO = "tarikskalic33/formal-conjectures"
WORKFLOW = ".github/workflows/aegis-rh-fork-replay-v1.yml"
SOURCE_DIR = "sovereign-omega-v2/formal/bridges/lean/"
OLD_AEGIS = "1bdc7abc06d44f39f1379503caabf7e66a708956"
NEW_AEGIS = "589adf0480bd4d7c12c9828027ea6228398377f4"
TARGETS = (
    (1, "proof/riemann-hypothesis-aegis-v1", "43b5864333132f942fafce685236beefeb76c08e", "555d8306cc697d5b2aa9fd5bc5ac8296b9190039", OLD_AEGIS),
    (2, "evidence/rh-v13-kernel-replay-856870f5", "0370e4fb6e07842443b88248efb344f7826505a8", "555d8306cc697d5b2aa9fd5bc5ac8296b9190039", OLD_AEGIS),
    (3, "evidence/rh-v13-kernel-replay-589adf", "4153c57a2338c56c1aa5b3a9b20636f2fc60732f", "3c556ad98b8c6af1e5f67e5c507c7fa1321490e8", NEW_AEGIS),
)
BAD_GAMMA = "              WeilPairedMellinProfileV5 f c t) :=\n    hplus.const_mul (1 / 2 : ℂ)"
GOOD_GAMMA = "              WeilPairedMellinProfileV5 f c t)) :=\n    hplus.const_mul (1 / 2 : ℂ)"


def api(path: str, data: dict | None = None):
    # Deliberately restrict writes to immutable Git objects, not refs or PRs.
    if data is not None and not re.fullmatch(rf"repos/{REPO}/git/(blobs|trees|commits)", path):
        raise ValueError(f"Forbidden write endpoint: {path}")
    request = urllib.request.Request(
        "https://api.github.com/" + path,
        data=None if data is None else json.dumps(data).encode(),
        headers={"Authorization": "Bearer " + os.environ["GH_TOKEN"],
                 "Accept": "application/vnd.github+json",
                 "X-GitHub-Api-Version": "2022-11-28",
                 "Content-Type": "application/json"},
        method="GET" if data is None else "POST",
    )
    with urllib.request.urlopen(request, timeout=60) as response:
        return json.load(response)


def read_file(repo: str, path: str, ref: str) -> tuple[str, str]:
    item = api(f"repos/{repo}/contents/{path}?ref={urllib.parse.quote(ref, safe='')}")
    raw = base64.b64decode(item["content"])
    sha = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
    if sha != item["sha"]:
        raise ValueError("Git blob binding mismatch")
    return raw.decode("utf-8"), sha


def replace_once(text: str, old: str, new: str) -> str:
    if text.count(old) != 1:
        raise ValueError(f"Expected one exact patch anchor: {old[:90]!r}")
    return text.replace(old, new, 1)


def indent_literal(text: str, start: str, end: str) -> str:
    if text.count(start) != 1 or text.count(end) != 1:
        raise ValueError("Expected one exact nested-proof literal")
    i = text.index(start)
    j = text.index(end, i) + len(end)
    lines = text[i:j].splitlines(keepends=True)
    if len(lines) < 2:
        raise ValueError("Expected a multiline proof literal")
    return text[:i] + lines[0] + "".join("  " + line for line in lines[1:]) + text[j:]


def render_moment(workflow: str, source: str) -> str:
    start = workflow.index("      - name: Apply moment-zero detection Lean 4.33 compatibility patch\n")
    end = workflow.index("\n      - name:", start + 1)
    step = workflow[start:end]
    begin = step.index("          python3 - \"$MOM\" <<'PY'\n") + len("          python3 - \"$MOM\" <<'PY'\n")
    finish = step.index("\n          PY", begin)
    code = textwrap.dedent(step[begin:finish])
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "WeilMomentZeroDetectionV10.lean"
        path.write_text(source, encoding="utf-8")
        argv = sys.argv
        try:
            sys.argv = ["source-bound-moment-regression", str(path)]
            exec(compile(code, "production-moment-patch", "exec"), {"__name__": "__main__"})
        finally:
            sys.argv = argv
        return path.read_text(encoding="utf-8")


def signatures(source: str) -> list[str]:
    return re.findall(r"(?m)^(?:(?:private|protected|noncomputable) )*(?:theorem|lemma|def|abbrev)\b[\s\S]*?:=", source)


def fixed_workflow(before: str, gamma: bool) -> str:
    text = indent_literal(before, '          new = """  have hmult : analyticOrderNatAt riemannZeta rho.1 ≠ 0 := by\n', 'exact hOrderNeZero hcast"""')
    text = indent_literal(text, '          new = """  · apply mul_ne_zero h1\n', "simpa using hc'\"\"\"")
    text = replace_once(text, "env:\n  AEGIS_SHA:", "env:\n  RH_PROVEN: 'false'\n  FORK_SHA: ${{ github.event.pull_request.head.sha || github.sha }}\n  AEGIS_SHA:")
    text = replace_once(text,
        "      - name: Checkout fork exact head\n        uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262\n        with:\n          fetch-depth: 1\n",
        "      - name: Checkout fork exact head\n        uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262\n        with:\n          ref: ${{ env.FORK_SHA }}\n          fetch-depth: 1\n")
    text = replace_once(text,
        "          test \"$(git -C .aegis rev-parse HEAD)\" = \"$AEGIS_SHA\"\n",
        "          test \"$(git rev-parse HEAD)\" = \"$FORK_SHA\"\n          echo \"FORK_EXACT_HEAD=$FORK_SHA RH_PROVEN=false\"\n          test \"$(git -C .aegis rev-parse HEAD)\" = \"$AEGIS_SHA\"\n")
    if gamma:
        code = '''from pathlib import Path
import hashlib
p = Path(".aegis/sovereign-omega-v2/formal/bridges/lean/WeilFixedLineCompletedGammaV10.lean")
raw = p.read_bytes()
assert hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\\0" + raw).hexdigest() == "f9caa990fd02d2bc75a788e42f131fb2b1e57200"
s = raw.decode("utf-8")
old = "              WeilPairedMellinProfileV5 f c t) :=\\n    hplus.const_mul (1 / 2 : ℂ)"
new = "              WeilPairedMellinProfileV5 f c t)) :=\\n    hplus.const_mul (1 / 2 : ℂ)"
assert s.count(old) == 2, "Completed-gamma preimage drift"
p.write_text(s.replace(old, new), encoding="utf-8")
print("COMPLETED_GAMMA_LOCAL_BINDER_REPAIR=APPLIED RH_PROVEN=false")
'''
        addition = "      - name: Repair completed-gamma local binder syntax\n        shell: bash\n        run: |\n          set -euo pipefail\n          python3 - <<'PY'\n" + textwrap.indent(code, "          ") + "          PY\n\n"
        text = replace_once(text, "      - name: Fetch exact Mathlib cache\n", addition + "      - name: Fetch exact Mathlib cache\n")
    return text


def main() -> None:
    if os.environ.get("GITHUB_REPOSITORY") != REPO:
        raise ValueError("Wrong repository")
    results = []
    shared_blobs: dict[str, str] = {}
    for number, branch, head, workflow_blob, source_pin in TARGETS:
        pr = api(f"repos/{REPO}/pulls/{number}")
        if not (pr["state"] == "open" and pr["draft"] and pr["head"]["sha"] == head and pr["head"]["ref"] == branch):
            raise ValueError(f"PR #{number} state moved; no target ref will be written")
        before, sha = read_file(REPO, WORKFLOW, head)
        if sha != workflow_blob or f"  AEGIS_SHA: {source_pin}\n" not in before:
            raise ValueError("Workflow or upstream pin drift")
        after = fixed_workflow(before, source_pin == OLD_AEGIS)
        moment, moment_blob = read_file("Aegis-Omega/AEGIS-OMEGA", SOURCE_DIR + "WeilMomentZeroDetectionV10.lean", source_pin)
        broken = render_moment(before, moment)
        repaired = render_moment(after, moment)
        hmult = "  have hmult : analyticOrderNatAt riemannZeta rho.1 ≠ 0 := by\n"
        assert hmult + "  have hstrip :=" in broken
        assert "  · apply mul_ne_zero h1\n  intro hc" in broken
        assert hmult + "    have hstrip :=" in repaired
        assert "  · apply mul_ne_zero h1\n    intro hc" in repaired
        assert signatures(moment) == signatures(broken) == signatures(repaired)
        assert re.sub(r"\s+", "", broken) == re.sub(r"\s+", "", repaired)
        assert not re.search(r"\b(?:sorry|admit|axiom)\b", repaired)
        if source_pin == OLD_AEGIS:
            gamma, gamma_blob = read_file("Aegis-Omega/AEGIS-OMEGA", SOURCE_DIR + "WeilFixedLineCompletedGammaV10.lean", source_pin)
            assert gamma_blob == "f9caa990fd02d2bc75a788e42f131fb2b1e57200"
            assert gamma.count(BAD_GAMMA) == 2
            gamma_fixed = gamma.replace(BAD_GAMMA, GOOD_GAMMA)
            assert gamma_fixed.count(BAD_GAMMA) == 0
            assert gamma_fixed.count(GOOD_GAMMA) == 2
            assert signatures(gamma) == signatures(gamma_fixed)
        assert "permissions:\n  contents: read\n" in after
        assert after.count("      - name:") == before.count("      - name:") + int(source_pin == OLD_AEGIS)
        for step in ("Compile exact AEGIS RH closure", "Audit load-bearing axioms"):
            assert step in before and step in after
        print(f"=== VERIFIED WORKFLOW DIFF PR {number} ===", flush=True)
        print("".join(difflib.unified_diff(before.splitlines(True), after.splitlines(True), fromfile=WORKFLOW, tofile=WORKFLOW)), flush=True)
        digest = hashlib.sha256(after.encode()).hexdigest()
        blob = shared_blobs.get(digest)
        if blob is None:
            blob = api(f"repos/{REPO}/git/blobs", {"content": after, "encoding": "utf-8"})["sha"]
            shared_blobs[digest] = blob
        base = api(f"repos/{REPO}/git/commits/{head}")
        tree = api(f"repos/{REPO}/git/trees", {"base_tree": base["tree"]["sha"], "tree": [{"path": WORKFLOW, "mode": "100644", "type": "blob", "sha": blob}]})
        commit = api(f"repos/{REPO}/git/commits", {"message": "fix(rh): repair replay local binders and nested proof indentation\n\nPreserve theorem signatures, upstream/toolchain pins and all replay gates.\nBind checkout to the actual PR head. RH_PROVEN=false; no merge.", "tree": tree["sha"], "parents": [head]})
        result = {"pr": number, "branch": branch, "head_before": head, "candidate_commit": commit["sha"], "workflow_blob_before": sha, "workflow_blob_after": blob, "source_pin": source_pin, "moment_source_blob": moment_blob, "python_source_regressions": "PASS", "lean_replay": "NOT_RUN", "RH_PROVEN": False, "target_refs_modified": False}
        results.append(result)
        print("CANDIDATE " + json.dumps(result, sort_keys=True), flush=True)
    assert results[0]["workflow_blob_after"] == results[1]["workflow_blob_after"]
    Path("compat-candidates.json").write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print("PREPARATION_COMPLETE NO_TARGET_REFS_WRITTEN RH_PROVEN=false", flush=True)


if __name__ == "__main__":
    main()
