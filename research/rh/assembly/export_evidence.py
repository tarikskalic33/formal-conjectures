"""Generate source-bound partial proof receipts after actual Lean compilation."""
import datetime, hashlib, json, os, pathlib, re, shutil, subprocess

ROOT = pathlib.Path(".")
OUT = ROOT / "evidence-cofinal" / "assembly"
OUT.mkdir(parents=True, exist_ok=True)
META = ROOT / "research/rh/assembly"

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def git_sha(p=ROOT):
    return subprocess.check_output(["git", "-C", str(p), "rev-parse", "HEAD"], text=True).strip()

def write(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")

manifest = json.loads((ROOT / "evidence-cofinal/source-manifest.json").read_text())
head = git_sha()
modules = {}
for record in manifest:
    module = record["module"]
    source = pathlib.Path(record["source"])
    assert digest(source) == record["sha256"], module
    log = ROOT / "evidence-cofinal" / ("compile-" + module.replace(".", "_") + ".log")
    text = log.read_text()
    assert "sorryAx" not in text and "error:" not in text, module
    src = source.read_text()
    imports = re.findall(r"^import\s+(\S+)", src, re.M)
    if str(source).startswith(".aegis/"):
        provenance = {"repo": "Aegis-Omega/AEGIS-OMEGA", "sha": os.environ["AEGIS_SHA"]}
    elif module.startswith(("Lc.", "Hadamard.", "FunctionsOfOneComplexVariable.")):
        provenance = {"repo": "nicholasbulka/li-criterion-rh-equivalence-lean",
                      "sha": os.environ["LI_CRITERION_SHA"],
                      "adaptation_note": "Factorization has three source-locked API edits recorded in the workflow"}
    elif str(source).startswith(("AEGISOverlay/", "FormalConjecturesUtil/", "research/", "AegisRH/")):
        provenance = {"repo": "tarikskalic33/formal-conjectures", "sha": head}
    else:
        provenance = {"repo": "tarikskalic33/formal-conjectures",
                      "replay_sha": head, "historical_containing_commit": None,
                      "note": "Archived/blob-staged input; see archived-source-lock and archive digest"}
    probes = re.findall(r"^#print axioms (\S+)$", src, re.M)
    modules[module] = dict(record, imports=imports, provenance=provenance,
                          kernel_status="compiled_on_exact_head", printed_axiom_probes=probes)
    dest = OUT / "sources" / pathlib.Path(module.replace(".", "/") + ".lean")
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, dest)

terms = json.loads((OUT / "proof-terms.json").read_text())
rows = {r["identifier"]: r for r in terms["declarations"]}
missing = sorted({d for r in rows.values() for d in r["direct_dependencies"] if d not in rows})
adj = {n: set(r["direct_dependencies"]) & rows.keys() for n, r in rows.items()}
reverse = {n: set() for n in rows}
for n, deps in adj.items():
    for d in deps:
        reverse[d].add(n)

# Condense recursive type/constructor dependencies into a genuine DAG.
seen = set()
order = []
for start in rows:
    stack = [(start, False)]
    while stack:
        n, exiting = stack.pop()
        if exiting:
            order.append(n)
            continue
        if n in seen:
            continue
        seen.add(n)
        stack.append((n, True))
        stack.extend((d, False) for d in adj[n] if d not in seen)
component = {}
components = []
for start in reversed(order):
    if start in component:
        continue
    idx = len(components)
    members = []
    stack = [start]
    while stack:
        n = stack.pop()
        if n in component:
            continue
        component[n] = idx
        members.append(n)
        stack.extend(reverse[n] - component.keys())
    components.append(members)
dag = sorted({(component[n], component[d]) for n, deps in adj.items() for d in deps
              if component[n] != component[d]})
root_axioms = {root: rows[root]["axioms"] for root in terms["roots"]}
for root, axioms in root_axioms.items():
    assert set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}, (root, axioms)

for row in rows.values():
    module = row["module"]
    row["source"] = modules.get(module)
    if module.startswith("Mathlib"):
        row["external_pin"] = {"repo": "leanprover-community/mathlib4",
                               "sha": os.environ["MATHLIB_SHA"]}
    elif module.startswith(("Lean", "Init", "Std", "Lake")):
        row["external_pin"] = {"toolchain": os.environ["LEAN_TOOLCHAIN"]}
    row["kernel_status"] = "reachable_from_kernel_compiled_and_axiom_audited_roots"

graph = {"status": "selected_root_elaborated_type_and_available_proof_dependency_closure",
         "scope_limit": "Selected terminal/constructor/Gram route; not an all-history repository census",
         "exact_replay_sha": head, "modules": modules,
         "roots": terms["roots"], "root_axioms": root_axioms,
         "declarations": list(rows.values()), "missing_environment_constants": missing,
         "strongly_connected_components": components,
         "condensation_dag_edges": dag,
         "unresolved_producer": json.loads((META / "RH_BLOCKER.json").read_text())["obligation_type"]}
write("RH_PROOF_GRAPH.json", graph)

probe_file = ROOT / "RH_CLOSURE_PROBE.lean"
probe_file.write_text((META / "RH_CLOSURE_PROBE.txt").read_text())
probe = subprocess.run(["lake", "env", "lean", str(probe_file)],
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
(OUT / "RH_CLOSURE_PROBE.log").write_text(probe.stdout)
if probe.returncode == 0:
    raise RuntimeError("Broader-window probe unexpectedly compiled; inspect its actual type")
assert "type mismatch" in probe.stdout.lower(), probe.stdout
assert "LogWindowContainsV1" in probe.stdout, probe.stdout

blocker = json.loads((META / "RH_BLOCKER.json").read_text())
blocker["status"] = "CONSTRUCTOR_KERNEL_PASS; UNIVERSAL_CLOSURE_NOT_ACHIEVED"
blocker["attempts"][0]["status"] = "KERNEL_AND_STANDARD_AXIOM_AUDIT_PASS"
blocker["attempts"][1]["status"] = "ACTUAL_COMPILER_TYPE_MISMATCH"
blocker["observed_failing_test"] = {"command": "lake env lean RH_CLOSURE_PROBE.lean",
                                  "exit_code": probe.returncode, "log": probe.stdout}
write("RH_BLOCKER.json", blocker)

passport = json.loads((META / "RH_EVIDENCE_PASSPORT.json").read_text())
passport.update(verification_status="SELECTED_CONSTRUCTOR_KERNEL_AND_AXIOM_PASS; UNCONDITIONAL_RH_CLOSURE_NOT_ACHIEVED",
                exact_replay_sha=head, new_candidate_axioms=root_axioms,
                proof_graph_status=graph["status"],
                workflow_run_id=os.environ.get("GITHUB_RUN_ID"),
                workflow_job=os.environ.get("GITHUB_JOB"),
                recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                actual_lean_version=subprocess.check_output(["lean", "--version"], text=True).strip(),
                actual_mathlib_sha=git_sha(ROOT / ".lake/packages/mathlib"),
                source_hashes={m: r["sha256"] for m, r in modules.items()},
                proof_term_graph_sha256=digest(OUT / "proof-terms.json"),
                compiler_probe={"exit_code": probe.returncode, "log_sha256": digest(OUT / "RH_CLOSURE_PROBE.log")},
                certificate_hashes={"abel_archive": digest(ROOT / "research/rh/integration/AEGIS_PR63_ARCHIVED_ABEL_SOURCES_V6.tar.gz")})
write("RH_EVIDENCE_PASSPORT.json", passport)
shutil.copyfile(ROOT / "AEGISOverlay/AEGIS_RH_Unconditional.lean", OUT / "AEGIS_RH_Unconditional.lean")
shutil.copyfile(META / "RH_PROOFBOOK.md", OUT / "RH_PROOFBOOK.md")
shutil.copyfile(META / "RH_EXACT_HEAD_REPLAY.sh", OUT / "RH_EXACT_HEAD_REPLAY.sh")
shutil.copyfile(probe_file, OUT / "RH_CLOSURE_PROBE.lean")
print("ASSEMBLY_KERNEL_ROOTS", len(terms["roots"]))
print("ASSEMBLY_PROOF_GRAPH_DECLARATIONS", len(rows))
print("ASSEMBLY_PROBE_ACTUAL_TYPE_MISMATCH", probe.returncode)
print("UNCONDITIONAL_RH_CLOSURE_NOT_ACHIEVED")
