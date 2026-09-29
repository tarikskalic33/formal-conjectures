#!/usr/bin/env python3
"""Exact-source detecting-packet replay; no theorem producer or RH authority.

Traverse all imported source modules to the pinned Lean toolchain boundary.
Freshly compile the AEGIS/overlay closure; cached provider/Mathlib artifacts
are explicitly distinguished from freshly compiled local modules.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

AEGIS_SHA = 'b6ec25c76f0c92b1fd52371b46311e3762866ec7'
BASELINE_SHA = '2c3d041b633147ec97c7ef753aa9d157a47bb9f5'
OVERLAY_SHA = 'e0ebc9920a3688aaff9bbd24c9167f92734dcf96'
PROVIDER_SHA = '35df682f3b709ffe5fbcfdd452dfa964bd622b87'
MATHLIB_SHA = '0df444a360eaa60ab8c11dca51a86af692955474'
LEAN_TOOLCHAIN = 'leanprover/lean4:v4.33.1'
ROOT_BLOBS = {
    'AEGISOverlay.RHDetectingPacketV1': '6fcdae47dd965b546dd4757178892b80fa4a79f2',
    'RHFixedPacketFourPhaseV1': '995e8866eaddee12e8d38faf414d39734d7495bb',
    'RHDetectingPacketCriterionV1': 'a3f44c834df57f6e6849eb0fb52b2d7db8e18a40',
    'RHFixedPacketFrontierV1': 'fad22159cff7afb7d42e4c387a7f90e4174e5359',
    'RHFixedPacketDenseShiftV1': '33586b0f3a7f7cc764c78f370870924c6082d2ef',
}
SUPPLEMENT_BLOBS = {'WeilMomentAnnihilatorV1': '0fe118c9a62b240beb3469805d50fb3ec1dccb4e'}
BARE_OVERLAYS = set(ROOT_BLOBS) - {'AEGISOverlay.RHDetectingPacketV1'}
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN = {'RHKreinDigammaLowerBoundV1', 'RHKreinDigammaMonotonicityV1',
             'RHKreinExplicitCorrectionV1', 'RHKreinRationalCertificateV1',
             'RHGlobalGrowthBoundaryV1', 'RHPhiParetoControlV1'}
MOD = r"[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def admit_supplement(name: str, observed_blob: str, current_present: bool) -> None:
    need(not current_present, 'Supplement would shadow current source')
    need(name in SUPPLEMENT_BLOBS and SUPPLEMENT_BLOBS[name] == observed_blob,
         'Unapproved or changed baseline supplement: ' + name)


def blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def imports(text: str) -> list[str]:
    """Parse the import header, including nested comments and public/meta imports.

    Reject unsupported import syntax rather than silently truncating a graph.
    Stop at the first body command; import-like strings in bodies are irrelevant.
    """
    result: list[str] = []
    depth = 0
    prelude = False
    for raw in text.lstrip('\ufeff').splitlines():
        out = []
        i = 0
        while i < len(raw):
            pair = raw[i:i + 2]
            if pair == '/-':
                depth += 1
                i += 2
            elif depth and pair == '-/':
                depth -= 1
                i += 2
            elif depth:
                i += 1
            elif pair == '--':
                break
            else:
                out.append(raw[i])
                i += 1
        line = ''.join(out).strip()
        if not line:
            continue
        if line == 'module':
            continue
        if line == 'prelude':
            prelude = True
            continue
        match = re.fullmatch(r'(?:(?:public|meta)\s+)*import\s+(.+)', line)
        if match:
            parts = match.group(1).split()
            if parts and parts[0] == 'all':
                parts = parts[1:]
            need(bool(parts) and all(re.fullmatch(MOD, p) for p in parts),
                 'Unsupported import header: ' + line)
            result.extend(parts)
        else:
            need(not re.match(r'(?:(?:public|meta)\s+)*import\b', line),
                 'Malformed import header: ' + line)
            # A bare module continuation is legal Lean header syntax.
            if result and re.fullmatch(r'(?:' + MOD + r'\s*)+', line) and line[0].isupper():
                result.extend(line.split())
                continue
            break
    need(depth == 0, 'Unclosed header comment')
    return list(dict.fromkeys(([] if prelude else ['Init']) + result))


def closure(roots: list[str], dependencies) -> list[str]:
    seen, active, order = set(), set(), []
    def visit(name):
        if name in seen:
            return
        need(name not in active, 'Import cycle: ' + name)
        active.add(name)
        for dependency in dependencies(name):
            visit(dependency)
        active.remove(name)
        seen.add(name)
        order.append(name)
        need(len(order) <= 20000, 'Unexpectedly large import graph')
    for root in roots:
        visit(root)
    return order


def audit(log: str, expected: list[str]) -> dict[str, list[str]]:
    need(not re.search(r'sorryAx|\berror:|declaration uses .sorry', log),
         'Compiler error or sorry in audit log')
    found = {}
    pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, log, flags=re.S):
        name = match.group(1)
        need(name not in found, 'Duplicate axiom probe: ' + name)
        axioms = [x.strip() for x in (match.group(2) or '').split(',') if x.strip()]
        need(set(axioms) <= ALLOWED_AXIOMS, 'Nonstandard axioms: ' + repr(axioms))
        found[name] = axioms
    need(set(found) == set(expected), 'Missing/unexpected axiom probes')
    return found


def output(argv: list[str], cwd: Path | None = None) -> bytes:
    return subprocess.check_output(argv, cwd=cwd, stderr=subprocess.STDOUT)


def git(root: Path, *args: str) -> str:
    return output(['git', '-C', str(root), *args]).decode().strip()


def tracked(root: Path) -> dict[str, str]:
    answer = {}
    for record in output(['git', '-C', str(root), 'ls-tree', '-rz', 'HEAD']).split(b'\0'):
        if record:
            meta, path = record.decode().split('\t', 1)
            mode, kind, digest = meta.split()
            if kind == 'blob':
                answer[path] = digest
    return answer


def main() -> None:
    here = Path.cwd()
    work = here / '.provider'
    aegis = here / '.aegis'
    baseline = here / '.aegis-baseline'
    overlay = here / '.overlay'
    verifier = here / '.verifier'
    evidence = here / 'evidence-detecting'
    evidence.mkdir(exist_ok=True)
    for directory, pin in ((aegis, AEGIS_SHA), (baseline, BASELINE_SHA),
                           (overlay, OVERLAY_SHA), (work, PROVIDER_SHA)):
        need(git(directory, 'rev-parse', 'HEAD') == pin, 'Checkout mismatch: ' + str(directory))
    verifier_sha = git(verifier, 'rev-parse', 'HEAD')
    need(verifier_sha == os.environ['VERIFIER_SHA'], 'Verifier checkout mismatch')
    need((work / 'lean-toolchain').read_text().strip() == LEAN_TOOLCHAIN, 'Wrong Lean pin')
    lean_version = output(['lake', 'env', 'lean', '--version'], work).decode().strip()
    need('version 4.33.1,' in lean_version, 'Wrong executing Lean')
    manifest_bytes = (work / 'lake-manifest.json').read_bytes()
    lake_manifest = json.loads(manifest_bytes)
    provider_tree = tracked(work)
    aegis_tree, baseline_tree, overlay_tree = tracked(aegis), tracked(baseline), tracked(overlay)
    extract_path = 'sovereign-omega-v2/formal/receipts/rh-pr679-scope-clean-v1.json'
    extraction = json.loads((aegis / extract_path).read_bytes())
    need(extraction['rh_proven'] is False and extraction['authority_effect'] == 'NONE',
         'Extraction boundary mismatch')
    need(extraction['local_closure_count'] == len(extraction['local_sources']) == 91,
         'Extraction count mismatch')
    for item in extraction['local_sources']:
        need(blob((aegis / item['path']).read_bytes()) == item['blob_sha'],
             'Extraction blob mismatch: ' + item['path'])

    package_roots, package_pins = [], []
    for package in lake_manifest['packages']:
        need(package['type'] == 'git', 'Unpinned non-Git package')
        root = work / '.lake/packages' / package['name']
        pin = package['rev']
        need(git(root, 'rev-parse', 'HEAD') == pin, 'Package checkout mismatch')
        package_roots.append((root, package['url'], pin, tracked(root)))
        package_pins.append({'name': package['name'], 'url': package['url'], 'sha': pin})
    need(next(x['sha'] for x in package_pins if x['name'] == 'mathlib') == MATHLIB_SHA,
         'Wrong executing Mathlib')
    prefix = Path(output(['lake', 'env', 'lean', '--print-prefix'], work).decode().strip())
    nodes, paths = {}, {}
    code_root = 'sovereign-omega-v2/formal/bridges/lean/'
    patched = 'Hadamard/General/Factorization.lean'
    old = output(['git', '-C', str(work), 'show', 'HEAD:' + patched]).decode()
    need(blob(old.encode()) == '10d38a54580ff72d698a30be64fe1c3c44f862a2', 'Provider source drift')
    replacements = [
        ('eventually_nhdsWithin_of_forall fun w hw => ite_eq_right hw',
         'eventually_nhdsWithin_of_forall fun w hw => if_neg hw'),
        ('have hgz : g z = Q z := ite_eq_left rfl', 'have hgz : g z = Q z := by simp [g]'),
        ('rw [ite_eq_right heq, hQ_eq_div z (hz heq)]', 'rw [if_neg heq, hQ_eq_div z (hz heq)]'),
    ]
    for before, after in replacements:
        need(old.count(before) == 1, 'Compatibility anchor mismatch')
        old = old.replace(before, after)
    need((work / patched).read_text() == old, 'Unexpected provider compatibility change')

    def resolve(name):
        if name in nodes:
            return nodes[name]['imports']
        need(name.split('.')[-1] not in FORBIDDEN, 'Excluded failed producer reached: ' + name)
        rel = name.replace('.', '/') + '.lean'
        is_overlay = name.startswith('AEGISOverlay.') or name in BARE_OVERLAYS or \
            name == 'FormalConjectures.Millennium.RHSnowflakeLog23'
        if is_overlay:
            if name in BARE_OVERLAYS:
                rel = 'AEGISOverlay/' + name + '.lean'
            root, repo, pin, tree, kind = (overlay, 'tarikskalic33/formal-conjectures',
                                          OVERLAY_SHA, overlay_tree, 'overlay')
        elif '.' not in name and code_root + rel in aegis_tree:
            rel = code_root + rel
            root, repo, pin, tree, kind = (aegis, 'Aegis-Omega/AEGIS-OMEGA',
                                          AEGIS_SHA, aegis_tree, 'aegis')
        elif '.' not in name and code_root + rel in baseline_tree:
            rel = code_root + rel
            admit_supplement(name, baseline_tree[rel], rel in aegis_tree)
            root, repo, pin, tree, kind = (baseline, 'Aegis-Omega/AEGIS-OMEGA',
                                          BASELINE_SHA, baseline_tree, 'aegis-supplement')
        elif rel in provider_tree:
            root, repo, pin, tree, kind = (work, 'nicholasbulka/li-criterion-rh-equivalence-lean',
                                          PROVIDER_SHA, provider_tree, 'provider')
        else:
            matches = [(r, u, p, t) for r, u, p, t in package_roots if rel in t]
            need(len(matches) <= 1, 'Ambiguous package source: ' + name)
            if matches:
                root, repo, pin, tree = matches[0]
                kind = 'package'
            else:
                core = prefix / 'lib/lean' / (name.replace('.', '/') + '.olean')
                need(core.is_file(), 'Unresolved imported module: ' + name)
                nodes[name] = {'module': name, 'kind': 'toolchain-boundary', 'imports': [],
                               'toolchain': LEAN_TOOLCHAIN,
                               'olean_sha256': sha256(core.read_bytes())}
                return []
        need(rel in tree, 'Untracked source: ' + rel)
        path = root / rel
        data = path.read_bytes()
        actual = blob(data)
        need(actual == tree[rel] or (kind == 'provider' and rel == patched),
             'Source working-tree drift: ' + rel)
        if name in ROOT_BLOBS:
            need(actual == ROOT_BLOBS[name], 'Headline producer blob mismatch')
        record = {'module': name, 'kind': kind, 'repository': repo, 'commit': pin,
                  'path': rel, 'git_blob_sha': tree[rel], 'effective_git_blob_sha': actual,
                  'sha256': sha256(data), 'imports': imports(data.decode())}
        if kind == 'aegis':
            need(rel in baseline_tree and baseline_tree[rel] == actual,
                 'Transitive old/new AEGIS source mismatch: ' + rel)
            record['baseline_commit'] = BASELINE_SHA
            record['baseline_git_blob_sha'] = baseline_tree[rel]
        if kind == 'aegis-supplement':
            record['absent_from_aegis_sha'] = AEGIS_SHA
            record['reason'] = 'Required construction module omitted from PR698 proof payload'
        nodes[name], paths[name] = record, path
        return record['imports']

    order = closure(list(ROOT_BLOBS), resolve)
    local = [n for n in order if nodes[n]['kind'] in ('aegis', 'overlay', 'aegis-supplement')]
    overlay_names = [n for n in local if nodes[n]['kind'] == 'overlay']
    need(len(overlay_names) == 9, 'Unexpected detecting overlay closure')
    supplements = [nodes[n] for n in local if nodes[n]['kind'] == 'aegis-supplement']
    need({n['module'] for n in supplements} == set(SUPPLEMENT_BLOBS),
         'Supplement inventory differs from the inspected missing dependency')
    all_manifest = {'schema': 'aegis.rh.detecting-transitive-source-manifest.v1',
                    'authority_effect': 'NONE', 'rh_proven': False,
                    'verifier_sha': verifier_sha, 'aegis_sha': AEGIS_SHA,
                    'baseline_sha': BASELINE_SHA, 'overlay_sha': OVERLAY_SHA,
                    'provider_sha': PROVIDER_SHA, 'mathlib_sha': MATHLIB_SHA,
                    'lean_toolchain': LEAN_TOOLCHAIN, 'lean_version': lean_version,
                    'core_boundary': 'Pinned toolchain modules; not a rebuild of the Lean compiler',
                    'pure_pr698_rebind': False,
                    'pure_pr698_blocker': 'Required source missing from exact PR698 payload',
                    'explicit_baseline_supplements': supplements,
                    'packages': package_pins, 'roots': list(ROOT_BLOBS),
                    'nodes': [nodes[n] for n in order], 'fresh_compile_order': local}
    manifest_file = evidence / 'transitive-source-manifest.json'
    manifest_file.write_text(json.dumps(all_manifest, indent=2, sort_keys=True) + '\n')
    (evidence / 'provider-lake-manifest.json').write_bytes(manifest_bytes)
    (evidence / 'provider-compatibility.patch').write_bytes(output(['git', 'diff'], work))
    print('TRANSITIVE_SOURCE_NODES', len(nodes), 'FRESH_LOCAL_MODULES', len(local), flush=True)
    print('OVERLAY_MODULES', ','.join(overlay_names), flush=True)
    for name in local:
        dest = work / (name.replace('.', '/') + '.lean')
        need(not dest.exists(), 'Staging would overwrite source: ' + str(dest))
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(paths[name], dest)
        need(blob(dest.read_bytes()) == nodes[name]['effective_git_blob_sha'], 'Copy mismatch')

    def run_logged(argv, logpath):
        proc = subprocess.run(argv, cwd=work, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        logpath.write_bytes(proc.stdout)
        text = proc.stdout.decode()
        print(text, end='', flush=True)
        need(proc.returncode == 0, 'Execution failed: ' + ' '.join(argv))
        need(not re.search(r'sorryAx|\berror:|declaration uses .sorry', text), 'Invalid proof output')
        return text

    compiled = []
    for name in local:
        relative = name.replace('.', '/')
        olean = work / '.lake/build/lib/lean' / (relative + '.olean')
        olean.parent.mkdir(parents=True, exist_ok=True)
        need(not olean.exists(), 'Stale local olean present: ' + name)
        log = evidence / (name + '.log')
        print('COMPILE', name, flush=True)
        run_logged(['lake', 'env', 'lean', '-o', str(olean), relative + '.lean'], log)
        dep_log = evidence / (name + '.deps.txt')
        run_logged(['lake', 'env', 'lean', '--deps', relative + '.lean'], dep_log)
        compiled.append({'module': name, 'source_sha256': nodes[name]['sha256'],
                         'olean_sha256': sha256(olean.read_bytes()),
                         'log_sha256': sha256(log.read_bytes()),
                         'compiler_deps_sha256': sha256(dep_log.read_bytes())})
    expected = []
    for name in ROOT_BLOBS:
        expected.extend(re.findall(r'^#print axioms\s+([A-Za-z0-9_.]+)',
                                   paths[name].read_text(), flags=re.M))
    need(len(expected) == len(set(expected)) == 23, 'Wrong headline endpoint set')
    probes = '\n'.join('import ' + n for n in ROOT_BLOBS) + '\n'
    probes += '\n'.join('#print axioms ' + n for n in expected) + '\n'
    probe_file = work / 'DetectingRebindAudit.lean'
    probe_file.write_text(probes)
    log = run_logged(['lake', 'env', 'lean', str(probe_file)], evidence / 'headline-axioms.log')
    ax = audit(log, expected)
    (evidence / 'headline-axioms.json').write_text(json.dumps(ax, indent=2, sort_keys=True) + '\n')
    (evidence / 'compiled-modules.json').write_text(json.dumps(compiled, indent=2) + '\n')
    receipt = {'schema': 'aegis.rh.detecting-pr698-replay.v1',
               'status': 'PASS_WITH_EXPLICIT_BASELINE_SUPPLEMENT',
               'pure_pr698_rebind': False,
               'pure_pr698_status': 'BLOCKED_MISSING_SOURCE',
               'explicit_baseline_supplements': supplements,
               'authority_effect': 'NONE', 'rh_proven': False, 'verifier_sha': verifier_sha,
               'aegis_sha': AEGIS_SHA, 'baseline_sha': BASELINE_SHA, 'overlay_sha': OVERLAY_SHA,
               'provider_sha': PROVIDER_SHA, 'mathlib_sha': MATHLIB_SHA,
               'lean_toolchain': LEAN_TOOLCHAIN, 'local_module_count': len(local),
               'aegis_module_count': sum(nodes[n]['kind'] == 'aegis' for n in local),
               'overlay_module_count': len(overlay_names), 'endpoint_count': len(ax),
               'transitive_source_node_count': len(nodes), 'shared_aegis_baseline_all_byte_identical': True,
               'transitive_manifest_sha256': sha256(manifest_file.read_bytes()),
               'axiom_log_sha256': sha256((evidence / 'headline-axioms.log').read_bytes()),
               'compiled_modules_sha256': sha256((evidence / 'compiled-modules.json').read_bytes()),
               'run_id': os.environ.get('GITHUB_RUN_ID'), 'run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT'),
               'remaining_obligation': 'AEGIS.RHFixedPacketDenseShiftV1.DenseFixedPacketSign',
               'limitations': ['Equivalence/reduction only; the residual is not proved.',
                               'NOT a standalone PR698 replay: one explicitly pinned baseline module is required.',
                               'Provider/Mathlib were built or loaded through pinned dependencies.',
                               'The Lean compiler and its bundled modules are the trusted toolchain boundary.']}
    (evidence / 'replay-receipt.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    print(json.dumps(receipt, indent=2), flush=True)


if __name__ == '__main__':
    main()
