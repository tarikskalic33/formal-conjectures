"""Pinned, fail-closed local Lean closure replay for the M8 continuation.

The one-line correction overlay is explicit and content-addressed. This is not
an unchanged-source replay. No success receipt is emitted after any failed build.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

BASE = 'e279d5765b2dc0cb8b4ec4f62b8db96b4dc69121'
AEGIS = '2c3d041b633147ec97c7ef753aa9d157a47bb9f5'
MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'
PROVIDER = '35df682f3b709ffe5fbcfdd452dfa964bd622b87'
CORRECTION_OLD = 'eaec6e0ebd43e5b528b2eea0bb05a1ffa93cd51c'
CORRECTION_NEW = '5c39770f4cf027f785928a104c3025f4ba34207c'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
BOUNDARY = {'Mathlib','Batteries','Aesop','Qq','ProofWidgets','LeanSearchClient',
            'Plausible','ImportGraph','Cli','Lean','Init','Std','Lake',
            'Lc','Hadamard','FunctionsOfOneComplexVariable'}
TARGETS = ['AEGISOverlay.RHKreinExplicitCorrectionV1',
           'AEGISOverlay.RHKreinM8CertificateV1',
           'AEGISOverlay.RHKreinCorrectionTaylorBridgeV1',
           'AEGISOverlay.RHKreinSplineL1NormV1']

def sha256(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

def blob(b: bytes) -> str:
    return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()

def imports(text: str) -> list[str]:
    # A linear scanner, not a backtracking regex, handles nested Lean comments.
    out=[]; i=0; depth=0; string=False
    while i < len(text):
        pair=text[i:i+2]; ch=text[i]
        if depth:
            if pair=='/-': depth+=1; out.extend('  '); i+=2; continue
            if pair=='-/': depth-=1; out.extend('  '); i+=2; continue
            out.append('\n' if ch=='\n' else ' '); i+=1; continue
        if string:
            if ch=='\\': out.extend('  '); i+=2; continue
            if ch=='"': string=False
            out.append('\n' if ch=='\n' else ' '); i+=1; continue
        if pair=='/-': depth=1; out.extend('  '); i+=2; continue
        if pair=='--':
            j=text.find('\n',i)
            if j==-1: break
            out.extend(' '*(j-i)); i=j; continue
        if ch=='"': string=True; out.append(' '); i+=1; continue
        out.append(ch); i+=1
    result=[]
    for line in ''.join(out).splitlines():
        words=line.split()
        while words and words[0] in {'public','private','protected','meta'}: words.pop(0)
        if not words or words[0]!='import': continue
        for m in words[1:]:
            if not re.fullmatch(r'[A-Za-z0-9_.]+',m): raise ValueError('unsupported import '+m)
            result.append(m)
    return result

def audit(source: str, log: str) -> dict[str,list[str]]:
    names=re.findall(r'^#print axioms (\S+)\s*$',source,re.M)
    if not names or len(names)!=len(set(names)): raise ValueError('missing/duplicate probes')
    if re.search(r'sorryAx|\berror(?:\([^)]*\))?:',log): raise ValueError('compiler error or sorryAx')
    flat=' '.join(log.split())
    hits=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",flat)
    hits += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",flat)]
    if len(hits)!=len(names) or {n for n,_ in hits}!=set(names):
        raise ValueError('missing/duplicate/unexpected axiom outputs')
    result={}
    for n,a in hits:
        ax={x.strip() for x in a.split(',') if x.strip()}
        if not ax<=ALLOWED: raise ValueError('nonstandard axiom '+n+':'+str(ax))
        result[n]=sorted(ax)
    return result

def patched_correction(b: bytes) -> bytes:
    if blob(b)!=CORRECTION_OLD: raise ValueError('wrong baseline correction blob')
    old='  change HasCompactSupport (∑ i, f i)'.encode()
    new='  rw [← Finset.sum_fn]'.encode()
    if b.count(old)!=1: raise ValueError('patch is not unique')
    result=b.replace(old,new)
    if blob(result)!=CORRECTION_NEW: raise ValueError('wrong patched correction blob')
    return result

def cmd(args: list[str]) -> str:
    return subprocess.check_output(args,text=True).strip()

def main() -> None:
    root=Path.cwd(); evidence=root/'evidence-m8-kernel'
    evidence.mkdir(exist_ok=True)
    if cmd(['git','-C','.aegis','rev-parse','HEAD'])!=AEGIS: raise ValueError('AEGIS pin')
    if cmd(['git','-C','.li-provider','rev-parse','HEAD'])!=PROVIDER: raise ValueError('provider pin')
    if cmd(['git','-C','.lake/packages/mathlib','rev-parse','HEAD'])!=MATHLIB: raise ValueError('Mathlib pin')
    if Path('lean-toolchain').read_text().strip()!='leanprover/lean4:v4.33.1': raise ValueError('Lean pin')
    version=cmd(['lake','env','lean','--version'])
    sources={}; edges={}; order=[]; active=set()
    aegisroot=root/'.aegis/sovereign-omega-v2/formal/bridges/lean'
    def visit(m: str) -> None:
        if m.split('.')[0] in BOUNDARY: return
        if m in active: raise ValueError('import cycle '+m)
        if m in sources: return
        if '.' in m:
            p=root/(m.replace('.','/')+'.lean'); origin='candidate'
        elif (aegisroot/(m+'.lean')).is_file():
            p=aegisroot/(m+'.lean'); origin='aegis'
        elif (root/'AEGISOverlay'/(m+'.lean')).is_file():
            p=root/'AEGISOverlay'/(m+'.lean'); origin='candidate-alias'
        else: raise ValueError('unresolved local import '+m)
        if not p.is_file(): raise ValueError('missing local source '+str(p))
        original=p.read_bytes(); compiled=original
        if p.name=='RHKreinExplicitCorrectionV1.lean': compiled=patched_correction(original)
        ds=imports(compiled.decode()); active.add(m)
        for d in ds: visit(d)
        active.remove(m)
        edges[m]=ds; sources[m]=(p,origin,original,compiled); order.append(m)
    targets=list(TARGETS)
    extra='AEGISOverlay.RHKreinM8AnalyticV1'
    if (root/'AEGISOverlay/RHKreinM8AnalyticV1.lean').is_file(): targets.append(extra)
    for t in targets: visit(t)
    # Preserve the complete planned source binding even if compilation later fails.
    planned=[]
    for m in order:
        p,origin,original,compiled=sources[m]
        planned.append(dict(module=m,origin=origin,path=str(p.relative_to(root)),
                            source_blob=blob(original),compiled_blob=blob(compiled),
                            compiled_sha256=sha256(compiled),imports=edges[m]))
    (evidence/'source-manifest.json').write_text(json.dumps(planned,indent=2)+'\n')
    (evidence/'actual-head.txt').write_text(cmd(['git','rev-parse','HEAD'])+'\n')
    (evidence/'lean-version.txt').write_text(version+'\n')
    compiled_reports=[]; endpoints={}
    for m in order:
        p,origin,original,b=sources[m]
        dest=root/(m.replace('.','/')+'.lean'); dest.parent.mkdir(parents=True,exist_ok=True)
        if dest!=p and dest.exists() and dest.read_bytes()!=original:
            raise ValueError('source shadowing '+str(dest))
        dest.write_bytes(b)
        rel=m.replace('.','/')
        out=root/('.lake/build/lib/lean/'+rel+'.olean'); out.parent.mkdir(parents=True,exist_ok=True)
        out.unlink(missing_ok=True)
        logp=evidence/(m+'.log'); depp=evidence/(m+'.deps')
        print('COMPILE',m,blob(b),flush=True)
        with depp.open('w') as f:
            subprocess.run(['lake','env','lean','--deps',str(dest.relative_to(root))],stdout=f,stderr=subprocess.STDOUT,check=True)
        with logp.open('w') as f:
            r=subprocess.run(['lake','env','lean','-o',str(out.relative_to(root)),str(dest.relative_to(root))],stdout=f,stderr=subprocess.STDOUT)
        log=logp.read_text(); print(log,flush=True)
        if r.returncode or re.search(r'sorryAx|\berror(?:\([^)]*\))?:',log):
            raise RuntimeError('failed compilation '+m)
        if not out.is_file(): raise RuntimeError('missing olean '+m)
        if re.search(r'^#print axioms ',b.decode(),re.M):
            ax=audit(b.decode(),log)
            if set(ax)&set(endpoints): raise ValueError('duplicate endpoint across modules')
            endpoints.update(ax)
        saved=evidence/'sources'/(rel+'.lean'); saved.parent.mkdir(parents=True,exist_ok=True); saved.write_bytes(b)
        oleancopy=evidence/'oleans'/(rel+'.olean'); oleancopy.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(out,oleancopy)
        compiled_reports.append(dict(module=m,source_blob=blob(b),olean_sha256=sha256(out.read_bytes()),
                                     log_sha256=sha256(logp.read_bytes()),deps_sha256=sha256(depp.read_bytes())))
    (evidence/'axiom-audit.json').write_text(json.dumps(endpoints,indent=2,sort_keys=True)+'\n')
    (evidence/'compiled-manifest.json').write_text(json.dumps(compiled_reports,indent=2)+'\n')
    checks={str(p.relative_to(evidence)):sha256(p.read_bytes()) for p in sorted(evidence.rglob('*')) if p.is_file() and p.name != 'replay.log'}
    receipt=dict(schema='aegis.rh.m8-kernel-replay.v1',status='PASS_WITH_EXPLICIT_ONE_LINE_SOURCE_OVERLAY',
                 exact_verifier_head=cmd(['git','rev-parse','HEAD']),baseline=BASE,aegis=AEGIS,
                 mathlib=MATHLIB,provider=PROVIDER,lean_version=version,targets=targets,
                 compiled_local_modules=len(order),audited_endpoints=len(endpoints),
                 correction_original_blob=CORRECTION_OLD,correction_compiled_blob=CORRECTION_NEW,
                 proof_source_overlay=True,rh_proven=False,authority_effect='NONE',members_sha256=checks)
    (evidence/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print('PASS',len(order),'modules',len(endpoints),'endpoints',flush=True)

if __name__=='__main__': main()
