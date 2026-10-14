#!/usr/bin/env bash
set -euo pipefail
# Usage: RH_EXACT_HEAD_REPLAY.sh EXACT_SHA NEW_WORK_DIRECTORY
SOURCE_SHA="${1:?supply the exact 40-character source SHA}"
WORK_DIR="${2:?supply a fresh work directory}"
[[ "$SOURCE_SHA" =~ ^[0-9a-f]{40}$ ]]
test ! -e "$WORK_DIR"
git clone https://github.com/tarikskalic33/formal-conjectures.git "$WORK_DIR"
git -C "$WORK_DIR" checkout --detach "$SOURCE_SHA"
test "$(git -C "$WORK_DIR" rev-parse HEAD)" = "$SOURCE_SHA"
cd "$WORK_DIR"
git clone https://github.com/Aegis-Omega/AEGIS-OMEGA.git .aegis
git -C .aegis checkout --detach 2c3d041b633147ec97c7ef753aa9d157a47bb9f5
git clone https://github.com/nicholasbulka/li-criterion-rh-equivalence-lean.git .li-provider
git -C .li-provider checkout --detach 35df682f3b709ffe5fbcfdd452dfa964bd622b87
python3 - <<'PY'
import os,pathlib,re,subprocess
text=pathlib.Path('.github/workflows/rh-cofinal-actual-schur-v1.yml').read_text()
env=os.environ.copy()
top=text.split('\nenv:\n',1)[1].split('\njobs:',1)[0]
for key,value in re.findall(r'^  (\w+): (.+)$',top,re.M):env[key]=value
env['PATH']=str(pathlib.Path.home()/'.elan/bin')+':'+env['PATH']
env['GITHUB_PATH']=str(pathlib.Path('.replay-github-path').resolve())
env.setdefault('GITHUB_RUN_ID','local-replay')
env.setdefault('GITHUB_JOB','local-replay')
blocks=[];name='';collect=False;code=[]
for line in text.splitlines()+['END']:
    if collect:
        if line.startswith('          '):code.append(line[10:]);continue
        if not line:code.append('');continue
        blocks.append((name,'\n'.join(code)));code=[];collect=False
    if line.startswith('      - name: '):name=line[14:]
    if line=='        run: |':collect=True
record=next(code for name,code in blocks if name=='Record exact-head receipt')
try:
    for name,code in blocks:
        if name=='Record exact-head receipt':continue
        if not env.get('GH_TOKEN'):
            code='\n'.join(line for line in code.splitlines() if '-H "Authorization: Bearer $GH_TOKEN"' not in line)
        print('REPLAY',name,flush=True)
        subprocess.run(['bash','-c',code],env=env,check=True)
finally:
    subprocess.run(['bash','-c',record],env=env,check=True)
PY
echo 'Replay source/axiom receipt written. No unconditional RH success is inferred.'
