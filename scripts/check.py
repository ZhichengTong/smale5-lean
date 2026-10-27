"""Compile all authored Lean modules and audit every public theorem.
Requires pinned dependencies and their Mathlib cache: lake exe cache get.
No Archon installation or external model invocation is required.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, os, re, shutil, subprocess, sys, time
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--lake",default="lake")
parser.add_argument("--packages",type=Path,help="Optional Lake dependency overrides for offline verification")
parser.add_argument("--inside-lake",action="store_true",help=argparse.SUPPRESS)
a=parser.parse_args()
v=ROOT/"verification";v.mkdir(exist_ok=True)
base=[a.lake]+(["--packages="+str(a.packages.resolve())] if a.packages else [])
env=os.environ.copy();env["PYTHONIOENCODING"]="utf-8"
# Load Lake's pinned dependency environment once, then use Lean directly.
if not a.inside_lake:
 command=base+["env",sys.executable,str(Path(__file__).resolve()),"--inside-lake"]
 if a.packages:command += ["--packages",str(a.packages.resolve())]
 raise SystemExit(subprocess.run(command,cwd=ROOT,env=env).returncode)
lean=shutil.which("lean")
if not lean:raise RuntimeError("Lake environment did not expose Lean")
def run(command,log):
 p=subprocess.run(command,cwd=ROOT,env=env,capture_output=True,text=True,encoding="utf-8",errors="replace")
 (v/log).write_text(p.stdout+p.stderr,encoding="utf-8")
 if p.returncode:raise RuntimeError(f"exit {p.returncode}; see verification/{log}")
 return p.stdout+p.stderr
run([sys.executable,"scripts/generate_audit.py"],"audit-generation.log")
version=run([lean,"--version"],"lean-version.log").strip()
if "version 4.35.0," not in version:raise RuntimeError("Expected Lean 4.35.0: "+version)
seen=set();order=[]
def visit(module):
 if module in seen or (module!="Smale5" and not module.startswith("Smale5.")):return
 seen.add(module);p=ROOT/(module.replace(".","/")+".lean")
 for line in p.read_text(encoding="utf-8-sig").splitlines():
  match=re.match(r"^import\s+(.*)",line)
  if match:
   for dep in match[1].split("--")[0].split():visit(dep)
 order.append(module)
visit("Smale5");records=[]
for module in order:
 rel=module.replace(".","/")+".lean";output=ROOT/".lake/build/lib/lean"/(module.replace(".","/")+".olean")
 output.parent.mkdir(parents=True,exist_ok=True);start=time.monotonic()
 run([lean,"-o",str(output),rel],module.replace(".","-")+".compile.log")
 records.append({"module":module,"exit_code":0,"seconds":round(time.monotonic()-start,2)})
 print(module+": passed",flush=True)
log=run([lean,"verification/AxiomAudit.lean"],"axioms.log")
expected=json.loads((v/"audited-declarations.json").read_text(encoding="utf-8"));found={}
for name,axs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log):found[name]=[x.strip() for x in axs.split(",") if x.strip()]
for name in re.findall(r"'([^']+)' does not depend on any axioms",log):found[name]=[]
if set(found)!=set(expected):raise RuntimeError("Axiom audit declaration set differs")
allowed={"propext","Classical.choice","Quot.sound"}
if any(not set(xs)<=allowed for xs in found.values()):raise RuntimeError("Unexpected axiom in audited theorem")
paths=[ROOT/"Smale5.lean"]+sorted((ROOT/"Smale5").glob("*.lean"))
summary={"status":"passed","checked_at":datetime.now(timezone.utc).isoformat(),"lean_version":version,"authored_module_count":len(paths)-1,"audited_theorem_count":len(expected),"axioms_found":sorted({x for xs in found.values() for x in xs}),"whole_main_theorem_proved":False,"source_sha256":{p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},"dependency_mode":"Lake package overrides" if a.packages else "pinned Git dependencies"}
(v/"direct-compile-summary.json").write_text(json.dumps({"method":"lake env lean -o","exit_code":0,"modules":records},indent=2),encoding="utf-8")
(v/"check-summary.json").write_text(json.dumps(summary,indent=2),encoding="utf-8")
print(f"Verified {len(expected)} public theorems in {len(paths)-1} modules; standard logical axioms only.")
