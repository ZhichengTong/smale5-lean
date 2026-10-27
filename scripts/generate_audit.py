"""Generate #print axioms for every public theorem in the authored library."""
from pathlib import Path
import re,json
ROOT=Path(__file__).resolve().parents[1]
modules=sorted((ROOT/'Smale5').glob('*.lean'))
lines=['-- Generated audit. The main target is a proposition definition.']
lines += ['import Smale5.'+p.stem for p in modules]
lines += ['', '#check Smale5.FiveBodyFiniteness', '#print Smale5.FiveBodyFiniteness', '']
names=[]
def strip_comments(s):
    out=[];i=0;depth=0
    while i<len(s):
        if s.startswith('/-',i):depth+=1;i+=2;out.append('  ');continue
        if depth and s.startswith('-/',i):depth-=1;i+=2;out.append('  ');continue
        if not depth and s.startswith('--',i):
            j=s.find('\n',i)
            if j<0:break
            out.append('\n');i=j+1;continue
        out.append(s[i] if not depth or s[i]=='\n' else ' ');i+=1
    assert depth==0
    return ''.join(out)
for p in modules:
    stack=[]
    txt=strip_comments(p.read_text(encoding='utf-8-sig'))
    for line in txt.splitlines():
        match=re.fullmatch(r'(?:noncomputable\s+)?(namespace|section)(?:\s+([A-Za-z_][A-Za-z0-9_.]*))?\s*',line)
        if match:
            stack.append((match[1],match[2]));continue
        if re.fullmatch(r'end(?:\s+[A-Za-z_][A-Za-z0-9_.]*)?\s*',line):
            assert stack, (p,line)
            stack.pop();continue
        match=re.match(r'^(?:@\[[^\]]*\]\s*)*(?:protected\s+)?(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_.]*)',line)
        if match:
            namespace='.'.join(name for kind,name in stack if kind=='namespace')
            name=(namespace+'.' if namespace else '')+match[1]
            names.append(name);lines.append('#print axioms '+name)
    assert not stack,(p,stack)
assert len(names)==len(set(names))
(ROOT/'verification/AxiomAudit.lean').write_text('\n'.join(lines)+'\n',encoding='utf-8')
(ROOT/'verification/audited-declarations.json').write_text(json.dumps(names,indent=2),encoding='utf-8')
print(f'Axiom audit generated for {len(names)} public theorems in {len(modules)} modules.')
