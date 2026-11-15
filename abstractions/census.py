"""Kernel-time census of one paragraph's generated theorems (Proofs.lean with checkpoints).

    python3 abstractions/census.py <Proofs.lean> <NN> <outdir> [kinds...]

Writes one file per theorem (header + the paragraph's defs + that theorem), checks each alone
with `lake env lean`, and prints the seconds spent inside the Lean lock (procs' own timer:
wall time would include waiting for other agents' jobs)."""
import re, sys, time, subprocess
from pathlib import Path
sys.path.insert(0, 'studio'); import procs
src, nn, out = Path(sys.argv[1]).read_text().splitlines(), sys.argv[2], Path(sys.argv[3])
kinds = sys.argv[4:]
hdr = []
for l in src:
    if l.startswith('def chunk01'): break
    if not l.startswith('#guard'): hdr.append(l)
prev = f"{int(nn) - 1:02}"
defs = [l for l in src if re.match(rf'def (chunk{nn}|c{prev}|c{nn}|s{prev}|s{nn}|p{nn}uses|p{nn}staging|p{nn}tree|p{nn}judges) ', l)]
thms = [l for l in src if l.startswith(f'theorem p{nn}_') and ':= by decide' in l]
base = '\n'.join(hdr) + '\n' + '\n'.join(defs) + '\n'
ns = re.search(r'^namespace (\S+)', '\n'.join(hdr), re.M).group(1)
cases = [('baseline', 'theorem baseline : True := trivial')] + [(t.split()[1], t) for t in thms]
for name, t in cases:
    if kinds and name != 'baseline' and not any(k in name for k in kinds): continue
    f = out / f'{name}.lean'
    f.write_text(base + t + f'\nend {ns}\n')
    r = procs.run(['lake', 'env', 'lean', str(f)], timeout=1500)
    err = 'ok' if r.returncode == 0 else (r.stdout + r.stderr).strip().splitlines()[0][:100]
    print(f"{name:28} {r.secs:7.1f} s  {err}", flush=True)
