"""Independent direct-profile oracle for the decorated-word Kannan frontend.

Finite fixtures are optimizer tests, never claims of complete physical k3 tables.
"""
from functools import lru_cache
from pathlib import Path
import json
import os
import random
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build/frontend'
FC = Path(os.environ.get('FC') or shutil.which('gfortran') or 'gfortran')
EXE = OUT / 'frontend.exe'


@lru_cache(None)
def leaf(N, w):
    r = N*w*w
    tau = (((100*r)**615).bit_length()-1+272)//200 if r else 1
    return r*(4+tau)


def reference(n, K, entries, share=True):
    upper = leaf(1, n)
    @lru_cache(None)
    def visit(w, N, selected):
        if N*5 >= upper:
            return upper
        result = min(upper, leaf(N, w))
        for e, (k,d,c,lo,hi) in enumerate(entries):
            chosen = selected[k-2]
            if chosen and chosen[0] != e:
                continue
            offsets = [chosen[1]] if chosen else range(lo,hi+1)
            for a in offsets:
                child = w//k+1+max(a,w%k+a-d)
                if child >= w:
                    continue
                own = 8*N*(child-1)*c
                if own >= result:
                    continue
                updated = list(selected)
                if share:
                    updated[k-2] = (e,a)
                result = min(result, own+visit(child,N*(2*k-1),tuple(updated)))
        return result
    return visit(n,1,((),)*(K-1))


def build():
    OUT.mkdir(parents=True, exist_ok=True)
    sources = ['sp_arithmetic','sp_rational','sp_lattice','sp_ilp','sp_oracle','sp_threshold','sp_outer']
    subprocess.run([str(FC),'-std=f95','-pedantic','-O0','-fcheck=all','-ftrapv',
                    *(['-static'] if sys.platform!='darwin' else []),'-J',str(OUT),'-I',str(OUT),
                    *[str(ROOT/'src'/f'{s}.f90') for s in sources],
                    str(ROOT/'tests/frontend_driver.f90'),'-o',str(EXE)],check=True,cwd=OUT)
    errors = OUT/'errors.exe'
    subprocess.run([str(FC),'-std=f95','-pedantic','-O0','-fcheck=all','-ftrapv',
                    *(['-static'] if sys.platform!='darwin' else []),'-J',str(OUT),'-I',str(OUT),
                    *[str(ROOT/'src'/f'{s}.f90') for s in sources],
                    str(ROOT/'tests/frontend_errors.f90'),'-o',str(errors)],check=True,cwd=OUT)
    subprocess.run([str(errors)],check=True)


def run(n,K,entries):
    text = f'{n} {K} {len(entries)}\n' + ''.join(' '.join(map(str,e))+'\n' for e in entries)
    p = subprocess.run([str(EXE)],input=text,text=True,capture_output=True,check=True)
    rows = [line.split() for line in p.stdout.splitlines()]
    result = list(map(int,rows[0][1:]))
    assert result[0] == 0, (text,p.stdout,p.stderr)
    path = [list(map(int,r[1:])) for r in rows[1:]]
    N,w,total,seen = 1,n,0,{}
    for k,c,a,b,child,e in path:
        ek,d,ec,lo,hi = entries[e-1]
        assert (k,c,a-b) == (ek,ec,d) and lo <= a <= hi
        assert seen.setdefault(k,(e,a)) == (e,a)
        assert child == w//k+1+max(a,w%k+b) and 1 <= child < w
        total += 8*N*(child-1)*c
        N *= 2*k-1
        w = child
    total += leaf(N,w)
    assert total == result[1] and len(path) == result[2]
    return result,path


def fixture(n):
    return [(2,0,4,2,n-2),(2,1,4,3,n-2),
            (3,0,19,5,5),(3,0,11,6,n-2),
            (3,1,19,5,5),(3,1,11,6,n-2),
            (3,2,19,6,6),(3,2,11,7,n-2)]


def main():
    build()
    cases = [(12,3,[]),(20,3,[(2,0,4,2,5)]),
             (32,3,[(2,1,4,3,7),(3,1,8,2,5)]),
             (45,4,[(2,1,6,3,8),(3,2,11,4,8),(4,1,12,2,8)])]
    rng = random.Random(20261016)
    for _ in range(24):
        n = rng.randrange(8,31)
        K = rng.randrange(2,5)
        entries = []
        for k in range(2,K+1):
            d = rng.randrange(k)
            lo = rng.randrange(d,d+4)
            hi = lo+rng.randrange(4)
            entries.append((k,d,rng.randrange(1,20),lo,hi))
        cases.append((n,K,entries))
    rows = []
    for n,K,entries in cases:
        expected = reference(n,K,entries)
        result,path = run(n,K,entries)
        assert result[1] == expected, (n,K,entries,expected,result,path)
        rows.append(dict(n=n,K=K,cost=result[1],counters=result[3:],path=path))
    assert sum(r['counters'][1] for r in rows) > 0
    print('PASS small catalogues:',len(cases),flush=True)
    for n in [40,50,60,79,100,125,160,206]:
        start = time.perf_counter()
        entries = fixture(n)
        expected = reference(n,3,entries)
        result,path = run(n,3,entries)
        assert result[1] == expected, (n,result,expected,path)
        rows.append(dict(n=n,K=3,cost=result[1],counters=result[3:],path=path))
        print('PASS shared fixture',n,expected,'seconds',round(time.perf_counter()-start,3),flush=True)
    assert rows[-1]['cost'] == 1715798
    unshared = reference(206,3,fixture(206),share=False)
    assert unshared == 1711150
    entries = [(2,1,21,3,3),(3,1,13,7,7),(4,1,45,5,5)]
    expected = reference(206,4,entries)
    result,path = run(206,4,entries)
    assert expected == result[1] == 1582354
    assert [p[0] for p in path] == [3,4]
    rows.append(dict(n=206,K=4,cost=result[1],counters=result[3:],path=path))
    print('PASS nonmonotone word (3,4):',result[1],flush=True)
    entries = [(2,1,21,3,12),(3,1,13,7,16),(4,1,45,5,14)]
    expected = reference(206,4,entries)
    result,path = run(206,4,entries)
    assert result[1] == expected == 1582354
    assert result[4] > 0 and result[5] > 0 and result[8] > 0
    rows.append(dict(n=206,K=4,cost=result[1],counters=result[3:],path=path))
    print('PASS widened intervals: ILP/HKZ/suffix',result[4],result[5],result[8],flush=True)
    (ROOT/'tests/frontend_report.json').write_text(json.dumps(dict(status='PASS',cases=rows,
        shared_cost=1715798,unshared_cost=unshared),indent=2)+'\n')


if __name__ == '__main__':
    main()
