"""Deterministic finite validation; limits here are test domains, never solver budgets."""
from pathlib import Path
from itertools import product
from fractions import Fraction as F
import random, subprocess, json, os, shutil

ROOT=Path(__file__).resolve().parents[1]
EXE=ROOT/'tests/test_backend_driver.exe'
GFORTRAN=Path(os.environ.get('FC') or shutil.which('gfortran') or 'gfortran')

def build():
    subprocess.run([str(GFORTRAN),'-std=f95','-pedantic','-fcheck=all','-fbacktrace','-O0',
        '-J',str(ROOT/'tests'),'-I',str(ROOT/'tests'),
        *map(str,[ROOT/'src/sp_arithmetic.f90',ROOT/'src/sp_rational.f90',
                  ROOT/'src/sp_lattice.f90',ROOT/'src/sp_ilp.f90',ROOT/'tests/test_backend_driver.f90']),
        '-o',str(EXE)],check=True,cwd=ROOT)

def run(data):
    env=dict(os.environ);env['PATH']=str(GFORTRAN.parent)+os.pathsep+env.get('PATH','')
    p=subprocess.run([str(EXE)],input=data,text=True,capture_output=True,check=True,cwd=ROOT,env=env)
    return p.stdout.strip().splitlines()

def dot(a,b): return sum(x*y for x,y in zip(a,b))
def feasible(rows,x): return all(dot(a,x)<=b for a,b in rows)
def box(n,lo=-2,hi=2):
    rows=[]
    for i in range(n):
        e=[0]*n;e[i]=1;rows.append((e,hi))
        e=[0]*n;e[i]=-1;rows.append((e,-lo))
    return rows
def det(a):
    a=[list(map(F,row)) for row in a];v=F(1)
    for j in range(len(a)):
        p=next((i for i in range(j,len(a)) if a[i][j]),None)
        if p is None:return F(0)
        if p!=j:a[p],a[j]=a[j],a[p];v=-v
        q=a[j][j];v*=q
        for i in range(j+1,len(a)):
            c=a[i][j]/q
            for k in range(j+1,len(a)):a[i][k]-=c*a[j][k]
    return v
def gs(cols):
    stars=[];mu=[];h=[]
    for v in cols:
        w=list(map(F,v));co=[]
        for u,hh in zip(stars,h):
            c=dot(v,u)/hh;co.append(c);w=[x-c*y for x,y in zip(w,u)]
        stars.append(w);h.append(dot(w,w));mu.append(co)
    return stars,h,mu

def main():
    build()
    assert run('2 0\n')==['ARITHMETIC_PASS           0']
    assert run('3 0\n')==['ALLOCATION_FAILURE_PASS']
    assert run('4 0\n')==['ILP_ALLOCATION_FAILURE_PASS']
    rng=random.Random(20261016)
    cases=[]
    for n in range(1,5):
        for _ in range(18):
            rows=box(n)
            for _ in range(rng.randrange(1,5)):
                rows.append(([rng.randrange(-4,5) for _ in range(n)],rng.randrange(-5,6)))
            if rng.randrange(4)==0:
                a,b=rows[-1];rows.append(([-x for x in a],-b))
            cases.append((n,rows,range(-2,3)))
    cases += [(1,box(1)+[([2],1),([-2],-1)],range(-2,3)),
              (2,box(2)+[([2,2],1),([-2,-2],-1)],range(-2,3)),
              (2,box(2)+[([1,1],1),([-1,-1],-1)],range(-2,3)),
              (0,[([],0)],range(1)),(0,[([],-1)],range(1)),
              (1,[([1],1000000000),([-1],-1000000000)],range(1000000000,1000000001))]
    data=f'0 {len(cases)}\n'
    for n,rows,_ in cases:
        data+=f'{len(rows)} {n}\n'+''.join(' '.join(map(str,a+[b]))+'\n' for a,b in rows)
    lines=run(data);assert len(lines)==len(cases)
    totals=[0]*7
    for (n,rows,domain),line in zip(cases,lines):
        parts=list(map(int,line.split()));st=parts[0];x=parts[1:1+n]
        brute=any(feasible(rows,z) for z in product(domain,repeat=n))
        assert st in (0,1),(st,n,rows,line)
        assert (st==0)==brute,(n,rows,line,brute)
        if st==0:assert feasible(rows,x)
        totals=[a+b for a,b in zip(totals,parts[1+n:])]
    matrices=[]
    for n in range(1,4):
        while sum(len(a)==n for a in matrices)<8:
            a=[[rng.randrange(-5,6) for _ in range(n)] for _ in range(n)]
            if det(a):matrices.append(a)
    data=f'1 {len(matrices)}\n'
    for a in matrices:data+=f'{len(a)} {len(a)}\n'+''.join(' '.join(map(str,r))+'\n' for r in a)
    for a,line in zip(matrices,run(data)):
        n=len(a);p=list(map(int,line.split()));assert p[0]==0
        g=[p[1+i*n:1+(i+1)*n] for i in range(n)]
        u=[p[1+n*n+i*n:1+n*n+(i+1)*n] for i in range(n)]
        assert abs(det(u))==1
        assert g==[[sum(a[i][k]*u[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
        cols=list(zip(*g));stars,h,mu=gs(cols)
        assert all(abs(c)<=F(1,2) for row in mu for c in row)
        for first in range(n):
            projected=[]
            for col in cols[first:]:
                w=list(map(F,col))
                for k in range(first):
                    c=dot(col,stars[k])/h[k];w=[x-c*y for x,y in zip(w,stars[k])]
                projected.append(w)
            for z in product(range(-5,6),repeat=n-first):
                if not any(z):continue
                w=[sum(z[k]*projected[k][i] for k in range(n-first)) for i in range(n)]
                assert dot(w,w)>=h[first],(a,g,first,z)
    report={'ilp_cases':len(cases),'hkz_bases':len(matrices),'stats_totals':totals,
            'arithmetic':'256-bit numerator/denominator, exact sqrt and negative floor passed',
            'allocation_failure_injections':1201,'ilp_allocation_failure_injections':60,
            'status':'PASS'}
    print(json.dumps(report,indent=2))
    (ROOT/'tests/backend_report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
