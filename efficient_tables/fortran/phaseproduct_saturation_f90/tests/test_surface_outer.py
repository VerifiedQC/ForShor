"""Exact coupled-outer regressions; these restricted fixtures never populate T*(n,K)."""
import hashlib
import importlib.util
import json
import os
import shutil
from pathlib import Path
import subprocess
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'build/surface_outer'


class MixedArityOuter(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        OUT.mkdir(exist_ok=True)
        fc=Path(os.environ.get('FC') or shutil.which('gfortran') or 'gfortran')
        sources=[ROOT/'src'/f'{name}.f90' for name in ['sp_arithmetic','sp_rational','sp_lattice',
                 'sp_ilp','sp_oracle','sp_threshold','sp_outer']]
        driver=ROOT/'tests/frontend_driver.f90'
        cls.exe=OUT/'surface_outer.exe'
        command=[str(fc),'-std=f95','-O0','-g','-fcheck=all','-ftrapv',*(['-static'] if sys.platform!='darwin' else []),
                 '-J',str(OUT),'-I',str(OUT),*[str(p) for p in sources],str(driver),'-o',str(cls.exe)]
        subprocess.run(command,check=True,cwd=OUT)
        spec=importlib.util.spec_from_file_location('independent_catalogue_reference',ROOT/'tests/test_frontend.py')
        cls.oracle=importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.oracle)
        cls.records=[]
        cls.hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources+[driver]}

    @classmethod
    def tearDownClass(cls):
        (OUT/'REPORT.json').write_text(json.dumps(dict(scope='restricted-catalogue exact outer regression only',
             physical_surface_eligible=False,source_sha256=cls.hashes,cases=cls.records),indent=2)+'\n')

    def check_case(self,n,K,entries,expected,sequence):
        text=f'{n} {K} {len(entries)}\n'+''.join(' '.join(map(str,e))+'\n' for e in entries)
        run=subprocess.run([str(self.exe)],input=text,text=True,capture_output=True,check=True)
        lines=[line.split() for line in run.stdout.splitlines() if line.split()]
        values=list(map(int,lines[0][1:]))
        self.assertEqual(values[0],0)
        self.assertEqual(values[1],expected)
        self.assertEqual(self.oracle.reference(n,K,entries),expected)
        path=[list(map(int,line[1:])) for line in lines[1:]]
        self.assertEqual([row[0] for row in path],sequence)
        self.assertEqual(values[2],len(path))
        w,mult,total,shared=n,1,0,{}
        for k,c,a,b,child,entry in path:
            ek,d,ec,lo,hi=entries[entry-1]
            self.assertEqual((k,c,a-b),(ek,ec,d))
            self.assertTrue(lo<=a<=hi)
            self.assertEqual(shared.setdefault(k,(entry,a)),(entry,a))
            self.assertEqual(child,w//k+1+max(a,w%k+b))
            self.assertTrue(1<=child<w)
            total+=8*mult*(child-1)*c
            mult*=2*k-1
            w=child
        self.assertEqual(total+self.oracle.leaf(mult,w),expected)
        self.records.append(dict(n=n,K=K,cost=expected,arity_sequence=sequence,counters=values[3:],path=path))
        return values

    def test_decreasing_arity_n125(self):
        self.check_case(125,3,self.oracle.fixture(125),743949,[3,2])

    def test_decreasing_arity_n160(self):
        self.check_case(160,3,self.oracle.fixture(160),1121092,[3,2])

    def test_shared_repeated_arity_gap_n206(self):
        entries=self.oracle.fixture(206)
        self.check_case(206,3,entries,1715798,[3,3])
        self.assertEqual(self.oracle.reference(206,3,entries,share=False),1711150)

    def test_increasing_arity_executes_kannan_suffix_batches(self):
        values=self.check_case(206,4,[(2,1,21,3,12),(3,1,13,7,16),(4,1,45,5,14)],1582354,[3,4])
        self.assertGreater(values[4],0)  # ILP calls
        self.assertGreater(values[5],0)  # HKZ calls
        self.assertGreater(values[8],0)  # suffix assignments


if __name__=='__main__':
    unittest.main(verbosity=2)
