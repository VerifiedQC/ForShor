"""Independent exact replay, costs and small complete policy enumeration."""
from functools import lru_cache
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
EXE = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else ROOT / 'build/debug/phaseproduct_saturation.exe'
sys.argv = sys.argv[:1]


def tau(r):
    return (((100*r)**615).bit_length()-1+272)//200 if r else 1


def leaf(N, w):
    r = N*w*w
    return r*(4+tau(r))


def targets(k):
    result = [tuple(int(j == 0) for j in range(k)), tuple(int(j == k-1) for j in range(k))]
    exp = 0
    while len(result) < 2*k-1:
        kinds = ['integer'] if exp == 0 else ['reciprocal', 'integer']
        for kind in kinds:
            for sign in [-1, 1]:
                z = sign * 2**exp
                result.append(tuple(z**(k-1-j if kind == 'reciprocal' else j) for j in range(k)))
        exp += 1
    return set(result[:2*k-1])


def replay(k, ops):
    ident = [[int(i == j) for j in range(k)] for i in range(k)]
    rows = [r[:] for r in ident]
    scans = [[0]*k, [0]*(k-1)+[k-1]]
    peaks = [0, k-1]
    seen = {tuple(r) for r in rows}
    charge = 0
    for tag, d, h, sign, s in ops:
        d -= 1
        h -= 1
        assert 0 <= d < k and s >= 0
        if tag == 1:
            assert 0 <= h < k and d != h and sign in (-1, 1)
            rows[d] = [x+sign*(2**s)*y for x, y in zip(rows[d], rows[h])]
            charge += 1 if sign == 1 else 3
            for v in scans:
                v[d] = 1+max(v[d], v[h]+s)
        elif tag == 2:
            rows[d] = [x*2**s for x in rows[d]]
            for v in scans:
                v[d] += s
        elif tag == 3:
            assert all(x % 2**s == 0 for x in rows[d])
            rows[d] = [x//2**s for x in rows[d]]
            for v in scans:
                v[d] = max(0, v[d]-s)
        elif tag == 4:
            rows[d] = [-x for x in rows[d]]
            charge += 1
            for v in scans:
                v[d] += 1
        else:
            raise AssertionError(tag)
        peaks = [max(p, max(v)) for p, v in zip(peaks, scans)]
        seen.update(tuple(r) for r in rows)
    assert rows == ident
    assert targets(k) <= seen
    return charge, peaks[0], peaks[1]-(k-1)


def run(n, K, **kwargs):
    values = dict(n=n, kmax=K)
    values.update(kwargs)
    text = '&run ' + ', '.join(f'{key}={str(v).lower() if not isinstance(v,bool) else (".true." if v else ".false.")}'
                               for key, v in values.items()) + ' /\n'
    p = subprocess.run([str(EXE)], input=text, text=True, capture_output=True)
    assert p.returncode == 0, (p.stdout, p.stderr)
    data, levels, tables = {}, [], {}
    current = None
    for line in p.stdout.splitlines():
        bits = line.split()
        if not bits:
            continue
        if bits[0] == 'LEVEL':
            levels.append(tuple(map(int, bits[1:])))
        elif bits[0] == 'TABLE':
            k, c, a, b, count = map(int, bits[1:])
            current = k
            tables[k] = ((c, a, b), count, [])
        elif bits[0] == 'OP':
            tables[current][2].append(tuple(map(int, bits[1:])))
        elif bits[0] != 'END_TABLE':
            data[bits[0]] = bits[1:]
    total, w, N, used = 0, n, 1, {}
    for k, c, a, b, child, multiplicity in levels:
        assert N == multiplicity
        assert child == w//k+1+max(a, w%k+b) and 1 <= child < w
        assert used.setdefault(k, (c,a,b)) == (c,a,b)
        total += 8*N*(child-1)*c
        N *= 2*k-1
        w = child
    total += leaf(N,w)
    assert total == int(data['COST'][0])
    assert set(tables) == set(used)
    for k, (profile, count, ops) in tables.items():
        assert count == len(ops)
        assert replay(k, ops) == profile == used[k]
    assert int(data['LOWER_BOUND'][0]) <= total
    if data['STATUS'] == ['OPTIMAL']:
        assert int(data['LOWER_BOUND'][0]) == total
    return data, levels, tables


def k2_reference(n):
    answer = leaf(1,n)
    for a in range(2,n-1):
        for b in range(max(2,a-1),a+1):
            @lru_cache(None)
            def solve(w,N):
                result = leaf(N,w)
                child = w//2+1+max(a,w%2+b)
                if child < w:
                    result = min(result, 32*N*(child-1)+solve(child,3*N))
                return result
            answer = min(answer,solve(n,1))
    return answer


class Integration(unittest.TestCase):
    def test_k2_exact(self):
        for n in [1,2,8,16,40,50,60,79,206]:
            data,_,_ = run(n,2)
            self.assertEqual(data['STATUS'], ['OPTIMAL'])
            self.assertEqual(int(data['COST'][0]), k2_reference(n))

    def test_global_certificates(self):
        for n, expected in [(40,92750),(50,141984)]:
            data,_,_ = run(n,5)
            self.assertEqual(data['STATUS'], ['OPTIMAL'])
            self.assertEqual(int(data['COST'][0]),expected)

    def test_no_budget_input(self):
        p = subprocess.run([str(EXE)], input='&run n=40,kmax=3,max_nodes=1 /',
                           text=True,capture_output=True)
        self.assertNotEqual(p.returncode,0)
        self.assertIn('ERROR',p.stdout)

    def test_pruning_equivalence(self):
        for n,K in [(5,3),(6,3),(16,2),(40,2),(60,2)]:
            a,_,_ = run(n,K,use_bounds=True)
            b,_,_ = run(n,K,use_bounds=False)
            self.assertEqual(a['COST'],b['COST'])
            self.assertEqual(a['STATUS'],b['STATUS'])

    def test_invalid(self):
        for text in ['&run n=0 /','&run n=-1 /','&run kmax=0 /',
                     '&run n=2147483647 /','garbage']:
            p=subprocess.run([str(EXE)],input=text,text=True,capture_output=True)
            self.assertNotEqual(p.returncode,0)
            self.assertIn('ERROR',p.stdout)


if __name__ == '__main__':
    assert EXE.exists(), 'Fortran executable must be built before acceptance tests'
    unittest.main()
