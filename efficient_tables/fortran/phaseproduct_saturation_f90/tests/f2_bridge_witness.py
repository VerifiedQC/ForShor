"""Deterministic F2 bridge/construction witnesses. No inference, no search.

Output JSON to a NEW path supplied on command line. Repository marker convention
is deliberately separate from positive-denominator homogeneous normalization.
"""
from fractions import Fraction
from pathlib import Path
from collections import Counter
import hashlib
import json
import sys


def points(mode, k, recipe="F2"):
    m = (2 * k - 1) if mode == "PP" else (3 * k - 2)
    out = [("int", 0), ("frac", 0)]
    out += [("int", -1), ("int", 1)] if recipe == "F2" else [("int", 1), ("int", -1)]
    e = 1
    while len(out) < m:
        z = 1 << e
        out += [("frac", -z), ("frac", z), ("int", -z), ("int", z)] if recipe == "F2" else [("int", z), ("int", -z), ("frac", z), ("frac", -z)]
        e += 1
    return out[:m]


def rational(p):
    kind, z = p
    return Fraction(z) if kind == "int" else (None if z == 0 else Fraction(1, z))


def target(k, p, convention="repo"):
    kind, z = p
    if convention == "repo":
        return [z ** j for j in range(k)] if kind == "int" else [z ** (k - 1 - j) for j in range(k)]
    t = rational(p)
    if t is None:
        return [0] * (k - 1) + [1]
    return [t.numerator ** j * t.denominator ** (k - 1 - j) for j in range(k)]


def inv(ops):
    out = []
    for o in reversed(ops):
        if o[0] == "add": out.append(("add", o[1], o[2], -o[3], o[4]))
        elif o[0] == "L": out.append(("R", o[1], o[2]))
        elif o[0] == "R": out.append(("L", o[1], o[2]))
        elif o[0] == "neg": out.append(o)
        else: raise ValueError("Cannot invert a marker")
    return out


def build(k, p, convention="repo"):
    if p == ("int", 0) or p == ("frac", 0): return []
    row = target(k, p, convention)
    ops = []
    if abs(row[0]) != 1: ops.append(("L", 0, abs(row[0]).bit_length() - 1))
    if row[0] < 0: ops.append(("neg", 0))
    for j in range(1, k):
        a = row[j]
        assert a and abs(a) & (abs(a) - 1) == 0
        ops.append(("add", 0, j, 1 if a > 0 else -1, abs(a).bit_length() - 1))
    return ops


def c1(k, pts, convention="repo"):
    ops = []
    for p in pts:
        b = build(k, p, convention)
        r = k - 1 if p == ("frac", 0) else 0
        ops += b + [("mark", r, p)] + inv(b)
    return ops


def paired(k, pts, positive_first=True, convention="repo"):
    assert pts[:2] == [("int", 0), ("frac", 0)]
    ops = [("mark", 0, pts[0]), ("mark", k - 1, pts[1])]
    ix = 2
    while ix < len(pts):
        if ix + 1 == len(pts):
            ops += c1(k, [pts[ix]], convention)
            break
        pn, pp = pts[ix:ix+2]
        assert rational(pn) == -rational(pp)
        pos = target(k, pp, "positive")
        b = []
        for j in [0, 1]:
            sh = pos[j].bit_length() - 1
            if sh: b.append(("L", j, sh))
        for j in range(2, k):
            b.append(("add", j % 2, j, 1, pos[j].bit_length() - 1))
        ops += b
        needs_neg = target(k, pn, convention) == [-x for x in target(k, pn, "positive")]
        def marker(p):
            if p == pn and needs_neg:
                return [("neg", 0), ("mark", 0, p), ("neg", 0)]
            return [("mark", 0, p)]
        if positive_first:
            ops += [("add", 0, 1, 1, 0)] + marker(pp)
            ops += [("add", 0, 1, -1, 1)] + marker(pn)
            ops += [("add", 0, 1, 1, 0)]
        else:
            ops += [("add", 0, 1, -1, 0)] + marker(pn)
            ops += [("add", 0, 1, 1, 1)] + marker(pp)
            ops += [("add", 0, 1, -1, 0)]
        ops += inv(b)
        ix += 2
    return ops


def replay(k, ops, required, convention="repo"):
    identity = [[int(i == j) for j in range(k)] for i in range(k)]
    st = [r[:] for r in identity]
    marks = []
    maxbits = 1
    for o in ops:
        t = o[0]
        if t == "add":
            _, d, s, sg, sh = o
            assert d != s and sh >= 0 and sg in [-1, 1]
            st[d] = [a + sg * (b << sh) for a, b in zip(st[d], st[s])]
        elif t == "L": st[o[1]] = [a << o[2] for a in st[o[1]]]
        elif t == "R":
            q = 1 << o[2]
            assert all(a % q == 0 for a in st[o[1]]), ("nonexact shift", o)
            st[o[1]] = [a // q for a in st[o[1]]]
        elif t == "neg": st[o[1]] = [-a for a in st[o[1]]]
        elif t == "mark":
            assert st[o[1]] == target(k, o[2], convention), ("marker", k, o, st[o[1]])
            marks.append(rational(o[2]))
        else: raise ValueError(o)
        maxbits = max(maxbits, max(abs(x).bit_length() for row in st for x in row))
    assert st == identity
    assert Counter(marks) == Counter(map(rational, required))
    assert len(marks) == len(set(marks))
    return maxbits


def width(w, k, ops):
    a = [w // k] * (k - 1) + [w - (k - 1) * (w // k)]
    mx = max(a)
    for o in ops:
        if o[0] == "add": a[o[1]] = 1 + max(a[o[1]], a[o[2]] + o[4])
        elif o[0] == "L": a[o[1]] += o[2]
        elif o[0] == "R": a[o[1]] = max(0, a[o[1]] - o[2])
        elif o[0] == "neg": a[o[1]] += 1
        mx = max(mx, max(a))
    return 1 + mx


def counts(ops):
    ap = sum(o[0] == "add" and o[3] == 1 for o in ops)
    am = sum(o[0] == "add" and o[3] == -1 for o in ops)
    nu = sum(o[0] == "neg" for o in ops)
    sh = sum(o[0] in ["L", "R"] for o in ops)
    return dict(additions=ap+am, positive_additions=ap, negative_additions=am, negations=nu, shifts=sh, charged=ap+3*am+nu, arithmetic=ap+am+nu+sh)


def signed_reciprocal(p):
    kind, z = p
    return ("frac", -z) if kind == "int" else ("int", -z)


def conjugate(k, ops):
    """Exact addition-preserving signed reversal, positive-denominator targets."""
    d = k - 1
    out = []
    for o in ops:
        if o[0] == "add":
            _, i, j, sg, s = o
            out.append(("add", d-i, d-j, sg * (-1)**(i+j), s))
        elif o[0] in ["L", "R"]: out.append((o[0], d-o[1], o[2]))
        elif o[0] == "neg": out.append(("neg", d-o[1]))
        elif o[0] == "mark":
            _, i, p = o
            newp = signed_reciprocal(p)
            qrow = [(-1)**(d-i+j) * target(k, p, "positive")[d-j] for j in range(k)]
            expected = target(k, newp, "positive")
            flip = qrow != expected
            assert not flip or qrow == [-x for x in expected]
            if flip: out.append(("neg", d-i))
            out.append(("mark", d-i, newp))
            if flip: out.append(("neg", d-i))
    return out


def run():
    cases = []
    tiny_programs = []
    scan_checks = 0
    for mode in ["PP", "PTP"]:
        for k in list(range(2, 25)) + [32, 48, 64]:
            pts = points(mode, k)
            m = len(pts); q = m-2; p = q//2; s = q%2
            f = sum(kind == "frac" and z != 0 for kind, z in pts)
            fm = sum(kind == "frac" and z < 0 for kind, z in pts)
            nu = 2*fm*(k%2 == 0)
            e = max([0] + [abs(z).bit_length()-1 for _,z in pts if z])
            E = e*(k-1)
            pc = c1(k, pts); pp = paired(k, pts); pn = paired(k, pts, False)
            bits = [replay(k, x, pts) for x in [pc,pp,pn]]
            cc,cp,cn = map(counts, [pc,pp,pn])
            assert cc["additions"] == 2*(k-1)*q
            assert cc["charged"] == 4*(k-1)*q+nu
            assert cc["arithmetic"] == 2*(k-1)*q+2*f+nu <= 12*k*k
            assert cp["additions"] == p*(2*k-1)+s*(2*k-2)
            assert cp["charged"] == p*(4*k-3)+s*4*(k-1)+nu
            assert cn["charged"] == cp["charged"]+2*p
            canon = points(mode, k, "canonical")
            assert set(map(rational, map(signed_reciprocal,canon))) == set(map(rational,pts))
            old = c1(k, canon, "positive")
            new = conjugate(k,old)
            replay(k,new,pts,"positive")
            assert counts(old)["additions"] == counts(new)["additions"]
            profiles = []
            # Every residue, both very small operands and large operands; exhaustive
            # over this declared finite set, not an all-w computational claim.
            for base in [0,k, max(4096,16*k**3)//k*k]:
                for r in range(k):
                    w = base+r
                    wc,wp,wn = [width(w,k,x) for x in [pc,pp,pn]]
                    assert wc <= w//k+k+2*E+2*k*m <= w//k+8*k*k
                    assert wp == wn
                    profiles.append(dict(w=w, c1_child=wc, paired_child=wp))
                    scan_checks += 1
            cases.append(dict(mode=mode,k=k,M=m,max_exponent=e,coefficient_bits=bits,c1=cc,paired_positive_first=cp,paired_negative_first=cn,width_profiles=profiles))
            if k <= 4:
                tiny_programs.append(dict(mode=mode,k=k,points=pts,c1=pc,paired=pp,canonical_conjugated=new))
    # Listed paper coefficients: exact signed-digit compilation and one-add
    # obstruction are proved in BRIDGES; the arithmetic identities replay here.
    macro = {3:[(1,2),(-1,0)],6:[(1,3),(-1,1)],15:[(1,4),(-1,0)],12:[(1,4),(-1,2)],48:[(1,6),(-1,4)]}
    for c, terms in macro.items(): assert sum(sg*(1<<e) for sg,e in terms)==c
    return dict(status="all_assertions_passed", scope="finite deterministic witnesses; all-k statements require BRIDGES proofs", cases=cases, case_count=len(cases), scan_checks=scan_checks, tiny_programs=tiny_programs, macro_expansions=macro)


if __name__ == "__main__":
    assert len(sys.argv)==2, "supply a new JSON output path"
    output=Path(sys.argv[1])
    assert not output.exists(), "refusing to replace an existing file"
    result=run()
    result["script_sha256"]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:result[k] for k in ["status","case_count","scan_checks","script_sha256"]}))
