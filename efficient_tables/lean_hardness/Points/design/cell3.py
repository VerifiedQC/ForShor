import itertools, sys
exec(open('cell2.py').read().split("for t in range(2, 7)")[0])  # covers, want
def arcs_of(order): return list(zip(order, order[1:]))
def run(t):
    nodes = list(range(t)); found = 0; checked = 0
    for sT in itertools.permutations(nodes):
        if sT[0] != 0: continue
        eL, xR = sT[0], sT[-1]
        for pp in itertools.permutations(nodes):
            if pp[0] != eL or pp[-1] != xR: continue
            for k in range(1, t):
                xC, eC = pp[k - 1], pp[k]
                A = set(arcs_of(sT)) | set(arcs_of(pp[:k])) | set(arcs_of(pp[k:]))
                out = {v: set() for v in nodes}
                for u, w in A: out[u].add(w)
                out[xR].add('R'); out[xC].add('C')
                if any(len(out[v]) > 2 for v in nodes): continue
                for sF in itertools.permutations(nodes):
                    eR, xL = sF[0], sF[-1]
                    o2 = {v: set(out[v]) for v in nodes}
                    for u, w in arcs_of(sF): o2[u].add(w)
                    o2[xL].add('L')
                    if any(len(o2[v]) > 2 for v in nodes): continue
                    checked += 1
                    if covers(t, o2, eL, eR, eC) == want:
                        print("FOUND t=%d eL=%d eR=%d eC=%d out=%s" % (t, eL, eR, eC, {v: sorted(map(str, o2[v])) for v in nodes}))
                        sys.stdout.flush(); found += 1
                        if found >= 3: return
    print("t", t, "candidates checked", checked)
for t in (5, 6, 7):
    run(t); sys.stdout.flush()
