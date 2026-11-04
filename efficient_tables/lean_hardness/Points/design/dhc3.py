import itertools, random, sys
sys.setrecursionlimit(100000)
CELL = {0: [1, 3], 1: [2, 'L'], 2: [3, 5], 3: [0, 4], 4: [5, 'C'], 5: [2, 'R']}
EL, ER, EC = 0, 4, 1          # entries from left / right / clause
XL, XR, XC = 1, 5, 4          # exit owners
def build(nv, clauses):
    G = {}
    def arc(u, v): G.setdefault(u, set()).add(v); G.setdefault(v, set())
    occ = {i: [] for i in range(nv)}
    for j, cl in enumerate(clauses):
        for k, (v, s) in enumerate(cl): occ[v].append((j, k, s))
    port = {}   # (cell) -> dict of physical entry/exit node names
    for i in range(nv):
        cells = occ[i] if occ[i] else [None]
        names = []
        for t, oc in enumerate(cells):
            mirror = (oc is not None and not oc[2])
            nd = lambda q, t=t: ('cell', i, t, q)
            for q, outs in CELL.items():
                for o in outs:
                    if isinstance(o, int): arc(nd(q), nd(o))
            # logical ports; mirror swaps left/right
            eL, eR = (nd(ER), nd(EL)) if mirror else (nd(EL), nd(ER))
            xL, xR = (nd(XR), nd(XL)) if mirror else (nd(XL), nd(XR))
            names.append(dict(eL=eL, eR=eR, xL=xL, xR=xR, eC=nd(EC), xC=nd(XC), oc=oc))
        top, bot = ('top', i), ('bot', i)
        arc(top, names[0]['eL']); arc(top, names[-1]['eR'])
        arc(names[0]['xL'], bot); arc(names[-1]['xR'], bot)
        for c1, c2 in zip(names, names[1:]):
            arc(c1['xR'], c2['eL']); arc(c2['xL'], c1['eR'])
        arc(bot, ('top', (i + 1) % nv))
        for nm in names:
            if nm['oc'] is not None: port[(nm['oc'][0], nm['oc'][1])] = nm
    for j, cl in enumerate(clauses):
        l = len(cl)
        for k in range(l):
            c = ('cl', j, k)
            arc(port[(j, k)]['xC'], c)                 # entry k at c^k
            if l > 1: arc(c, ('cl', j, (k + 1) % l))
            arc(c, port[(j, (k + 1) % l)]['eC'])        # exit from c^m to literal m+1
    return G
def has_hc(G):
    n = len(G); start = ('top', 0); path = [start]; seen = {start}
    def dfs(u):
        if len(path) == n: return start in G[u]
        for v in G[u]:
            if v not in seen:
                seen.add(v); path.append(v)
                if dfs(v): return True
                seen.discard(v); path.pop()
        return False
    return dfs(start)
def sat(nv, clauses):
    return any(all(any(b[v] == s for v, s in cl) for cl in clauses) for b in itertools.product([False, True], repeat=nv))
if __name__ == '__main__':
    random.seed(int(sys.argv[1])); bad = 0; cnt = {True: 0, False: 0}
    for trial in range(int(sys.argv[2])):
        nv = random.randint(1, 3); m = random.randint(1, 5)
        clauses = [[(random.randrange(nv), random.random() < 0.5) for _ in range(random.randint(1, 3))] for _ in range(m)]
        if random.random() < 0.25 and nv >= 2:
            clauses = [[(0, True), (1, True)], [(0, False), (1, True)], [(0, True), (1, False)], [(0, False), (1, False)]]
        G = build(nv, clauses)
        od = max(len(G[u]) for u in G)
        s, h = sat(nv, clauses), has_hc(G)
        cnt[s] += 1
        if od > 2 or s != h:
            bad += 1; print("MISMATCH", nv, clauses, "sat", s, "hc", h, "maxout", od); sys.stdout.flush()
            if bad > 3: break
    print("seed", sys.argv[1], "sat/unsat:", cnt, "mismatches:", bad)
