import itertools, sys
# Exits: 'L','R','C' as extra targets. Each internal node chooses <=2 out-targets among internal nodes + exits,
# each exit used by exactly one node. Entries eL,eR,eC.
def covers(t, out, eL, eR, eC):
    entries = {'L': eL, 'R': eR, 'C': eC}
    res = set()
    for k in (1, 2, 3):
        for ens in itertools.combinations('LRC', k):
            for exs in itertools.permutations('LRC', k):
                pairs = list(zip(ens, exs))
                def go(i, visited):
                    if i == len(pairs): return len(visited) == t
                    s, e = entries[pairs[i][0]], pairs[i][1]
                    if s in visited: return False
                    def dfs(v, vis):
                        if e in out[v] and go(i + 1, vis): return True
                        for w in out[v]:
                            if isinstance(w, int) and w not in vis and dfs(w, vis | {w}): return True
                        return False
                    return dfs(s, visited | {s})
                if go(0, frozenset()): res.add(frozenset(pairs))
    return res
want = {frozenset([('L', 'R')]), frozenset([('L', 'C'), ('C', 'R')]), frozenset([('R', 'L')])}
def search(t):
    nodes = list(range(t))
    for exitowner in itertools.product(nodes, repeat=3):   # owners of exits L,R,C
        for eL, eR, eC in itertools.product(nodes, repeat=3):
            if eL != 0: continue
            fixed = {v: [x for x, o in zip('LRC', exitowner) if o == v] for v in nodes}
            if any(len(fixed[v]) > 2 for v in nodes): continue
            opts = []
            for v in nodes:
                room = 2 - len(fixed[v]); others = [w for w in nodes if w != v]
                choices = [c for r in range(room + 1) for c in itertools.combinations(others, r)]
                opts.append([tuple(fixed[v]) + c for c in choices])
            for combo in itertools.product(*opts):
                out = {v: set(combo[v]) for v in nodes}
                if covers(t, out, eL, eR, eC) == want:
                    print("FOUND t=%d eL=%d eR=%d eC=%d out=%s" % (t, eL, eR, eC, {v: sorted(map(str, out[v])) for v in nodes}))
                    sys.stdout.flush(); return True
    return False
for t in range(2, 7):
    print("t", t); sys.stdout.flush()
    if search(t): break
