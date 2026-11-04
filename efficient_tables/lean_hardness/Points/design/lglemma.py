import itertools, random, sys
sys.setrecursionlimit(10000)
def dhc(n, arcs):
    succ = {v: [w for (u, w) in arcs if u == v] for v in range(n)}
    path = [0]; seen = {0}
    def dfs(u):
        if len(path) == n: return 0 in succ[u]
        for w in succ[u]:
            if w not in seen:
                seen.add(w); path.append(w)
                if dfs(w): return True
                seen.discard(w); path.pop()
        return False
    return dfs(0)
def H_edges(n, arcs):
    E = []
    for v in range(n):
        E += [frozenset({('in', v), ('mid', v)}), frozenset({('mid', v), ('out', v)}), frozenset({('mid', v), ('leaf', v)})]
    for u, w in arcs: E.append(frozenset({('out', u), ('in', w)}))
    return E
def lg_hc(E):
    m = len(E); adj = {i: [j for j in range(m) if j != i and E[i] & E[j]] for i in range(m)}
    path = [0]; seen = {0}
    def dfs(u):
        if len(path) == m: return 0 in adj[u]
        for w in adj[u]:
            if w not in seen:
                seen.add(w); path.append(w)
                if dfs(w): return True
                seen.discard(w); path.pop()
        return False
    return dfs(0)
random.seed(int(sys.argv[1])); bad = 0; cnt = {True: 0, False: 0}
for trial in range(int(sys.argv[2])):
    n = random.randint(2, 5)
    arcs = set()
    for u in range(n):
        for w in random.sample([x for x in range(n) if x != u], min(n - 1, random.randint(1, 2))):
            arcs.add((u, w))
    arcs = sorted(arcs)
    a, b = dhc(n, arcs), lg_hc(H_edges(n, arcs))
    cnt[a] += 1
    if a != b:
        bad += 1; print("MISMATCH", n, arcs, a, b)
print("seed", sys.argv[1], cnt, "mismatches", bad)
