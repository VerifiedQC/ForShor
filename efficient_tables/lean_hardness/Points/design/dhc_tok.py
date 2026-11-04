# Token-local SAT -> DHC2 construction (the one formalized in Points/SatDhc.lean).
# Tokens: ('b',False)=00, ('b',True)=11, 'L'=01 (litSep), 'C'=10 (clauseSep).
import itertools, random, sys
sys.setrecursionlimit(100000)
def tokens(cnf):
    t = []
    for cl in cnf:
        for (v, s) in cl:
            t.append(('b', s)); t += [('b', True)] * v; t.append('L')
        t.append('C')
    return t
def build(tk):
    T = len(tk); N6 = 6 * T * T
    c = lambda x, t, q: 6 * (x * T + t) + q
    top = lambda x: N6 + x; bot = lambda x: N6 + T + x
    r = lambda t: N6 + 2 * T + t; qq = lambda t: N6 + 3 * T + t
    n = N6 + 4 * T
    isSep = lambda t: tk[t] in ('L', 'C')
    bnd = lambda t: t == 0 or isSep(t - 1)
    sgn = lambda s: s < T and tk[s] not in ('L', 'C') and bnd(s)
    def lit(x, s):
        return sgn(s) and all(s + 1 + i < T and tk[s + 1 + i] == ('b', True) for i in range(x)) \
            and s + 1 + x < T and tk[s + 1 + x] == 'L'
    pos = lambda s: tk[s] == ('b', True)
    mir = lambda x, t: lit(x, t) and not pos(t)
    cs = lambda t: tk[t] == 'C'
    clStart = lambda t: t == 0 or cs(t - 1)
    eL = lambda x, t: c(x, t, 4 if mir(x, t) else 0)
    eR = lambda x, t: c(x, t, 0 if mir(x, t) else 4)
    Lp = lambda x, t: bot(x) if t == 0 else eR(x, t - 1)
    Rp = lambda x, t: bot(x) if t == T - 1 else eL(x, t + 1)
    outs = {}
    for x in range(T):
        for t in range(T):
            m = mir(x, t)
            outs[c(x, t, 0)] = [c(x, t, 1), c(x, t, 3)]
            outs[c(x, t, 1)] = [c(x, t, 2), Rp(x, t) if m else Lp(x, t)]
            outs[c(x, t, 2)] = [c(x, t, 3), c(x, t, 5)]
            outs[c(x, t, 3)] = [c(x, t, 0), c(x, t, 4)]
            outs[c(x, t, 4)] = [c(x, t, 5)] + ([r(t)] if lit(x, t) else [])
            outs[c(x, t, 5)] = [c(x, t, 2), Lp(x, t) if m else Rp(x, t)]
        outs[top(x)] = [eL(x, 0), eR(x, T - 1)]
        outs[bot(x)] = [top((x + 1) % T)]
    for t in range(T):
        o = [qq(t)] if cs(t) else [r(t + 1)]
        if not cs(t):
            o += [c(x, t + 1, 1) for x in range(T) if lit(x, t + 1)]
        outs[r(t)] = o
        o = [r(t)] if clStart(t) else [qq(t - 1)]
        if clStart(t):
            o += [c(x, t, 1) for x in range(T) if lit(x, t)]
        outs[qq(t)] = o
    assert len(outs) == n and all(len(v) <= 2 and len(set(v)) == len(v) and u not in v for u, v in outs.items())
    assert all(0 <= w < n for v in outs.values() for w in v)
    order = [top(x) for x in range(T)] + [qq(t) for t in range(T)] + [r(t) for t in range(T)] + list(range(n))
    return n, outs, order
def has_hc(n, outs, order=None):
    order = order if order is not None else list(range(n))
    preds = {u: set() for u in range(n)}
    for u, vs in outs.items():
        for v in vs: preds[v].add(u)
    S = {u: set(vs) for u, vs in outs.items()}; P = preds
    def solve(S, P, succ, pred):
        # propagate
        changed = True
        while changed:
            changed = False
            for u in range(n):
                if u not in succ:
                    if not S[u]: return False
                    if len(S[u]) == 1:
                        v = next(iter(S[u]))
                        if v in pred: return False
                        if not force(S, P, succ, pred, u, v): return False
                        changed = True
                if u not in pred:
                    if not P[u]: return False
                    if len(P[u]) == 1:
                        w = next(iter(P[u]))
                        if w in succ: return False
                        if not force(S, P, succ, pred, w, u): return False
                        changed = True
        if len(succ) == n:
            x = 0
            for _ in range(n - 1):
                x = succ[x]; assert x != 0
            assert succ[x] == 0 and all(succ[a] in outs[a] for a in range(n))
            return True
        cand = [u for u in order if u not in succ]
        u = cand[0]
        for v in list(S[u]):
            S2 = {a: set(b) for a, b in S.items()}; P2 = {a: set(b) for a, b in P.items()}
            s2, p2 = dict(succ), dict(pred)
            if force(S2, P2, s2, p2, u, v) and solve(S2, P2, s2, p2): return True
        return False
    def force(S, P, succ, pred, u, v):
        if u in succ: return succ[u] == v
        if v in pred: return False
        if v not in S[u]: return False
        # subtour check: walk from v forward
        end = v; k = 1
        while end in succ: end = succ[end]; k += 1
        if end == u and k < n: return False
        succ[u] = v; pred[v] = u
        for w in S[u]:
            if w != v: P[w].discard(u)
        for w in P[v]:
            if w != u: S[w].discard(v)
        S[u] = {v}; P[v] = {u}
        # forbid closing a short cycle: end of chain through v -> start of chain through u
        st = u; k = 0
        while st in pred and pred[st] != v and k <= n: st = pred[st]; k += 1
        if st in pred: return len(succ) == n or True
        en = v; cnt = 1
        while en in succ: en = succ[en]; cnt += 1
        x = st; tot = 1
        while x in succ: x = succ[x]; tot += 1
        if tot < n and st in S[en]:
            S[en].discard(st); P[st].discard(en)
        return True
    return solve(S, P, {}, {})
ORDER = []
def sat(nv, cnf):
    return any(all(any(b[v] == s for v, s in cl) for cl in cnf) for b in itertools.product([False, True], repeat=nv))
if __name__ == '__main__':
    random.seed(int(sys.argv[1])); bad = 0; cnt = {True: 0, False: 0}
    for trial in range(int(sys.argv[2])):
        nv = random.randint(1, 3); m = random.randint(1, 5)
        cnf = [[(random.randrange(nv), random.random() < 0.5) for _ in range(random.randint(0 if random.random() < 0.05 else 1, 3))] for _ in range(m)]
        if random.random() < 0.2 and nv >= 2:
            cnf = [[(0, True), (1, True)], [(0, False), (1, True)], [(0, True), (1, False)], [(0, False), (1, False)]]
        n, outs, order = build(tokens(cnf))
        s, h = sat(nv, cnf), has_hc(n, outs, order)
        cnt[s] += 1
        if s != h:
            bad += 1; print("MISMATCH", cnf, "sat", s, "hc", h); sys.stdout.flush()
            if bad > 3: break
    print("seed", sys.argv[1], "sat/unsat:", cnt, "mismatches:", bad)
