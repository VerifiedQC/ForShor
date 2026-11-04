# Nine elementary algebra lemmas passed trusted kernel replay

Source: `lean/Paper/GapAlgebraRepair20261015.lean`. Record: `GapAlgebraRepair20261015.formal.json`. Adapter: `check_gap_formal.2026-10-15.py GapAlgebraRepair20261015`.

The existing autoformalizer check and compile adapters and its separate trusted kernel replay all succeeded. All nine theorem checks returned true, every structural problem is null, and `all_certified=true`. Check time was 16.20 seconds, compilation 17.06 seconds, replay 49.32 seconds. The unchanged limit was 180 seconds per stage. The prior failed source and JSON remain preserved: that attempt used unqualified generic lemma names unavailable under the deliberately minimal import; the repaired file qualifies three lemmas with `Int`. No mathematical statement was weakened.

The module proves:

1. Equal scanner-sum and log-determinant shift changes cancel.
2. The scalar addition-scanner update increases its destination width by at least one.
3. A paid step preserves the elementary count-versus-potential inequality.
4. An unchanged potential preserves that inequality across a free step.
5. Given the final count/potential relation and endpoint equalities, t<=ka and c<=3ka.
6. The canonical width offset rewrites as max(a,r+b)=a+max(0,r-d) when d=a-b.
7. If a terminal value and its tail are divisible by m, the value at the cut is divisible by m.
8. Divisibility of x-pr by pk gives x=p(kq+r) for some integer q.
9. The preceding two divisibility implications compose.

These are elementary implications, not an encoding of the table DSL, determinant evolution, the whole-program induction, marker legality, all prefix-product divisibilities, word-count bounds, Kannan's algorithm, or a complexity theorem. In particular the potential inequality is an explicit premise of lemma 5. It is proved analytically for actual programs in the profile paper; it is not silently formalized here. The two main gap theorems are not claimed to be fully machine checked.

The trusted replay records allowed foundational axioms and no `sorryAx`. The accepted module fingerprint is `0c2e0f188ea76867d33901f87c6dab831bcc4499f13924433d8016071a6b6440`; the compiled module SHA256 is `32d537862f56a6c6e2dee34b60fc8a4ea35d32cf8019312a0c6eafef5d383d5e`. The JSON pins the source, checker, existing autoresearcher workbench toolchain, Lake manifest, and trusted adapter. No toolkit source, dependency, or installed model was modified; no local inference was used.
