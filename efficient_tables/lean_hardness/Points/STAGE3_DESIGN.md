# Stage 3 design (2026-10-12): SAT → table problem, all steps validated by brute force

Chain (all ours, no third-party code):
  CNF-SAT (complexitylib, NP-complete)
    → DHC₂: directed Hamiltonian cycle, every vertex out-degree ≤ 2        [cells + rotating clauses]
    → EHC: Hamiltonian cycle in the line graph of H(D)                       [split + pendant lemma]
    → GenTableOpt with k = 2 (cycle version of Stage 1: translate labels so one edge's label is 0)

## 1. SAT → DHC₂  (design/dhc3.py; 480 random CNFs, 0 mismatches, max out-degree 2)
- Cell (one per literal occurrence; 6 nodes, out ≤ 2):
  0→{1,3}, 1→{2,L}, 2→{3,5}, 3→{0,4}, 4→{5,C}, 5→{2,R}; entries L→0, R→4, C→1.
  Exact coverings (found by design/cell3.py, checked exhaustively):
    rightward L⇒R (0 1 2 3 4 5), rightward+detour {L⇒C (0 3 4), C⇒R (1 2 5)}, leftward R⇒L (4 5 2 3 0 1).
  Negative literals use the mirrored cell (L↔R), so their detour exists only leftward.
- Row of variable x: cells for its occurrences in sequence (dummy cell if none); top_x → first.eL,
  top_x → last.eR; first.xL → bot_x, last.xR → bot_x; bot_x → top_{x+1}; cyclic.
  Rightward row = x true.
- Clause with ℓ literals: rotating cycle c¹→…→c^ℓ→c¹; literal k's cell xC → c^k; c^m → eC of literal m+1.
- YES: one chosen true literal per clause detours through the whole rotating cycle (enter c^k, exit c^{k−1}).
- NO: each cell is in one of its three modes (finite lemma); modes propagate along rows (a direction);
  clause nodes are entered only from detour-mode cells ⇒ a true literal per clause. Cross-overs between
  detours are harmless for this direction.

## 2. DHC₂ → EHC  (design/lglemma.py; 450 random digraphs, 0 mismatches)
H(D): per vertex v: v_in – v_mid – v_out, pendant v_mid – ℓ_v; per arc u→v: u_out – v_in.
Claim: D has a directed Hamiltonian cycle ⟺ L(H(D)) has a Hamiltonian cycle (out-degree ≤ 2 in D).
Proof: pivots of consecutive edges; ℓ_v never a pivot ⇒ both mid edges are transitions; transitions at
each vertex are even; v_out has the mid edge + an odd number (≤ 2) of out-arc transitions ⇒ exactly 1;
Σ in = Σ out = n ⇒ exactly one in-arc transition at every v_in; transitions never leave a σ-closed set
and the pivot sequence is cyclic ⇒ σ is one cycle.

## 3. EHC → GenTableOpt (cycle version of Stage 1)
Points {lab e − lab e₀ : e ∈ E}, budget 7|E|; the extraction lemma already yields W2 steps on the whole
cyclic sequence 0, O, 0 when 0 ∈ O.

## Formalization order
3a. EHC ↔ GenTableOpt (cycle version) + the split/pendant lemma DHC₂ ↔ EHC.
3b. SAT → DHC₂ correctness (cell lemma by `decide`, row propagation, clause argument, explicit YES cycle).
3c. Encodings + FP for the composite map SAT.language → GenLang; then NPHard GenLang (Cook–Levin).
