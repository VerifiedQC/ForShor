// Data for the Shor's algorithm overview on the project page (index.html).
// Generated from curated text plus verbatim copies of the named declarations
// at the recorded file:line. If a statement no longer matches the source,
// regenerate rather than edit the snippet.
window.ALGORITHM = {
 "root": "ForShor/ShorVerification",
 "repo": "https://github.com/VerifiedQC/ForShor/blob/main",
 "rows": [
  [
   "factor"
  ],
  [
   "choose"
  ],
  [
   "hreg",
   "inity",
   "modexp",
   "iqft"
  ],
  [
   "cf"
  ],
  [
   "reduce"
  ]
 ],
 "edges": [
  {
   "from": "factor",
   "to": "choose",
   "kind": "primary",
   "label": "N"
  },
  {
   "from": "choose",
   "to": "hreg",
   "kind": "primary",
   "label": "a"
  },
  {
   "from": "hreg",
   "to": "inity",
   "kind": "primary"
  },
  {
   "from": "inity",
   "to": "modexp",
   "kind": "primary"
  },
  {
   "from": "modexp",
   "to": "iqft",
   "kind": "primary"
  },
  {
   "from": "iqft",
   "to": "cf",
   "kind": "primary",
   "label": "measure x: o"
  },
  {
   "from": "cf",
   "to": "reduce",
   "kind": "primary",
   "label": "r = ord a N",
   "mono": true
  },
  {
   "from": "reduce",
   "to": "factor",
   "kind": "secondary",
   "side": "right",
   "lane": 0,
   "label": "a factor of N"
  }
 ],
 "groups": [
  {
   "row": 2,
   "label": "orderFindingIdeal: the only quantum part"
  }
 ],
 "layers": {
  "factor": {
   "title": "Factor N",
   "role": "the problem",
   "kind": "classical",
   "summary": "<p>The input is an odd composite <code>N &gt; 2</code> that is not a prime power. Those three hypotheses are exactly the fields of <code>ShorFactoringInstance</code>, and they are what the classical reduction needs: an odd <code>N</code> with at least two distinct prime factors.</p><p>The end-to-end theorem, <code>Shor_end_to_end_factoring_approx_lowered</code>, is the whole diagram in one statement: at least half of the admissible bases <code>a</code> are good, and for every good one the lowered approximate order-finding circuit at any precision <code>η ≤ shorPrecision N x</code>, followed by the continued-fraction scan, recovers <code>r = ord a N</code> with probability at least <code>κ / (2 · log(log₂ N + 1))</code>, and <code>gcd(a^(r/2) ± 1, N)</code> is then a nontrivial factor.</p>",
   "snippets": [
    {
     "name": "ShorFactoringInstance",
     "file": "Implementation/Shor/Proofs/Support.lean",
     "line": 306,
     "code": "structure ShorFactoringInstance where\n  /-- The modulus to factor. -/\n  N : ℕ\n  /-- The modulus is odd. -/\n  odd : Odd N\n  /-- The modulus is nontrivial. -/\n  gt_two : N > 2\n  /-- The modulus is not a prime power. -/\n  not_prime_power : ∀ (p k : ℕ), Nat.Prime p → N ≠ p ^ k",
     "note": null
    },
    {
     "name": "Shor_end_to_end_factoring_approx_lowered",
     "file": "Implementation/Shor/Proofs/Correctness.lean",
     "line": 1201,
     "code": "theorem Shor_end_to_end_factoring_approx_lowered\n    [GateSemanticsFacts qs]\n    [LowerGateClass qs]\n    (T : ℕ → ℕ) (hT : ContinuedFractionSearchComplete T)\n    (fact : ShorFactoringInstance) :\n    ShorEndToEndFactoringApproxLowered T hT fact := by",
     "note": "The conclusion <code>ShorEndToEndFactoringApproxLowered</code> is defined just above it in <code>Shor/Proofs/Correctness.lean</code>; it is the conjunction described on the left."
    }
   ],
   "layers": [
    "Shor",
    "Framework"
   ]
  },
  "choose": {
   "title": "Pick a base a",
   "role": "classical, random",
   "kind": "classical",
   "summary": "<p>Choose <code>a</code> with <code>1 &lt; a &lt; N</code> and <code>gcd(a, N) = 1</code> (if the gcd is not 1, it is already a factor). The base is <em>good</em> when its order <code>r</code> is even and <code>a^(r/2) ≢ −1 (mod N)</code>.</p><p>The first half of the end-to-end theorem is the classical counting argument that at least half of the valid bases are good, <code>2 · |successful_choices N| ≥ |valid_choices N|</code>, proved by a CRT argument over two distinct prime factors in <code>Factoring_Reduction/ProbabilityBound.lean</code>.</p>",
   "snippets": [
    {
     "name": "shor_success_conditions",
     "file": "Implementation/Shor/Proofs/Math/Factoring_Reduction/Defs.lean",
     "line": 40,
     "code": "def shor_success_conditions (a r N : ℕ) : Prop :=\n  (Even r) ∧ ((a : ZMod N) ^ (r / 2) ≠ -1)",
     "note": null
    },
    {
     "name": "valid_choices, successful_choices",
     "file": "Implementation/Shor/Proofs/Math/Factoring_Reduction/Defs.lean",
     "line": 59,
     "code": "-- the set of valid a's; 1 < a < N and a coprime to N\nnoncomputable def valid_choices (N : ℕ) : Finset ℕ :=\n  (Finset.range N).filter (fun a => 1 < a ∧ Nat.gcd a N = 1)\n\n/-- The subset of valid 'a's that will successfully yield a factor. -/\nnoncomputable def successful_choices (N : ℕ) : Finset ℕ :=\n  (valid_choices N).filter (fun a => is_successful_choice a N)",
     "note": "Together with <code>is_successful_choice</code> just above them: some period of <code>a</code> meets the two success conditions."
    }
   ],
   "layers": [
    "Framework"
   ]
  },
  "hreg": {
   "title": "H on x",
   "role": "uniform superposition",
   "kind": "quantum",
   "summary": "<p>The quantum part is one circuit, <code>orderFindingIdeal</code>, four gates in sequence on two registers: the exponent register <code>x</code> of <code>log₂(2N²)</code> qubits and the data register <code>y</code> of <code>log₂(2N)</code> qubits. The first step puts <code>x</code> into the uniform superposition over all exponents.</p>",
   "snippets": [
    {
     "name": "orderFindingIdeal",
     "file": "Implementation/Shor/Proofs/Support.lean",
     "line": 324,
     "code": "noncomputable def orderFindingIdeal (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs]\n    (a N : ℕ) (x y : ExtReg) : Gate :=\n  (H_reg x.active) ;; (initY1 y.active) ;; (modExpIdeal' qs a N x.active y.active) ;; (IQFT x)",
     "note": "The circuit the correctness theorem is about. The compiled circuit, <code>orderFindingApprox</code> in the same file, has the same four steps with the verified approximate modular exponentiation in third place; <code>Policy.lowerGate</code> then turns it into <code>LowGate</code>s."
    },
    {
     "name": "H_reg",
     "file": "Implementation/ModularExponentiation/Circuit/Steps.lean",
     "line": 21,
     "code": "def H_reg (r : Reg) : Gate :=\n  (regQubits r).foldl (fun acc q => (Gate.H q) ;; acc) Gate.id",
     "note": null
    }
   ],
   "layers": [
    "Shor"
   ]
  },
  "inity": {
   "title": "y ← 1",
   "role": "data register",
   "kind": "quantum",
   "summary": "<p>Set the data register to the basis state <code>1</code> with a single <code>X</code> on its lowest qubit, so that modular exponentiation can write <code>aˣ mod N</code> into it.</p>",
   "snippets": [
    {
     "name": "initY1",
     "file": "Implementation/Shor/Statement.lean",
     "line": 217,
     "code": "def initY1 (y : Reg) : Gate :=\n  match y.qubits with\n  | [] => Gate.id\n  | q :: _ => Gate.X q",
     "note": null
    }
   ],
   "layers": [
    "Shor"
   ]
  },
  "modexp": {
   "title": "y ← aˣ mod N",
   "role": "modular exponentiation",
   "kind": "quantum",
   "summary": "<p>Controlled on each bit <code>xᵢ</code> of the exponent, multiply <code>y</code> by <code>a^(2^i) mod N</code>. This is where almost all of the gates are, and where the fast multiplication goes: each modular multiplication is built from QFT arithmetic, and each QFT from phase products.</p><p>In the ideal circuit this step is the exact gate <code>modExpIdeal'</code>. In the compiled circuit it is <code>modExpApproxValid</code>, whose error against the ideal one is bounded by <code>modExpApprox_correct</code>; that bound is what lets the success probability survive compilation.</p>",
   "snippets": [
    {
     "name": "modExpIdeal'",
     "file": "Implementation/ModularExponentiation/Circuit/ModExp.lean",
     "line": 25,
     "code": "def modExpIdeal'\n    (qs : QSemantics) [RegEncoding qs.Basis] [GateSemanticsCore qs] (a N : ℕ) (x data : Reg) :\n    Gate :=\n  modExpIdealSteps qs a N data 0 x.qubits",
     "note": null
    }
   ],
   "layers": [
    "ModularExponentiation",
    "QFT",
    "PhaseProduct"
   ]
  },
  "iqft": {
   "title": "QFT⁻¹ on x",
   "role": "inverse Fourier transform",
   "kind": "quantum",
   "summary": "<p>The inverse QFT on the exponent register turns the period of <code>x ↦ aˣ mod N</code> into peaks near multiples of <code>Q/r</code>, where <code>Q = 2^|x|</code>. The QFT is the recursive one from the QFT layer.</p>",
   "snippets": [
    {
     "name": "IQFT",
     "file": "Implementation/ModularExponentiation/Circuit/Steps.lean",
     "line": 17,
     "code": "def IQFT (r : ExtReg) : Gate :=\n  †(Gate.QFT r)",
     "note": null
    }
   ],
   "layers": [
    "QFT",
    "PhaseProduct"
   ]
  },
  "cf": {
   "title": "Measure x, continued fractions",
   "role": "classical post-processing",
   "kind": "classical",
   "summary": "<p>Measure <code>x</code> to get an outcome <code>o &lt; Q</code>. Scan the first <code>T(Q)</code> convergents of <code>o/Q</code>, keep the denominators <code>d</code> with <code>aᵈ ≡ 1 (mod N)</code>, and return the smallest; that is <code>OF_post</code>. The scan budget <code>T</code> is classical and costs no gates; <code>ContinuedFractionSearchComplete T</code> says it is long enough.</p><p><code>probability_of_success</code> sums, over all outcomes, the probability of measuring <code>o</code> times the indicator that <code>OF_post</code> returns exactly <code>r</code>. <code>Shor_correct</code> bounds it below by <code>κ / log(log₂ N + 1)</code>.</p>",
   "snippets": [
    {
     "name": "OF_post",
     "file": "Implementation/Shor/Statement.lean",
     "line": 67,
     "code": "noncomputable def OF_post (T : ℕ → ℕ) (verify : ℕ → Bool) (o Q : ℕ) : ℕ :=\n  if h : (orderCandidates T verify o Q).Nonempty then (orderCandidates T verify o Q).min' h else 0",
     "note": null
    },
    {
     "name": "probability_of_success",
     "file": "Implementation/Shor/Statement.lean",
     "line": 192,
     "code": "noncomputable def probability_of_success {qs : QSemantics} [RegEncoding qs.Basis]\n    [MeasureClass qs] {Circuit : Type} (evalC : Circuit → qs.State → qs.State) (T : ℕ → ℕ)\n    (verify : OrderVerifier) (x : Reg) (r Q : ℕ) (C : Circuit) (ψ : qs.State) : ℝ :=\n  ∑ o : Fin Q, (r_found (T := T) verify o.1 Q r) *\n    MeasureClass.probMeas (qs := qs) x o.1 (evalC C ψ)",
     "note": null
    }
   ],
   "layers": [
    "Shor",
    "Framework"
   ]
  },
  "reduce": {
   "title": "gcd(a^(r/2) ± 1, N)",
   "role": "classical reduction",
   "kind": "classical",
   "summary": "<p>With <code>r</code> even, <code>a^r − 1 = (a^(r/2) − 1)(a^(r/2) + 1) ≡ 0 (mod N)</code>, and the second success condition rules out <code>N</code> dividing the second factor; <code>N</code> cannot divide the first because <code>r</code> is the order. So <code>N</code> shares a nontrivial factor with one of them.</p>",
   "snippets": [
    {
     "name": "shors_classical_reduction",
     "file": "Implementation/Shor/Proofs/Math/Factoring_Reduction/Reduction.lean",
     "line": 75,
     "code": "theorem shors_classical_reduction (a r N : ℕ)\n(h_N : N > 2)\n(h_a : 1 < a ∧ a < N)\n(h_coprime : Nat.gcd a N = 1)\n(h_period : is_period a r N)\n(h_success : shor_success_conditions a r N) :\nis_nontrivial_factor (Nat.gcd ((a ^ (r / 2)) - 1) N) N ∨\nis_nontrivial_factor (Nat.gcd ((a ^ (r / 2)) + 1) N) N := by {",
     "note": null
    }
   ],
   "layers": [
    "Framework"
   ]
  }
 }
};
