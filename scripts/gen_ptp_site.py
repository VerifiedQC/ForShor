#!/usr/bin/env python3
"""Generate the data behind docs/phasetripleproduct/ (the PhaseTripleProduct page).

Reads the PhaseTripleProduct development, which lives in ForShor itself under
`ForShor/ShorVerification/Implementation/PhaseTripleProduct/` (Statement.lean, Proofs/, Main.lean),
plus `Model/Standard/PhaseTripleProductHeadline.lean`, and writes

    docs/phasetripleproduct/data/layers.js    window.PTP_LAYERS   the layer graph (docs/layers.js)
    docs/phasetripleproduct/data/ptpfig.js    window.PTPFIG       the recursion figure (ptpfig.js)
    docs/phasetripleproduct/data/flow.js      window.PTP_FLOW      the algorithm-flow diagram
    docs/phasetripleproduct/data/champions.js window.PTP_CHAMPIONS the benchmark's PTP targets

Everything quoted from Lean is copied verbatim from the source at the recorded file:line; the
import edges are read from the `import` lines (curated edges are asserted to be real imports);
the register contents in the figure are computed by executing the reference k = 2 table (and the
PTP node identity is re-checked numerically on it). Never edit the output by hand: re-run this script.

Inputs. The Lean sources come from a checkout of ForShor (`--suite`, a git repository). Three inputs
are NOT part of the Lean suite and still come from the ShorTableOptimization interim fork (`--sto`),
where the benchmark and the policy checker live: `leaderboard/best-known.md` (the benchmark's PTP
champions), `policies/ref_ptp_2048.json` and `scripts/ptp_exact_width.py` (the reference policy and the
Python mirror of the exact-width ladder, for the figure).

Where links point:

    --suite PATH      a ForShor checkout holding the development (default: ../ForShor-ptp)
    --repo-url URL    GitHub repository the links point at (default https://github.com/VerifiedQC/ForShor)
    --ref REF         commit/branch used in the links (default: HEAD of --suite)
    --root DIR        where ShorVerification/ sits in that repository (default ForShor/ShorVerification;
                      it is the root rather than the PhaseTripleProduct folder so that the file under
                      Model/Standard/ can be linked too)

Usage:
    python3 -I scripts/gen_ptp_site.py            # write the data files
    python3 -I scripts/gen_ptp_site.py --check    # fail if the files on disk are stale
"""
import argparse
import importlib.util
import json
import os
import random
import re
import subprocess
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
FORSHOR = os.path.dirname(HERE)
OUT = os.path.join(FORSHOR, "docs", "phasetripleproduct", "data")
DEFAULT_STO = os.path.normpath(os.path.join(
    FORSHOR, "..", "ShorTableOptimization-JMCversion", "ShorTableOptimization_temp"))
DEFAULT_SUITE = os.path.normpath(os.path.join(FORSHOR, "..", "ForShor-ptp"))
REFPOLICY = "policies/ref_ptp_2048.json"
SUITE = "Implementation/PhaseTripleProduct"      # the development's folder, relative to ShorVerification/
MODEL = "Model/Standard/PhaseTripleProductHeadline"


def K(short):
    """Key (path under ShorVerification/, no extension) of a file given relative to the PTP folder."""
    return short if short == MODEL else f"{SUITE}/{short}"


# ----------------------------------------------------------------------------------------
# Layers: which files form each block of the layer graph, and the curated text. `kind` only picks
# the tint. Ids are letters only (they go into the URL hash). The block `Framework` holds no files:
# it stands for everything the development imports from ForShor outside its own folder.
# ----------------------------------------------------------------------------------------
LAYERS = {
    "Framework": dict(kind="upstream", role="vocabulary, semantics, cost model; PhaseProduct", files=[]),
    "Statement": dict(kind="statement", role="every definition and every claim", files=["Statement"]),
    "Support": dict(kind="table", role="table-language lemmas and the Bool ↔ Prop bridges",
                    files=["Proofs/Support/Language", "Proofs/Support/Mirror"]),
    "Table": dict(kind="table", role="the contract and the width scan",
                  files=["Proofs/Table/Contract", "Proofs/Table/Width"]),
    "Values": dict(kind="table", role="the node identity and the exact widths",
                   files=["Proofs/Values/Semantics", "Proofs/Values/Exact"]),
    "Gates": dict(kind="gate", role="the leaf and one node, as gates",
                  files=["Proofs/Gates/Leaf", "Proofs/Gates/LeafSandwich", "Proofs/Gates/Node"]),
    "Recursion": dict(kind="gate", role="recursion and census at the scan widths",
                      files=["Proofs/Recursion/Census", "Proofs/Recursion/Recursion", "Proofs/Recursion/Build",
                             "Proofs/Recursion/CensusFull"]),
    "ExactBoard": dict(kind="gate", role="the same recursion at exact widths",
                       files=["Proofs/ExactBoard/ExactNode", "Proofs/ExactBoard/ExactRecursion",
                              "Proofs/ExactBoard/ExactBuild"]),
    "Accept": dict(kind="surface", role="the acceptance rule", files=["Proofs/Threshold"]),
    "Surface": dict(kind="surface", role="circuit = specification, on clean states", files=["Proofs/Surface"]),
    "Controlled": dict(kind="ext", role="controlled PTP by operand masking", files=["Proofs/Controlled"]),
    "Asymptotic": dict(kind="ext", role="O(n^log_k(3k−2)) gates", files=["Proofs/Asymptotic"]),
    "Unbalanced": dict(kind="ext", role="operands of unequal width", files=["Proofs/Unbalanced"]),
    "QubitsTight": dict(kind="ext", role="the qubit count", files=["Proofs/QubitsTight"]),
    "Witness": dict(kind="witness", role="negative controls and non-vacuity",
                    files=["Proofs/Witness/FaultChallenge", "Proofs/Witness/RecursionWitness",
                           "Proofs/Witness/ExactFault"]),
    "Main": dict(kind="main", role="the claims, proved", files=["Main"]),
    "Model": dict(kind="witness", role="the claims at ForShor's concrete model", files=[MODEL]),
}
ROWS = [["Framework"], ["Statement"], ["Support"], ["Table"], ["Values"], ["Gates"], ["Recursion"],
        ["ExactBoard"], ["Surface", "Asymptotic", "QubitsTight"], ["Accept", "Controlled", "Witness"],
        ["Unbalanced"], ["Main"], ["Model"]]

# Curated edges (dependency -> importer). Every one must be a real import edge between the blocks.
EDGES = [
    ("Framework", "Statement", "primary", "Mathlib, Framework/, PhaseProduct/Statement only", {}),
    ("Statement", "Support", "primary", "Boolean checkers", {}),
    ("Support", "Table", "primary", "contract_iff", dict(mono=True)),
    ("Table", "Values", "primary", "node_width_sound", dict(mono=True)),
    ("Values", "Gates", "primary", "node identity", dict(theorem="node_identity")),
    ("Gates", "Recursion", "primary", "evalL_ptpNode_ket", dict(mono=True)),
    ("Recursion", "ExactBoard", "primary", "PolicyImpl", dict(mono=True)),
    ("ExactBoard", "Surface", "primary", "ptp_gate_full_exact", dict(mono=True)),
    ("ExactBoard", "Asymptotic", "secondary", None, {}),
    ("ExactBoard", "QubitsTight", "secondary", None, dict(side="right", lane=0)),
    ("ExactBoard", "Witness", "secondary", None, dict(side="right", lane=1)),
    ("Surface", "Controlled", "primary", "PTPPhaseOp", dict(mono=True)),
    ("Controlled", "Unbalanced", "primary", "padding", {}),
    ("Values", "Accept", "secondary", None, dict(side="left", lane=0)),
    ("Unbalanced", "Main", "primary", None, {}),
    ("Statement", "Main", "primary", "the claims it proves", dict(side="left", lane=1)),
    ("Accept", "Main", "secondary", None, {}),
    ("Asymptotic", "Main", "secondary", None, dict(side="right", lane=2)),
    ("QubitsTight", "Main", "secondary", None, dict(side="right", lane=3)),
    ("Main", "Model", "primary", "model_ptp_lowerExact_correct", dict(mono=True)),
    ("Witness", "Model", "secondary", None, {}),
]

# Statements quoted in each panel: (declaration, file given relative to the PTP folder, note).
SNIPS = {
    "Statement": [
        ("PTPTable", "Statement", "A table: the arity \\(k\\), the interpolation points in the order the program consumes them, and the program (the Framework's <code>Prog k</code>). Nothing about PTP is in the program language; the tripling lives in what the node does with it."),
        ("PTPTable.contract", "Statement", "The admissibility check as one kernel-reducible <code>Bool</code>: \\(3k-2\\) points, pairwise distinct, each benchmark-valid, consumed in order by the program, a safe program, and registers returned to where they started. <code>Proofs/Table/Contract.lean</code> proves it equivalent to the same conditions written in the Framework's language (<code>contract_iff_framework</code>)."),
        ("PTPPolicy.check", "Statement", "A policy is a list of bands, widest first. It is accepted when the thresholds strictly decrease and every band's table passes the contract."),
        ("PolicyImpl", "Statement", "The circuits the claims are about: a gate-level recursion following a policy."),
        ("PTPLowerExactCorrect", "Statement", "The headline claim, as a proposition. <code>Main.lean</code> proves it as <code>ptp_lowerExact_correct</code>."),
    ],
    "Support": [
        ("checkedProg_iff_framework", "Proofs/Support/Language", "The Statement's Boolean checkers (<code>progConsumesPts?</code>, <code>safeProg?</code>, <code>returnsToStartCheck</code>) are equivalent to the Framework's propositions."),
        ("pairwise_distinct_of_nodup", "Proofs/Support/Mirror", "Distinct normalised points are pairwise distinct as projective points, which is what makes the interpolation matrix invertible."),
    ],
    "Table": [
        ("contract_iff", "Proofs/Table/Contract", "<code>contract</code> is exactly the table conditions: a valid point list (count \\(3k-2\\), distinct, valid) and a safe, consuming program."),
        ("contract_iff_framework", "Proofs/Table/Contract", "The same, in the Framework's own language (<code>ProgConsumesPts</code>, <code>SafeProg</code>, <code>run?</code>)."),
        ("node_width_sound", "Proofs/Table/Width", "At the scanned width no register write ever wraps, so wrapping and exact arithmetic agree."),
    ],
    "Values": [
        ("node_identity", "Proofs/Values/Semantics", "The PTP node identity. A product of three degree-\\((k-1)\\) limb polynomials has degree \\(3(k-1)\\), so its value at the radix is a fixed rational combination of its values at \\(3k-2\\) distinct points. This is the whole reason the recursion works."),
        ("coeff_eq_interpCoeff", "Proofs/Values/Semantics", "The interpolation weight, defined directly in the Statement as a matrix inverse, is the one the identity is proved with (by <code>rfl</code>)."),
        ("ptpTightWidth_spec", "Proofs/Values/Exact", "The exact width: the least \\(W\\) whose signed range holds every value the table can produce (<code>tight_fits</code> that it suffices; <code>tight_le_childWidth</code> that it never exceeds the scan)."),
        ("tight_minimal", "Proofs/Values/Exact", "And that it is minimal: one bit fewer and some operand that fits \\(n\\) bits has a reachable register value that does not fit."),
    ],
    "Gates": [
        ("evalL_ptpLeafSandwich_ket", "Proofs/Gates/LeafSandwich", "The leaf (defined in the Statement) multiplies a basis state by the product phase, with no workspace hypothesis beyond two clean ancillas. One rotation per cell."),
        ("evalL_ptpNode_ket", "Proofs/Gates/Node", "One level, on a basis state: three <code>LowGate</code>s per table operation (one per operand), a child on each triple of slot registers, angle \\(\\varphi\\,c_t\\). The node multiplies by \\(\\exp(i\\pi\\varphi\\,x_0x_1x_2)\\) and returns the basis state unchanged. Children here are leaves on pre-split slots; whole policies are the next layer."),
    ],
    "Recursion": [
        ("PolicyImpl.specOn", "Proofs/Recursion/Recursion", "Correctness at every depth: a node over children that meet the phase specification meets it, given a clean reserve."),
        ("ptp_gate_full", "Proofs/Recursion/CensusFull", "Existence for every checked policy and width, with the resource census (Rz, Toffoli, X, H, CNOT, And†) and a qubit bound."),
    ],
    "ExactBoard": [
        ("WidthRule", "Statement", "The recursion is generic in the width rule; <code>exactRule</code> is <code>ptpTightWidth</code>, <code>scanRule</code> the conservative scan."),
        ("ptp_gate_full_exact", "Proofs/ExactBoard/ExactBuild", "The same existence, correctness and census at exact widths. This is the board the headline theorem and the gate-count theorem use."),
    ],
    "Accept": [
        ("PTPPolicy.chainContractsTight_iff_reach", "Proofs/Threshold", "Beyond <code>check</code>: every table chosen at every width the exact recursion from \\(n\\) reaches has \\(k \\le m\\) and strictly shrinks the width. A band that fails this is rejected, which is what keeps degenerate bands from being claimed as recursion."),
    ],
    "Surface": [
        ("PTPPhaseOp", "Statement", "The specification operator the reader supplies: a linear map acting on each basis ket as \\(\\exp(i\\pi\\varphi\\,x_0x_1x_2)\\). Nothing in it mentions <code>LowGate</code>, so the claim is independent of the circuit."),
        ("evalL_policyImplD_state", "Proofs/Surface", "The state-level step: the circuit equals the specification operator on the whole clean closure, by linearity from the basis-ket case."),
    ],
    "Controlled": [
        ("PTPCtlLowerExactCorrect", "Statement", "A controlled PTP by <em>masking</em>: copy the control into a fresh operand \\(Y = c \\wedge X_0\\), run the uncontrolled circuit, unmask. It costs \\(2n\\) Toffolis (\\(n\\) of them \\(\\dagger\\)), \\(n+1\\) extra qubits, no extra rotations."),
        ("ptp_ctl_lowerExact_correct_core", "Proofs/Controlled", "The proof; <code>Main.lean</code> re-states it under the claim's name."),
    ],
    "Asymptotic": [
        ("ptpExponent", "Statement", "The exponent \\(\\log_k(3k-2)\\)."),
        ("PTPGateTotalBound", "Statement", "For a constant policy (one table at every width), the exact-board gate count is \\(O(n^{\\log_k(3k-2)})\\), by ForShor's shifted master theorem (proved in <code>Proofs/Asymptotic.lean</code>)."),
        ("PTPCircuitGateCountBound", "Statement", "And some circuit following the constant policy has that many gates. The claim is existential: it does not itself say the circuit is correct or that it is the circuit of <code>PTPLowerExactCorrect</code>."),
    ],
    "Unbalanced": [
        ("PTPPadLowerExactCorrect", "Statement", "Operands of different widths: sign-extend each in place into a clean reserve to the common width \\(n\\), run the balanced circuit, undo. The extension costs \\(2(d_0+d_1+d_2)\\) CNOTs. A native unbalanced node is not built."),
    ],
    "QubitsTight": [
        ("PTPQubitsTight", "Statement", "There is a circuit following the policy touching at most \\(3n + \\texttt{ptpWsTD}\\) distinct qubits (children share one workspace pool)."),
        ("PTPQubitsLePtpQubits", "Statement", "<code>ptpQubits</code> is a proved <em>upper bound</em> at the scan rule. It bounds <code>usedQubits</code>, not the framework's <code>qubitCount</code>, which adds <code>cleanAnc</code>."),
    ],
    "Witness": [
        ("faulty_rejected", "Proofs/Witness/FaultChallenge", "Negative control: a table whose points are declared in the wrong order is rejected by the contract (and evaluated anyway it gives the wrong value, <code>faulty_wrong</code>)."),
        ("gate_fault_wrong", "Proofs/Witness/ExactFault", "One bit below the exact width the gate-level circuit is <em>wrong</em>, on a concrete state. The width is load-bearing."),
        ("impl_hyps_sat", "Proofs/Witness/RecursionWitness", "Non-vacuity: a concrete depth-one recursion on three 20-qubit registers meets every structural hypothesis."),
    ],
    "Main": [
        ("ptp_lowerExact_correct", "Main", "The headline theorem. Its statement is the proposition <code>PTPLowerExactCorrect</code> of the Statement; it is assembled here from <code>ptp_gate_full_exact</code> and <code>evalL_policyImplD_state</code>."),
        ("ptp_ctl_lowerExact_correct", "Main", "The other theorems are re-statements of the <code>_core</code> theorems of <code>Proofs/</code>, each as exactly its claim."),
        ("ptp_pad_lowerExact_correct", "Main", None),
        ("ptp_gateTotal_bound", "Main", None),
        ("ptp_circuit_gateCount_bound", "Main", None),
        ("ptp_qubits_tight", "Main", None),
        ("ptp_qubits_tight_exact", "Main", None),
        ("ptp_qubits_le_ptpQubits", "Main", None),
        ("ptp_chainContractsTight_iff_reach", "Main", None),
    ],
    "Model": [
        ("model_ptp_lowerExact_correct", MODEL, "The headline claim specialised to ForShor's concrete <code>Model.qs</code>, with the specification operator built by <code>diagLift</code>: the hypotheses are satisfiable."),
        ("model_witness_correct", MODEL, "And the concrete \\(k=2\\) witness meets it."),
    ],
}

# The claims, in the order of the Statement, with the theorem of Main.lean that proves each.
CLAIMS = [
    ("PTPLowerExactCorrect", "ptp_lowerExact_correct"),
    ("PTPCtlLowerExactCorrect", "ptp_ctl_lowerExact_correct"),
    ("PTPPadLowerExactCorrect", "ptp_pad_lowerExact_correct"),
    ("PTPGateTotalBound", "ptp_gateTotal_bound"),
    ("PTPCircuitGateCountBound", "ptp_circuit_gateCount_bound"),
    ("PTPQubitsTight", "ptp_qubits_tight"),
    ("PTPQubitsTightExact", "ptp_qubits_tight_exact"),
    ("PTPQubitsLePtpQubits", "ptp_qubits_le_ptpQubits"),
    ("PTPChainContractsTightIffReach", "ptp_chainContractsTight_iff_reach"),
]

# Curated prose per block. Files, sizes and links are appended by the script.
SUMMARY = {
    "Framework": "<p>What the development is built on. <code>Statement.lean</code> imports only Mathlib, <code>Framework/</code> and <code>PhaseProduct/Statement.lean</code>: ForShor's gate language <code>LowGate</code>, its semantics classes (<code>QSemantics</code>, <code>LowerGateClass</code>), its resource model <code>shorGateResourceModel</code> (Cuccaro adders, arbitrary-angle rotations, not T), and the table language of <code>Framework/ToomCookTable.lean</code> (<code>Register</code>, <code>State</code>, <code>Point</code>, <code>valid_ops</code>, <code>Prog</code>, <code>run?</code>). The proofs may import more: ForShor's phase-product lemmas (<code>PhaseProduct/Proofs/</code>: the naive leaf, the basis-level gate laws, the register lemmas, the master theorem). Nothing in the order-finding development imports it: the only importers are <code>ForShor.lean</code> (the library root) and <code>Model/Standard/PhaseTripleProductHeadline.lean</code>.</p><p>The Statement imports: {FSTATEMENT}.</p><p>The proofs additionally import: {FPROOFS}.</p><p>The model headline imports: {FMODEL}.</p>",
    "Statement": "<p><strong>Read this first.</strong> Every definition the claims mention, and the claims themselves as propositions, and nothing else. The definitions are plain data; their invariants are stated and proved in <code>Proofs/</code>. A reader who wants to know what is claimed needs only this file and <code>Main.lean</code>; building <code>Main.lean</code> is the guarantee that each claim is proved.</p><p>The rule that makes this true, that the file imports only Mathlib, <code>Framework/</code> and other <code>Statement.lean</code> files, is checked semantically rather than by reading the imports: <a href=\"{SCRIPT_CLOSURE}\"><code>scripts/StatementClosure.lean</code></a> computes every constant the claims reach, unfolding definitions, and fails if one lives anywhere else, so a definition cannot hide in a proof file. CI runs it.</p><p>The claims, and the theorems of <code>Main.lean</code> that prove them:</p>{CLAIMSTABLE}<p>The file's sections, in the order a reader needs them:</p>{OUTLINE}",
    "Support": "<p>The table-language lemmas the PTP proofs use. The Statement defines the contract as a Boolean (a decision procedure is needed to check a policy), while the Framework states the same conditions as propositions; <code>Language</code> proves each checker equivalent to its proposition (<code>safeProg?_iff</code>, <code>progConsumesPts?_iff</code>, <code>checkedProg_iff_framework</code>) together with <code>statesEqual_iff</code>, <code>returnsToStartCheck_iff</code> and <code>sortedDesc_iff</code>. <code>Mirror</code> holds the interpolation facts (<code>pointRowQ_good</code>, <code>pairwise_distinct_of_nodup</code>, <code>toomCook_exact</code>, <code>sum_limbs</code>).</p>",
    "Table": "<p>The PTP table contract and the width scan, as lemmas about the Statement's definitions. A node takes <em>three</em> operands, each split into \\(k\\) limbs, so the interpolation needs \\(3(k-1)+1 = 3k-2\\) points instead of PhaseProduct's \\(2k-1\\).</p><p><code>Contract</code> proves <code>contract_iff</code> and <code>contract_iff_framework</code>, the choice and check lemmas, and <code>pointCount_eq</code>. <code>Width</code> runs the table's program on magnitude bounds, separately for the three operands, and shows that at the resulting width no register write wraps (<code>node_width_sound</code>).</p>",
    "Values": "<p>The mathematics, before any gate. <code>node_identity</code> is the Toom–Cook identity for three factors, <code>evalPhase</code> the recursive semantics, <code>evalPhase_correct</code> (and the wrapping and exact-width variants) that the recursion computes \\(\\varphi\\,x_0x_1x_2\\).</p><p><code>Exact</code> replaces the scan by the <em>least</em> width that works, <code>ptpTightWidth</code> (defined in the Statement): it runs the program on coefficient rows, takes the largest demand on a signed register, and is proved sound, minimal and never larger than the scan.</p>",
    "Gates": "<p>One recursion level in ForShor's <code>LowGate</code>. The leaf and the node are defined in the Statement; this layer proves what they do. The node holds \\(3k\\) slot registers; each table operation becomes three gates, one per operand; the \\(t\\)-th <code>phaseProduct i</code> becomes a child on the triple <code>(slot 0 i, slot 1 i, slot 2 i)</code> at angle \\(\\varphi\\,c_t\\).</p><p>The base case is the sandwich leaf (<code>LeafSandwich</code>). <code>Leaf</code> keeps the earlier doubly-controlled-phase leaf as a documented alternative with all its theorems; no claim mentions it, so its definitions live in that proof file.</p><p><em>Not covered here:</em> splitting three parent registers into slots, reserve management, children that are themselves nodes, any controlled variant. Those are the next layers.</p>",
    "Recursion": "<p>From one node to a whole policy, at the conservative scan widths. <code>SplitLayout</code> splits three registers in place into child slots (zero-extending lower limbs, sign-extending the top), <code>SpecOn</code> is the register-level phase contract with explicit workspace, and <code>PolicyImpl</code> is the recursion. Correctness and the census hold at every depth (<code>Recursion</code>, <code>Census</code>), exist for every checked policy and width (<code>Build</code>), and include CNOT and And† counts and a qubit bound (<code>CensusFull</code>).</p>",
    "ExactBoard": "<p>The same recursion with the width rule abstracted (<code>WidthRule</code>, with <code>exactRule</code> and <code>scanRule</code>), so one development serves both boards: <code>PolicyImplD</code>, <code>ptp_gate_full_D</code>, and <code>ptp_gate_full_exact</code> at exact widths.</p>",
    "Accept": "<p>A policy can pass <code>check</code> and still be degenerate: a band whose table does not shrink the width would be claimed as recursion and then silently take the leaf. <code>chainContractsTight</code> closes that: every band the exact recursion from \\(n\\) selects must apply at a width \\(\\ge k\\) and strictly shrink it. <code>chainContractsTight_iff_reach</code> states the rule without the ladder.</p>",
    "Surface": "<p>The claim a reader should check, stated apart from the proof. The specification operator is a structure the reader supplies, so the statement does not mention <code>LowGate</code>. The claim covers the linear span of <em>clean</em> basis kets: operands fit signed \\(n\\ge1\\) bits and the workspace is \\(|0\\rangle\\). For \\(n=0\\) no ket is clean and the state-level conjunct is vacuous (the circuit, the workspace bound and the census are still required). This layer proves the lemmas that lift the basis-ket case to every clean state.</p>",
    "Controlled": "<p>A controlled PTP built by <em>masking</em> one operand. This is not ForShor's construction, which controls every leaf phase; that variant is <strong>not</strong> proved here. On the clean subspace, the control may overlap the other registers in a degenerate way (then the circuit is the identity on the clean span), which the claim's docstring states. The final theorem is <code>ptp_ctl_lowerExact_correct_core</code>; <code>Main.lean</code> re-states it as <code>ptp_ctl_lowerExact_correct</code>.</p>",
    "Asymptotic": "<p>The PTP analogue of ForShor's PhaseProduct gate-count theorem, under the same hypothesis: a <strong>constant policy</strong>, one table at every width. The exponent is \\(\\log_k(3k-2)\\): 2.000 at \\(k=2\\), 1.771 at \\(k=3\\), 1.661 at \\(k=4\\), tending to 1. The count is <code>rz + toffoli + x + h + cnot</code> under <code>shorGateResourceModel</code>, not a T count. Both claims of this layer are proved as <code>_core</code> theorems here and re-stated in <code>Main.lean</code>.</p>",
    "Unbalanced": "<p>Operands of unequal width, handled by padding rather than a native unbalanced node. Open: a native node, the least width at which the wrapping semantics is correct, and the leaf-control variant.</p>",
    "QubitsTight": "<p>The circuit names at most \\(3n + \\texttt{ptpWsTD}\\) qubits, with \\(\\texttt{ptpWsTD} = 3(k\\,C' - n)\\) per node and one shared pool. This is not the framework's <code>qubitCount</code>: the Cuccaro/negation scratch <code>cleanAnc</code> of the recursive circuit is not bounded here. <code>ptpQubits</code> is also loose by up to a factor \\(k\\) per level (private per-child workspace versus the shared pool). The claims are existential: some circuit following the policy has that qubit count.</p>",
    "Witness": "<p>Why the theorems are not vacuous, and why the hypotheses are needed. <code>FaultChallenge</code> is the negative control: a point-order fault the contract rejects (and which gives the wrong value if evaluated anyway: \\(B^3+3B^2-5B+1\\) rather than \\((B+1)^3\\) at \\(x=y=z=B+1\\)), and a width fault (wrapping the registers one bit below the scan width corrupts a child operand). <code>RecursionWitness</code> assembles a concrete \\(k=2\\) gate-level recursion on three 20-qubit registers (child width 14), every structural hypothesis discharged by <code>decide</code>. <code>ExactFault</code> shows that one bit below the <em>exact</em> width the gate-level circuit is wrong on a concrete state.</p>",
    "Main": "<p>Proves every claim of the Statement. Each theorem has the name of the claim it proves, in lower case, and is stated as exactly that proposition, so what is proved is what the Statement says. For the extensions the work is done in <code>Proofs/</code> by a theorem with a <code>_core</code> suffix, and <code>Main.lean</code> re-states it. The headline <code>ptp_lowerExact_correct</code> is assembled here from <code>ptp_gate_full_exact</code> and <code>evalL_policyImplD_state</code>.</p><p>The claims, their statements and their proofs:</p>{CLAIMSTABLE}",
    "Model": "<p>Non-vacuity at the concrete model. <code>Model/Standard/PhaseTripleProductHeadline.lean</code> specialises the typeclass stack of the headline claims to ForShor's <code>Model.qs</code>, builds the specification operators there with <code>diagLift</code> (<code>modelPhaseOp</code>, <code>modelCtlPhaseOp</code>), and states the two state-level claims at the model (<code>model_ptp_lowerExact_correct</code>, <code>model_ptp_ctl_lowerExact_correct</code>) together with the concrete \\(k=2\\) witness (<code>model_witness_correct</code>). Like ForShor's other model headlines it reaches into <code>Implementation/</code>, and nothing outside <code>Model/</code> imports it.</p>",
}


# ----------------------------------------------------------------------------------------
# Lean parsing
# ----------------------------------------------------------------------------------------
DECL_RE = re.compile(r"^(\s*)(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                     r"(theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+([^\s(:{\[]+)")


def read(p):
    with open(p, encoding="utf-8") as f:
        return f.read()


def parse(path):
    text = read(path)
    lines = text.splitlines()
    ns, decls = [], []
    for i, ln in enumerate(lines, 1):
        m = re.match(r"^namespace\s+(\S+)", ln)
        if m:
            ns.append(m.group(1)); continue
        m = re.match(r"^end\s+(\S+)\s*$", ln)
        if m and ns and ns[-1] == m.group(1):
            ns.pop(); continue
        d = DECL_RE.match(ln)
        if d:
            decls.append(dict(kind=d.group(2), name=".".join(ns + [d.group(3)]), line=i))
    imports = re.findall(r"^import\s+(\S+)", text, re.M)
    doc = re.search(r"/-!(.*?)-/", text, re.S)
    title = None
    if doc:
        t = re.search(r"^#\s+(.+)$", doc.group(1), re.M)
        title = t.group(1).strip() if t else None
    return dict(lines=lines, decls=decls, imports=imports, title=title, n=len(lines))


def statement(P, qual):
    """Verbatim statement of declaration `qual` (suffix match): docstring, header, up to `:=`."""
    lines = P["lines"]
    hits = [d for d in P["decls"] if d["name"] == qual or d["name"].endswith("." + qual)]
    if not hits:
        raise SystemExit(f"declaration not found: {qual}")
    d = hits[0]
    start = d["line"] - 1
    s = start
    if start > 0 and lines[start - 1].rstrip().endswith("-/"):      # contiguous doc comment
        j = start - 1
        while j >= 0 and not lines[j].lstrip().startswith("/--"):
            j -= 1
        if j >= 0:
            s = j
    out = []
    is_thm = d["kind"] in ("theorem", "lemma")
    depth = 0
    for k in range(s, min(len(lines), start + 40)):
        ln = lines[k]
        if k > start and not is_thm and ln.strip() == "":
            break                                   # a definition: its whole body, to the blank line
        if k > start and DECL_RE.match(ln) and not ln.startswith(" "):
            break
        if is_thm and k >= start:
            cut = None
            for i, ch in enumerate(ln):
                if ch in "([{⟨":
                    depth += 1
                elif ch in ")]}⟩":
                    depth -= 1
                elif ch == ":" and ln[i:i + 2] == ":=" and depth == 0 and not re.match(r"\s*(let|have|set)\b", ln):
                    cut = i
                    break
            if cut is not None:
                rest = ln[cut + 2:].strip()
                out.append(ln[:cut + 2] + (" by" if rest.startswith("by") else " …"))
                break
        out.append(ln)
    while out and out[-1].strip() == "":
        out.pop()
    return d, "\n".join(out)


def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


# ----------------------------------------------------------------------------------------
# The reference table, executed (the figure's register contents)
# ----------------------------------------------------------------------------------------
SUB = "₀₁₂₃₄₅₆₇₈₉"


def poly_str(v, names):
    parts = []
    for c, nm in zip(v, names):
        if c == 0:
            continue
        a = abs(c)
        term = nm if a == 1 else f"{a}{nm}"
        parts.append(("−" if c < 0 else "+") + term)
    s = "".join(parts) if parts else "0"
    s = re.sub(r"^\+", "", s)
    return re.sub(r"([^\s])([+−])", r"\1 \2 ", s) if len(parts) > 1 else s


def run_table(k, ops):
    regs = [[Fraction(int(i == j)) for j in range(k)] for i in range(k)]
    seg, cur = [], []
    states = []
    for op in ops:
        if op[0] == "addScaled":
            _, dst, src, sg, sh = op
            cur.append((op, [r[:] for r in regs]))
            regs[dst] = [a + sg * b * (2 ** sh) for a, b in zip(regs[dst], regs[src])]
        elif op[0] == "phaseProduct":
            if cur:
                seg.append(("U", cur)); cur = []
            seg.append(("PP", [op[1], [r[:] for r in regs]]))
        else:
            raise SystemExit(f"unsupported op in the figure's table: {op}")
    if cur:
        seg.append(("U", cur))
    return seg, regs


def interp_coeffs(pts, k):
    """c_t(B) = sum_j W[t][j] B^j with  c^T V = u^T, V[t][j] = a_t^j b_t^(3k-3-j)."""
    q = 3 * k - 2
    deg = 3 * (k - 1)
    V = []
    for p in pts:
        a, b = (Fraction(1), Fraction(0)) if p == "inf" else (Fraction(int(p)), Fraction(1))
        V.append([a ** j * b ** (deg - j) for j in range(q)])
    # invert V
    n = q
    M = [row[:] + [Fraction(int(i == j)) for j in range(n)] for i, row in enumerate(V)]
    for c in range(n):
        piv = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    inv = [row[n:] for row in M]
    # c = V^{-T} u  ->  c_t = sum_j inv[j][t] B^j
    return [[inv[j][t] for j in range(q)] for t in range(q)]


def coeff_tex(w):
    terms = []
    for j, c in enumerate(w):
        if c == 0:
            continue
        pw = "" if j == 0 else ("B" if j == 1 else f"B^{j}")
        terms.append((c, pw))
    num = Fraction(1)
    den = 1
    for c, _ in terms:
        den = den * c.denominator // __import__("math").gcd(den, c.denominator)
    s = ""
    for c, pw in terms:
        v = c * den
        a = abs(v)
        mag = (str(int(a)) if (pw == "" or a != 1) else "") + pw
        s += ("-" if v < 0 else ("+" if s else "")) + mag
    return s if den == 1 else f"({s})/{den}"


def build_fig(sto, policy):
    sys.path.insert(0, os.path.join(sto, "scripts"))
    spec = importlib.util.spec_from_file_location("ptp_exact_width", os.path.join(sto, "scripts", "ptp_exact_width.py"))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    n = 2048
    ladder = mod.exact_ladder(policy, n)
    scan = mod.scan_ladder(policy, n)
    bands = [dict(threshold=b["threshold"], k=b["k"]) for b in policy["bands"]]

    def band_of(w):
        for i, b in enumerate(bands):
            if b["threshold"] <= w:
                return i
        return -1
    levels = [dict(w=w, k=k, band=band_of(w) if k else -1) for w, k in ladder]
    # the k = 2 table of the third band
    tb = policy["bands"][2]
    k, ops, pts = tb["k"], tb["operations"], tb["point_order"]
    assert k == 2 and pts == ["1", "0", "-1", "inf"]
    seg, final = run_table(k, ops)
    assert [list(map(int, r)) for r in final] == [[1, 0], [0, 1]], "table must return the registers"
    names = ["x₀", "x₁"]
    segs, pps, ppi = [], [], 0
    for kind, body in seg:
        if kind == "U":
            segs.append(dict(kind="U", name=f"U{sum(1 for s in segs if s['kind']=='U')}",
                             ops=[f"{o[0]} dst={o[1]} src={o[2]} {'neg' if o[3] < 0 else 'pos'} sh={o[4]}" for o, _ in body],
                             math=[f"r{o[1]} {'−=' if o[3] < 0 else '+='} " + (f"{2**o[4]}·" if o[4] else "") + f"r{o[2]}" for o, _ in body],
                             before=[poly_str(r, names) for r in body[0][1]],
                             after=None))
        else:
            reg, state = body
            ppi += 1
            pps.append(dict(n=ppi, reg=reg, point=pts[ppi - 1].replace("inf", "∞").replace("-", "−"),
                            x=poly_str(state[reg], ["x₀", "x₁"]),
                            y=poly_str(state[reg], ["y₀", "y₁"]),
                            z=poly_str(state[reg], ["z₀", "z₁"]),
                            row=[str(int(c)) for c in state[reg]]))
            segs.append(dict(kind="PP", count=1, pp=ppi))
    # states after each U segment (replay)
    regs = [[Fraction(int(i == j)) for j in range(k)] for i in range(k)]
    ui = 0
    for s in segs:
        if s["kind"] != "U":
            continue
    regs = [[Fraction(int(i == j)) for j in range(k)] for i in range(k)]
    idx = 0
    for kind, body in seg:
        if kind == "U":
            for o, _ in body:
                _, dst, src, sg, sh = o
                regs[dst] = [a + sg * b * (2 ** sh) for a, b in zip(regs[dst], regs[src])]
            s = [x for x in segs if x["kind"] == "U"][idx]
            s["after"] = [poly_str(r, names) for r in regs]
            idx += 1
    # interpolation weights and a numeric re-check of the node identity on this table
    W = interp_coeffs(pts, k)
    coeffs = [coeff_tex(w) for w in W]
    rnd = random.Random(7)
    for _ in range(50):
        Wd = rnd.randint(2, 12)
        B = 2 ** Wd
        x = [[rnd.randint(-5 * B, 5 * B) for _ in range(k)] for _ in range(3)]
        tot = Fraction(0)
        for t, p in enumerate(pts):
            prod = Fraction(1)
            for s in range(3):
                a, b = (Fraction(1), Fraction(0)) if p == "inf" else (Fraction(int(p)), Fraction(1))
                prod *= sum(x[s][j] * a ** j * b ** (k - 1 - j) for j in range(k))
            tot += sum(c * B ** j for j, c in enumerate(W[t])) * prod
        want = Fraction(1)
        for s in range(3):
            want *= sum(x[s][j] * B ** j for j in range(k))
        assert tot == want, "PTP node identity failed on the figure's table"
    for p, c in zip(pps, coeffs):
        p["coeff"] = c
    arith = sum(1 for o in ops if o[0] != "phaseProduct")
    layers = 0
    prev_pp = False
    for o in ops:
        is_pp = o[0] == "phaseProduct"
        if is_pp and not prev_pp:
            layers += 1
        prev_pp = is_pp
    return dict(policy=dict(name=policy["name"], n=n, bands=bands, levels=levels,
                            scan=[dict(w=w, k=kk) for w, kk in scan]),
                k=k, q=3 * k - 2, points=[p.replace("inf", "∞").replace("-", "−") for p in pts],
                segments=segs, pps=pps, arithmetic=arith, layers=layers, score=arith + 5 * layers,
                tableOps=[list(o) for o in ops])


def champions(sto):
    rows = {}
    for ln in read(os.path.join(sto, "leaderboard", "best-known.md")).splitlines():
        m = re.match(r"\|\s*`(PhaseProduct|PhaseTripleProduct)`\s+`k=(\d+)`\s*\|\s*\*\*(\d+)\*\*\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|\s*(\d+)", ln)
        if m:
            rows.setdefault(m.group(1), {})[int(m.group(2))] = [int(m.group(i)) for i in range(3, 9)]
    return rows



# ----------------------------------------------------------------------------------------
# The PTP algorithm flow (the counterpart of the Shor flow on the project page): one node of the
# recursion, as steps. Same data shape as the layer graph; no `imports`.
# ----------------------------------------------------------------------------------------
FLOW_ROWS = [["input"], ["choose"], ["split", "leaf"], ["evaluate"], ["children"], ["restore"], ["count"]]
FLOW_EDGES = [
    ("input", "choose", "primary", "width n", {}),
    ("choose", "split", "primary", "shrinks w", {}),
    ("choose", "leaf", "primary", "none", {}),
    ("split", "evaluate", "primary", "k limbs each", {}),
    ("evaluate", "children", "primary", "a point reached", {}),
    ("children", "restore", "primary", "3k − 2 products done", {}),
    ("children", "choose", "primary", "each child: width w′ < w", dict(side="left", lane=0)),
    ("restore", "count", "primary", None, {}),
    ("leaf", "count", "secondary", None, dict(side="right", lane=0)),
]
FLOW = {
    "input": dict(title="Three registers", role="the problem", kind="classical",
        summary=r"""<p>Three \(n\)-qubit registers holding signed integers \(x, y, z\), an angle \(\varphi\), and a clean workspace. The goal is the operator that multiplies each basis ket by \(\exp(i\pi\varphi\,xyz)\) and does nothing else.</p><p>The statement is written without any circuit: <code>PTPPhaseOp</code> is a linear map the reader supplies, required only to act on every basis ket as <code>ptpEigenphase</code>. The theorem <code>ptp_lowerExact_correct</code> says a circuit built by the steps below equals it on every <em>clean</em> state. The rest of this diagram is how that circuit is built, one node at a time.</p>""",
        snips=[("ptpEigenphase", "Statement", None), ("PTPPhaseOp", "Statement", None)]),
    "choose": dict(title="Choose a table", role="the policy", kind="classical",
        summary=r"""<p>The policy is a list of bands, widest first. At the current width \(w\) it returns the table of the first band whose threshold is at most \(w\), or nothing. The node is a <em>leaf</em> if there is no table, and also if the table would not shrink the width, so the recursion cannot fail to terminate.</p><p>The policy is checked once, before any circuit exists: thresholds strictly decrease and every table passes the contract (\(3k-2\) distinct points, consumed in order, registers returned to start). A stronger rule, <code>chainContractsTight</code>, requires every band the recursion reaches to shrink the width.</p>""",
        snips=[("PTPPolicy.choose", "Statement", None), ("PTPPolicy.check", "Statement", None)]),
    "split": dict(title="Split into limbs", role="three operands", kind="quantum",
        summary=r"""<p>Each operand is split in place into \(k\) limbs of about \(n/k\) bits: the lower limbs zero-extended and the top limb sign-extended to the child width \(C'\) (at exact widths, \(\mathtt{ptpTightWidth}\)), using a clean reserve. The three operands give \(3k\) slot registers, laid out so that no two overlap.</p><p>The width matters: it is the least one at which no register in the program ever overflows. One bit fewer and the circuit is provably wrong on a concrete state (<code>gate_fault_wrong</code>).</p>""",
        snips=[("SplitLayout", "Statement", None), ("ptpTightWidth_spec", "Proofs/Values/Exact", None)]),
    "leaf": dict(title="Sandwich leaf", role="the base case", kind="quantum",
        summary=r"""<p>Where the recursion stops, the product is computed directly. For each pair of bits of \(y\) and \(z\), a Toffoli writes their product into a clean ancilla; one rotation then applies the phase for every bit of \(x\); the Toffoli is undone. One rotation per cell instead of five for the doubly-controlled phase it replaced.</p><p>The leaf costs \(O(n^3)\) cells at width \(n\), so the policy should take it only at small widths.</p>""",
        snips=[("ptpLeafSandwich", "Statement", None)]),
    "evaluate": dict(title="Evaluate at a point", role="register arithmetic", kind="quantum",
        summary=r"""<p>The table's program runs on the limb registers: additions of shifted registers, negations, shifts. Every operation is emitted three times, once per operand, so \(x\), \(y\) and \(z\) are moved to the same interpolation point together. When the program reaches a <code>phaseProduct i</code> checkpoint, register \(i\) of each operand holds that point's value; that is the contract's consumption condition.</p>""",
        snips=[("opGates", "Statement", None)]),
    "children": dict(title="A smaller PTP per point", role="the recursion", kind="quantum",
        summary=r"""<p>At each of the \(3k-2\) checkpoints a phase triple product is taken on the three registers just prepared, at angle \(\varphi\,c_t\), where \(c_t\) is the point's interpolation weight at the limb radix. Each is the same problem at the smaller width, so control returns to <em>Choose a table</em> with \(w' < w\).</p><p>That the weighted sum is right is <code>node_identity</code>: \(\sum_t c_t\prod_s x_s(p_t) = x_0x_1x_2\). Children run one after another and share one workspace pool, which keeps the qubit count at \(3n\) plus a workspace term (<code>ptpWsTD</code>) instead of one workspace per child.</p>""",
        snips=[("ptpSubNode", "Statement", None), ("node_identity", "Proofs/Values/Semantics", None)]),
    "restore": dict(title="Undo and merge", role="clean up", kind="quantum",
        summary=r"""<p>The program's last stretch returns every limb register to its own limb (<code>returnsToStartCheck</code>, part of the contract), and the split is undone. The net effect of the node on a basis state is the single phase \(\exp(i\pi\varphi\,xyz)\), with the basis state otherwise unchanged. <code>evalL_ptpNode_ket</code> states this for one node over leaf children; <code>PolicyImpl.specOn</code> lifts it through the whole recursion.</p>""",
        snips=[("evalL_ptpNode_ket", "Proofs/Gates/Node", None), ("PolicyImpl.specOn", "Proofs/Recursion/Recursion", None)]),
    "count": dict(title="Count the gates", role="the cost", kind="classical",
        summary=r"""<p>The circuit's gates are counted exactly, by a census that follows the recursion (<code>ptp_gate_full_exact</code>): rotations, Toffolis, X, H, CNOTs and the number of uncomputing Toffolis. For a <em>constant</em> policy (one table at every width) the total is \(O(n^{\log_k(3k-2)})\): a node does work linear in its width and has \(3k-2\) children of about a \(k\)-th of it, and ForShor's shifted master theorem solves that recurrence. The count is in <code>shorGateResourceModel</code>, not T gates.</p>""",
        snips=[("ptpExponent", "Statement", None), ("PTPGateTotalBound", "Statement", None)]),
}



def src_path(suite, root, key):
    return os.path.join(suite, root, key + ".lean")


def get_info(cache, suite, root, key):
    if key not in cache:
        cache[key] = parse(src_path(suite, root, key))
    return cache[key]


def edge_dict(a, b, kind, lab, opt):
    e = {"from": a, "to": b, "kind": kind}
    if lab:
        e["label"] = lab
    for key in ("mono", "theorem", "side", "lane"):
        if key in opt:
            e[key] = opt[key]
    return e


def build_flow(cache, suite, root, blob):
    layers = {}
    for lid, F in FLOW.items():
        snips = []
        for name, f, note in F["snips"]:
            key = K(f)
            d, code = statement(get_info(cache, suite, root, key), name)
            e = dict(name=name, file=key + ".lean", line=d["line"], code=code)
            if note:
                e["note"] = note
            snips.append(e)
        layers[lid] = dict(title=F["title"], role=F["role"], kind=F["kind"], summary=F["summary"], snippets=snips)
    edges = [edge_dict(*e) for e in FLOW_EDGES]
    return dict(root=root, repo=blob, rows=FLOW_ROWS, edges=edges, layers=layers)


def find_decl(P, qual):
    hits = [d for d in P["decls"] if d["name"] == qual or d["name"].endswith("." + qual)]
    if not hits:
        raise SystemExit(f"declaration not found: {qual}")
    return hits[0]


def outline(P):
    """(line, title) of the Statement's section markers, in file order."""
    out, lines = [], P["lines"]
    for i, ln in enumerate(lines):
        m = re.match(r"^/-!\s*#+\s*(.*?)\s*-/\s*$", ln)
        if m:
            out.append((i + 1, m.group(1)))
        elif re.match(r"^/-!\s*=+\s*$", ln):
            for nx in lines[i + 1:i + 4]:
                t = nx.strip()
                if t and not set(t) <= {"="}:
                    out.append((i + 2, t))
                    break
    return out


# ----------------------------------------------------------------------------------------
def build(suite, sto, repo_url, ref, root):
    blob = f"{repo_url}/blob/{ref}"
    cache, layer_of = {}, {}
    for lid, L in LAYERS.items():
        for f in L["files"]:
            layer_of[K(f)] = lid
            get_info(cache, suite, root, K(f))
    # --- imports between blocks, from the `import` lines
    imp = {}
    ext = {"statement": set(), "proofs": set(), "model": set()}
    for key, P in cache.items():
        me = layer_of[key]
        for i in P["imports"]:
            if not i.startswith("ForShor.ShorVerification."):
                continue
            k2 = i[len("ForShor.ShorVerification."):].replace(".", "/")
            tgt = layer_of.get(k2)
            if tgt is None:
                if k2.startswith(SUITE + "/"):
                    raise SystemExit(f"{key} imports {k2}, which is not in any block")
                tgt = "Framework"
                ext["statement" if key == K("Statement") else ("model" if key == K(MODEL) else "proofs")].add(k2)
            if tgt != me:
                imp.setdefault((tgt, me), set()).add(key)
    # the owner's rule, checked on the import lines too: the Statement imports only Framework/ and Statements
    for k2 in ext["statement"]:
        if not (k2.startswith("Framework/") or k2.endswith("/Statement")):
            raise SystemExit(f"Statement.lean imports {k2}: not Framework/ or a Statement.lean")
    rowof = {lid: r for r, row in enumerate(ROWS) for lid in row}
    assert set(rowof) == set(LAYERS), "every block must be in exactly one row"
    for (a, b), _ in imp.items():
        assert rowof[a] < rowof[b], f"import {a} -> {b} points up the figure"
    for a, b, kind, lab, opt in EDGES:
        assert (a, b) in imp, f"curated edge {a} -> {b} is not an import edge"
    edges = [edge_dict(*e) for e in EDGES]
    imports = [{"from": a, "to": b, "files": len(s)} for (a, b), s in sorted(imp.items())]

    def short(key):
        return key[len(SUITE) + 1:] if key.startswith(SUITE + "/") else key

    def link(key, line=None):
        return f"{blob}/{root}/{key}.lean" + (f"#L{line}" if line else "")

    # --- the claims table (Statement and Main) and the Statement's outline
    S_P, M_P = cache[K("Statement")], cache[K("Main")]
    rows = ""
    for claim, thm in CLAIMS:
        cs, ts = find_decl(S_P, claim), find_decl(M_P, thm)
        rows += (f'<tr><td><a href="{link(K("Statement"), cs["line"])}"><code>{claim}</code></a></td>'
                 f'<td><a href="{link(K("Main"), ts["line"])}"><code>{thm}</code></a></td></tr>')
    claims_table = ('<table class="ptp-mods"><tr><td><em>claim (Statement.lean)</em></td><td><em>proved by (Main.lean)</em></td></tr>'
                    + rows + "</table>")
    sec = "<ul>" + "".join(f'<li><a href="{link(K("Statement"), ln)}">{esc(t)}</a></li>' for ln, t in outline(S_P)) + "</ul>"

    layers = {}
    for lid, L in LAYERS.items():
        files = L["files"]
        decls = sum(len(cache[K(f)]["decls"]) for f in files)
        nlines = sum(cache[K(f)]["n"] for f in files)
        h = ""
        if files:
            h += (f'<p class="lmeta">{len(files)} file{"s" if len(files) > 1 else ""} · {decls} declarations · '
                  f'{nlines:,} lines</p>')
        s = SUMMARY[lid]
        fmt = lambda xs: ", ".join(f"<code>{x}</code>" for x in sorted(xs)) or "nothing"
        s = s.replace("{FSTATEMENT}", fmt(ext["statement"]))
        s = s.replace("{FPROOFS}", fmt(ext["proofs"] - ext["statement"]))
        s = s.replace("{FMODEL}", fmt(ext["model"]))
        s = s.replace("{SCRIPT_CLOSURE}", f"{blob}/scripts/StatementClosure.lean")
        s = s.replace("{CLAIMSTABLE}", claims_table).replace("{OUTLINE}", sec)
        h += s
        if files:
            h += '<table class="ptp-mods">' + "".join(
                f'<tr><td><a href="{link(K(f))}">{esc(short(K(f)))}.lean</a></td>'
                f'<td>{len(cache[K(f)]["decls"])} decls</td><td>{esc(cache[K(f)]["title"] or "")}</td></tr>'
                for f in files) + "</table>"
        snips = []
        for name, f, note in SNIPS.get(lid, []):
            key = K(f)
            d, code = statement(get_info(cache, suite, root, key), name)
            e = dict(name=name, file=key + ".lean", line=d["line"], code=code)
            if note:
                e["note"] = note
            snips.append(e)
        layers[lid] = dict(title=lid if lid != "Framework" else "Framework", role=L["role"], kind=L["kind"],
                           summary=h, snippets=snips)
    # --- every file quoted or linked must exist at the pinned commit
    tracked = set(subprocess.check_output(["git", "-C", suite, "ls-tree", "-r", "--name-only", ref], text=True).split())

    def need(rel):
        if f"{root}/{rel}" not in tracked:
            raise SystemExit(f"{rel} is not tracked at {ref}: links to it would 404 and its content is not pinned")
    if "scripts/StatementClosure.lean" not in tracked:
        raise SystemExit("scripts/StatementClosure.lean is not tracked at " + ref)
    for key in cache:
        need(key + ".lean")
    for L in layers.values():
        for sn in L["snippets"]:
            need(sn["file"])
    out_layers = dict(root=root, repo=blob, rows=ROWS, edges=edges, imports=imports, layers=layers)
    # --- the recursion figure (reference policy and its exact ladder come from the STO fork)
    policy = json.load(open(os.path.join(sto, REFPOLICY)))
    fig = build_fig(sto, policy)
    FS = [("PTPTable", "Statement"), ("PTPTable.contract", "Statement"), ("pointCount", "Statement"),
          ("PTPPolicy.choose", "Statement"), ("PTPPolicy.check", "Statement"), ("childWidth3", "Statement"),
          ("node_identity", "Proofs/Values/Semantics"), ("PTPPolicy.evalPhase", "Proofs/Values/Semantics"),
          ("ptpTightWidth", "Statement"), ("ptpTightWidth_spec", "Proofs/Values/Exact"), ("ptpSubNode", "Statement"),
          ("evalL_ptpNode_ket", "Proofs/Gates/Node"), ("PolicyImpl", "Statement"),
          ("ptp_gate_full_exact", "Proofs/ExactBoard/ExactBuild"), ("PTPGateTotalBound", "Statement"),
          ("ptpExponent", "Statement"), ("ptp_lowerExact_correct", "Main"), ("PTPPolicy.ladderX", "Statement")]
    sn = {}
    for name, f in FS:
        key = K(f)
        d, code = statement(get_info(cache, suite, root, key), name)
        sn[name.split(".")[-1]] = dict(name=name, file=key + ".lean", line=d["line"], code=code)
    for v in sn.values():
        need(v["file"])
    fig["snippets"] = sn
    fig["root"] = root
    fig["repo"] = blob
    fig["policyFile"] = REFPOLICY
    ch = champions(sto)
    flow = build_flow(cache, suite, root, blob)
    for L in flow["layers"].values():
        for sn_ in L["snippets"]:
            need(sn_["file"])
    return out_layers, fig, ch, flow


def js(var, obj, banner):
    return f"// {banner}\n// Generated by scripts/gen_ptp_site.py from the PhaseTripleProduct development; regenerate, don't edit.\nwindow.{var} = " + \
        json.dumps(obj, indent=1, ensure_ascii=False) + ";\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--suite", default=os.environ.get("PTP_SUITE", DEFAULT_SUITE),
                    help="a ForShor checkout (git repository) holding the development")
    ap.add_argument("--sto", default=DEFAULT_STO,
                    help="the ShorTableOptimization fork: benchmark champions, the reference policy and its ladder")
    ap.add_argument("--repo-url", default="https://github.com/VerifiedQC/ForShor")
    ap.add_argument("--ref", default=None)
    ap.add_argument("--root", default="ForShor/ShorVerification")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--allow-dirty", action="store_true", help="quote a working tree that differs from --ref")
    a = ap.parse_args()
    ref = a.ref or subprocess.check_output(["git", "-C", a.suite, "rev-parse", "--short=12", "HEAD"], text=True).strip()
    # The links pin `ref`, so what is quoted must be exactly that commit.
    if not a.allow_dirty:
        dirty = subprocess.check_output(["git", "-C", a.suite, "status", "--porcelain", "--", a.root,
                                         "scripts/StatementClosure.lean"], text=True).strip()
        if dirty:
            sys.exit(f"{a.suite} has uncommitted changes under {a.root}:\n{dirty}\nre-run when clean, or pass --allow-dirty")
    layers, fig, ch, flow = build(a.suite, a.sto, a.repo_url, ref, a.root)
    files = {
        "layers.js": js("PTP_LAYERS", layers, "Data for the PhaseTripleProduct layer graph (docs/layers.js)."),
        "ptpfig.js": js("PTPFIG", fig, "Data for the PhaseTripleProduct recursion figure (ptpfig.js)."),
        "flow.js": js("PTP_FLOW", flow, "Data for the PhaseTripleProduct algorithm-flow diagram (docs/layers.js)."),
        "champions.js": js("PTP_CHAMPIONS", ch, "Benchmark champions (structural score) per target, from the STO fork's leaderboard/best-known.md."),
    }
    bad = 0
    for name, text in files.items():
        p = os.path.join(OUT, name)
        if a.check:
            if not os.path.exists(p) or read(p) != text:
                print(f"STALE: {p}"); bad += 1
        else:
            os.makedirs(OUT, exist_ok=True)
            with open(p, "w", encoding="utf-8") as f:
                f.write(text)
            print("wrote", p, f"({len(text)//1024} KiB)")
    if a.check:
        print("ok" if not bad else f"{bad} stale file(s); re-run without --check")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
