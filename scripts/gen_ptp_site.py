#!/usr/bin/env python3
"""Generate the data behind docs/phasetripleproduct/ (the PhaseTripleProduct page).

Reads the PTP verification suite (STO's TableGeneration/RecursiveCost/PTP/) and writes

    docs/phasetripleproduct/data/layers.js    window.PTP_LAYERS   the layer graph (docs/layers.js)
    docs/phasetripleproduct/data/ptpfig.js    window.PTPFIG       the recursion figure (ptpfig.js)
    docs/phasetripleproduct/data/flow.js      window.PTP_FLOW      the algorithm-flow diagram
    docs/phasetripleproduct/data/champions.js window.PTP_CHAMPIONS the benchmark's PTP targets

Everything quoted from Lean is copied verbatim from the source at the recorded file:line; the
import edges are read from the `import` lines; the register contents in the figure are computed
by executing the reference k = 2 table (and the PTP node identity is re-checked numerically on it).
Never edit the output by hand: re-run this script.

Where links point is three settings, because the suite does not (yet) live in this repository:

    --sto PATH        a checkout of the suite (default: the sibling STO fork)
    --repo-url URL    GitHub repository the links point at
    --ref REF         commit/branch used in the links (default: HEAD of --sto)
    --root DIR        where RecursiveCost/ sits inside that repository
                      (default TableGeneration/RecursiveCost; if the suite is moved into
                      ForShor, pass e.g. --repo-url https://github.com/VerifiedQC/ForShor
                      --ref main --root ptp_suite/TableGeneration/RecursiveCost)

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
FORSHOR_BLOB = "https://github.com/VerifiedQC/ForShor/blob/main"
REFPOLICY = "policies/ref_ptp_2048.json"

# ----------------------------------------------------------------------------------------
# Layers: which modules (relative to PTP/) form each block of the layer graph, and the curated
# text. `kind` only picks the tint. Ids are letters only (they go into the URL hash).
# ----------------------------------------------------------------------------------------
LAYERS = {
    "ForShor": dict(kind="upstream", role="gate language, semantics, cost model, master theorem", modules=[]),
    "STO": dict(kind="upstream", role="tables, point lists, banded-policy mirror", modules=[]),
    "Table": dict(kind="table", role="the table contract and the width scan", modules=["Contract", "Width"]),
    "Values": dict(kind="table", role="exact values, the node identity, exact widths", modules=["Semantics", "Exact"]),
    "Gates": dict(kind="gate", role="one recursion level, as gates", modules=["Leaf", "LeafSandwich", "Node"]),
    "Scan": dict(kind="gate", role="recursion, census, scan widths", modules=["Census", "Recursion", "Build", "CensusFull"]),
    "ExactBoard": dict(kind="gate", role="the same recursion at exact widths", modules=["ExactNode", "ExactRecursion", "ExactBuild"]),
    "Accept": dict(kind="surface", role="the acceptance rule", modules=["Threshold"]),
    "Surface": dict(kind="surface", role="the public specification and theorem", modules=["Assertions", "Main"]),
    "Controlled": dict(kind="ext", role="controlled PTP by operand masking", modules=["Controlled"]),
    "Asymptotic": dict(kind="ext", role="O(n^log_k(3k−2)) gates", modules=["Asymptotic"]),
    "Unbalanced": dict(kind="ext", role="operands of unequal width", modules=["Unbalanced"]),
    "QubitsTight": dict(kind="ext", role="the qubit count", modules=["QubitsTight"]),
    "Witness": dict(kind="witness", role="non-vacuity and fault witnesses",
                    modules=["StandardModel", "RecursionWitness", "Instances/FaultChallenge", "Instances/ExactFault"]),
    "Planner": dict(kind="witness", role="a planner whose output is always valid", modules=["Plan"]),
    "Harness": dict(kind="harness", role="policy JSON in, kernel verdict out", modules=["AxiomAudit"]),
}
ROWS = [["STO", "ForShor"], ["Table"], ["Values"], ["Gates"], ["Scan"], ["ExactBoard"],
        ["Accept", "Surface"], ["Controlled", "Asymptotic", "QubitsTight"],
        ["Unbalanced", "Witness", "Planner"], ["Harness"]]

# Curated edges (dependency -> importer). `generated` edges are not Lean imports: the harness
# writes a Lean file that imports the suite. Everything else must be a real import edge.
EDGES = [
    ("STO", "Table", "primary", "ValidPointList, Prog", dict(mono=True)),
    ("ForShor", "Table", "secondary", None, {}),
    ("Table", "Values", "primary", "contract, childWidth", dict(mono=True)),
    ("Values", "Gates", "primary", "node identity", dict(theorem="node_identity")),
    ("ForShor", "Gates", "primary", "LowGate, NaiveLeaf", dict(mono=True, side="right", lane=0)),
    ("Gates", "Scan", "primary", "evalL_ptpNode_ket", dict(mono=True)),
    ("Scan", "ExactBoard", "primary", "PolicyImpl", dict(mono=True)),
    ("Values", "ExactBoard", "primary", "ptpTightWidth", dict(mono=True, side="left", lane=0)),
    ("ExactBoard", "Surface", "primary", "ptp_gate_full_exact", dict(mono=True)),
    ("Values", "Accept", "primary", "chainContractsTight_iff_reach", dict(mono=True, side="left", lane=1)),
    ("Surface", "Controlled", "primary", "PTPPhaseOp", dict(mono=True)),
    ("ExactBoard", "Asymptotic", "secondary", None, {}),
    ("ForShor", "Asymptotic", "primary", "master theorem", dict(side="right", lane=1)),
    ("ExactBoard", "QubitsTight", "secondary", None, dict(side="right", lane=2)),
    ("Controlled", "Unbalanced", "primary", "padding", {}),
    ("Asymptotic", "Unbalanced", "secondary", None, {}),
    ("Controlled", "Witness", "secondary", None, {}),
    ("Surface", "Witness", "secondary", None, dict(side="right", lane=3)),
    ("Values", "Planner", "secondary", None, dict(side="left", lane=2)),
    ("Accept", "Harness", "primary", "generated Lean", dict(side="left", lane=3, generated=True)),
]

# Statements quoted in each panel: (declaration, file under PTP/, note).
SNIPS = {
    "Table": [
        ("PTPTable", "Contract", "A table: the arity \\(k\\), the interpolation points in the order the program consumes them, and the program, which is STO's own <code>Prog k</code>. Nothing about PTP is in the program language; the tripling lives in what the node does with it."),
        ("PTPTable.contract", "Contract", "The admissibility check as one kernel-reducible <code>Bool</code>: \\(3k-2\\) points, pairwise distinct, each valid, consumed in order by the program, a safe program, and registers returned to where they started. <code>contract_iff</code> proves it equals STO's <code>ValidPointList .PhaseTripleProduct</code> plus <code>ProgConsumesPtsSafe</code>."),
        ("PTPPolicy.check", "Contract", "A policy is a list of bands, widest first. It is accepted when the thresholds strictly decrease and every band's table passes the contract."),
        ("childWidth3", "Contract", "The width scan. Each of the three operands is split top-heavy into \\(k\\) limbs and the program is run on <em>widths</em> (magnitude bounds); the child width is one sign bit above the largest bound any register reaches."),
        ("node_width_sound", "Width", "At that width no register write ever wraps, so wrapping and exact arithmetic agree."),
    ],
    "Values": [
        ("node_identity", "Semantics", "The PTP node identity. A product of three degree-\\((k-1)\\) limb polynomials has degree \\(3(k-1)\\), so its value at the radix is a fixed rational combination of its values at \\(3k-2\\) distinct points. This is the whole reason the recursion works."),
        ("PTPPolicy.evalPhase", "Semantics", "The exact semantics of a policy: split, take \\(3k-2\\) smaller phases on the point values, recurse; or the plain product when no table applies or the width would not shrink."),
        ("ptpTightWidth_spec", "Exact", "The exact width: the least \\(W\\) whose signed range holds every value the table can produce (<code>tight_fits</code> that it suffices; <code>tight_le_childWidth</code> that it never exceeds the scan)."),
        ("tight_minimal", "Exact", "And that it is minimal: one bit fewer and some operand that fits \\(n\\) bits has a reachable register value that does not fit."),
    ],
    "Gates": [
        ("ptpLeafSandwich", "LeafSandwich", "The default base case: compute the product of one bit from each operand into a clean ancilla with Toffolis, rotate once, uncompute. One rotation per cell instead of five for the doubly-controlled phase leaf of <code>Leaf.lean</code>."),
        ("evalL_ptpNode_ket", "Node", "One level, on a basis state: three <code>LowGate</code>s per table operation (one per operand), a child on each triple of slot registers, angle \\(\\varphi\\,c_t\\). The node multiplies by \\(\\exp(i\\pi\\varphi\\,x_0x_1x_2)\\) and returns the basis state unchanged. Children here are leaves on pre-split slots; whole policies are the next layer."),
    ],
    "Scan": [
        ("PolicyImpl", "Recursion", "A gate-level recursion following a policy: a leaf where the policy stops, otherwise a split layout, a node, and one <code>PolicyImpl</code> per child."),
        ("PolicyImpl.specOn", "Recursion", "Correctness at every depth: a node over children that meet the phase specification meets it, given a clean reserve."),
        ("ptp_gate_full", "CensusFull", "Existence for every checked policy and width, with the resource census (Rz, Toffoli, X, H, CNOT, And†) and a qubit bound."),
    ],
    "ExactBoard": [
        ("WidthRule", "ExactRecursion", "The recursion is generic in the width rule; <code>exactRule</code> is <code>ptpTightWidth</code>, <code>scanRule</code> the conservative scan."),
        ("ptp_gate_full_exact", "ExactBuild", "The same existence, correctness and census at exact widths. This is the board the headline theorem and the gate-count theorem use."),
    ],
    "Accept": [
        ("PTPPolicy.chainContractsTight_iff_reach", "Threshold", "Beyond <code>check</code>: every table chosen at every width the exact recursion from \\(n\\) reaches has \\(k \\le m\\) and strictly shrinks the width. A band that fails this is rejected, which is what keeps degenerate bands from being claimed as recursion."),
    ],
    "Surface": [
        ("PTPPhaseOp", "Assertions", "The specification operator the reader supplies: a linear map acting on each basis ket as \\(\\exp(i\\pi\\varphi\\,x_0x_1x_2)\\). Nothing in it mentions <code>LowGate</code>, so the claim is independent of the circuit."),
        ("PTPLowerExactCorrect", "Assertions", "What is asserted: for a checked policy and three disjoint \\(n\\)-qubit registers there is a circuit following the policy at exact widths that acts as the specification on every clean state and has the exact gate counts."),
        ("ptp_lowerExact_correct", "Main", "The theorem."),
    ],
    "Controlled": [
        ("PTPCtlLowerExactCorrect", "Controlled", "A controlled PTP by <em>masking</em>: copy the control into a fresh operand \\(Y = c \\wedge X_0\\), run the uncontrolled circuit, unmask. It costs \\(2n\\) Toffolis (\\(n\\) of them \\(\\dagger\\)), \\(n+1\\) extra qubits, no extra rotations."),
        ("ptp_ctl_lowerExact_correct", "Controlled", None),
    ],
    "Asymptotic": [
        ("ptpExponent", "Asymptotic", "The exponent \\(\\log_k(3k-2)\\)."),
        ("ptp_gateTotal_bound", "Asymptotic", "For a constant policy (one table at every width), the exact-board gate count is \\(O(n^{\\log_k(3k-2)})\\), by ForShor's shifted master theorem."),
        ("ptp_circuit_gateCount_bound", "Asymptotic", "And the circuit of <code>ptp_gate_full_exact</code> has that many gates."),
    ],
    "Unbalanced": [
        ("PTPPadLowerExactCorrect", "Unbalanced", "Operands of different widths: sign-extend each in place into a clean reserve to the common width \\(n\\), run the balanced circuit, undo. The extension costs \\(2(d_0+d_1+d_2)\\) CNOTs. A native unbalanced node is not built."),
        ("ptp_pad_lowerExact_correct", "Unbalanced", None),
    ],
    "QubitsTight": [
        ("ptp_qubits_tight", "QubitsTight", "The circuit touches at most \\(3n + \\texttt{ptpWsTD}\\) distinct qubits (children share one workspace pool)."),
        ("ptp_qubits_le_ptpQubits", "QubitsTight", "<code>ptpQubits</code> is a proved <em>upper bound</em> at the scan rule. It bounds <code>usedQubits</code>, not the framework's <code>qubitCount</code>, which also adds <code>cleanAnc</code>."),
    ],
    "Witness": [
        ("model_ptp_lowerExact_correct", "StandardModel", "The theorem specialised to ForShor's concrete <code>Model.qs</code>, with the specification operator built by <code>diagLift</code>: the hypotheses are satisfiable."),
        ("gate_fault_wrong", "Instances/ExactFault", "A fault witness: one bit below the exact width the gate-level circuit is <em>wrong</em>, on a concrete state. The width is load-bearing."),
    ],
    "Planner": [
        ("Planner.plan_check", "Plan", None),
        ("Planner.plan_ladder", "Plan", None),
    ],
}

# Curated prose per layer. Modules, sizes and links are appended by the script.
SUMMARY = {
    "ForShor": "<p>What the suite is built on, and the reason it is a <em>standalone</em> suite rather than a part of ForShor's order-finding development: it uses ForShor's gate language <code>LowGate</code>, its semantics classes (<code>QSemantics</code>, <code>LowerGateClass</code>), its resource model <code>shorGateResourceModel</code> (Cuccaro adders, arbitrary-angle rotations, not T), its basis-level gate laws, the naive-leaf lemmas and the pure master theorem. Nothing in ForShor imports it.</p><p>Imported (read from the sources): {FORSHORIMPORTS}.</p>",
    "STO": "<p>The table language and the benchmark's contract: <code>Prog k</code>, <code>Point</code>, <code>ValidPointList</code>, <code>ProgConsumesPtsSafe</code> and the point count <code>ProductMode.pointCount .PhaseTripleProduct k = 3k − 2</code> (<code>pointCount_spec</code> pins it by <code>rfl</code>). From the banded PhaseProduct mirror the suite reuses only a few arity-free facts and the <code>sortedDesc</code> helper, so nothing here is borrowed from the PhaseProduct <em>circuit</em>.</p><p>Imported: {STOIMPORTS}.</p>",
    "Table": "<p>The PTP table and policy as data, with the contract that decides admissibility. A node takes <em>three</em> operands, each split into \\(k\\) limbs, so the interpolation needs \\(3(k-1)+1 = 3k-2\\) points instead of PhaseProduct's \\(2k-1\\).</p><p>The width scan runs the table's program on magnitude bounds, separately for the three operands, and gives the width every register of the node is allocated at. <code>node_width_sound</code> shows that no write wraps at that width.</p>",
    "Values": "<p>The mathematics, before any gate. <code>node_identity</code> is the Toom–Cook identity for three factors, <code>evalPhase</code> the recursive semantics, <code>evalPhase_correct</code> (and the wrapping and exact-width variants) that the recursion computes \\(\\varphi\\,x_0x_1x_2\\).</p><p><code>Exact</code> replaces the scan by the <em>least</em> width that works, <code>ptpTightWidth</code>: it runs the program on coefficient rows, takes the largest demand on a signed register, and is proved sound, minimal and never larger than the scan. On the reference policy at \\(n=2048\\) the exact ladder is 2048, 375, 189, 96, 50; the scan gives 2048, 398, 122, 66, 38 under a different band choice, which is why both boards exist.</p>",
    "Gates": "<p>One recursion level in ForShor's <code>LowGate</code>. The node holds \\(3k\\) slot registers; each table operation becomes three gates, one per operand; the \\(t\\)-th <code>phaseProduct i</code> becomes a child on the triple <code>(slot 0 i, slot 1 i, slot 2 i)</code> at angle \\(\\varphi\\,c_t\\).</p><p>The base case is the sandwich leaf. The earlier doubly-controlled-phase leaf is kept as a documented alternative with all its theorems.</p><p><em>Not covered here:</em> splitting three parent registers into slots, reserve management, children that are themselves nodes, any controlled variant. Those are the next layers.</p>",
    "Scan": "<p>From one node to a whole policy. <code>SplitLayout</code> splits three parent registers in place into child slots (zero-extending lower limbs, sign-extending the top), <code>SpecOn</code> is the register-level phase contract with explicit workspace, and <code>PolicyImpl</code> is the recursion. Correctness and the census hold at every depth (<code>Recursion</code>), exist for every checked policy and width (<code>Build</code>), and include CNOT and And† counts and a qubit bound (<code>CensusFull</code>).</p><p>Widths here are the conservative scan.</p>",
    "ExactBoard": "<p>The same recursion with the width rule abstracted (<code>WidthRule</code>, with <code>exactRule</code> and <code>scanRule</code>), so one development serves both boards: <code>PolicyImplD</code>, <code>ptp_gate_full_D</code>, and <code>ptp_gate_full_exact</code> at exact widths.</p>",
    "Accept": "<p>A policy can pass <code>check</code> and still be degenerate: a band whose table does not shrink the width would be claimed as recursion and then silently take the leaf. <code>chainContractsTight</code> closes that: every band the exact recursion from \\(n\\) selects must apply at a width \\(\\ge k\\) and strictly shrink it. <code>chainContractsTight_iff_reach</code> states the rule without the ladder.</p>",
    "Surface": "<p>The claim a reader should check, stated apart from the proof. The specification operator is a structure the reader supplies, so the statement does not mention <code>LowGate</code>. The theorem covers the linear span of <em>clean</em> basis kets: operands fit signed \\(n\\ge1\\) bits and the workspace is \\(|0\\rangle\\). For \\(n=0\\) no ket is clean and the statement is vacuous.</p>",
    "Controlled": "<p>A controlled PTP built by <em>masking</em> one operand. This is not ForShor's construction, which controls every leaf phase; that variant is <strong>not</strong> proved here. On the clean subspace, the control may overlap the other registers in a degenerate way (then the circuit is the identity on the clean span), which the docstring of <code>PTPCtlLowerExactCorrect</code> states.</p>",
    "Asymptotic": "<p>The PTP analogue of ForShor's PhaseProduct gate-count theorem, under the same hypothesis: a <strong>constant policy</strong>, one table at every width. The exponent is \\(\\log_k(3k-2)\\): 2.000 at \\(k=2\\), 1.771 at \\(k=3\\), 1.661 at \\(k=4\\), tending to 1. The count is <code>rz + toffoli + x + h + cnot</code> under <code>shorGateResourceModel</code>, not a T count.</p>",
    "Unbalanced": "<p>Operands of unequal width, handled by padding rather than a native unbalanced node. Open: a native node, the least width at which the wrapping semantics is correct, and the leaf-control variant.</p>",
    "QubitsTight": "<p>The circuit names at most \\(3n + \\texttt{ptpWsTD}\\) qubits, with \\(\\texttt{ptpWsTD} = 3(k\\,C' - n)\\) per node and one shared pool. This is not the framework's <code>qubitCount</code>: the Cuccaro/negation scratch <code>cleanAnc</code> of the recursive circuit is not bounded here. <code>ptpQubits</code> is also loose by up to a factor \\(k\\) per level (private per-child workspace versus the shared pool).</p>",
    "Witness": "<p>Why the theorems are not vacuous, and why the hypotheses are needed. <code>StandardModel</code> specialises the typeclass stack to ForShor's <code>Model.qs</code>. <code>RecursionWitness</code> assembles a concrete \\(k=2\\) gate-level recursion on three 20-qubit registers (child width 14), every structural hypothesis discharged by <code>decide</code>. The <code>Instances/</code> modules are faults: a point-order fault the contract rejects, a width fault (one bit under the exact width, the circuit is wrong on a concrete state). The harness also writes per-policy certificate modules (<code>Instances/PTPSubmitted*.lean</code>) when it checks a policy; those are generated, git-ignored, and not part of the suite's source.</p>",
    "Planner": "<p>A Lean planner for banded PTP policies. <code>plan tables n o</code> walks from \\(n\\) at the exact widths, takes at each width the table an oracle names, stops at the leaf when the oracle names nothing or a non-contracting table, and merges consecutive bands with the same table. For <em>every</em> oracle and every \\(n\\) the output passes <code>check</code>, is correct under all three semantics, and its ladder is the oracle's. <code>PlanSeeds/</code> holds reconstructed seeds with their negative controls (unsorted thresholds, a foreign table or index), which the planner provably does not produce.</p><p>This validates the planner's <em>output</em>; it says nothing about how good the oracle's choices are.</p>",
    "Harness": "<p>Not Lean imports: scripts around the suite. <code>check_ptp_policy.py</code> takes a policy JSON, generates a Lean module (<code>ptp_policy_json_to_lean.py</code>), has the kernel decide <code>check</code> and <code>chainContractsTight</code>, replays the report and cross-checks the widths against the Python mirror <code>ptp_exact_width.py</code>. It exits 0 on accept and 1 on reject; the <code>policies/threshold_*</code> and <code>faulty_*</code> files are negative controls that must be rejected. <code>PTPAxiomCheck.lean</code> asserts that the headline theorems depend only on <code>propext</code>, <code>Classical.choice</code>, <code>Quot.sound</code>; <code>check_ptp_layers.py</code> enforces the layer order and bans <code>sorry</code>, <code>native_decide</code> and <code>axiom</code>.</p>",
}

HARNESS_FILES = ["scripts/check_ptp_policy.py", "scripts/ptp_policy_json_to_lean.py", "scripts/PTPPolicyReport.lean",
                 "scripts/ptp_exact_width.py", "scripts/PTPAxiomCheck.lean", "scripts/check_ptp_layers.py",
                 "policies/ref_ptp_2048.json"]

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
        snips=[("ptpEigenphase", "Assertions", None), ("PTPPhaseOp", "Assertions", None)]),
    "choose": dict(title="Choose a table", role="the policy", kind="classical",
        summary=r"""<p>The policy is a list of bands, widest first. At the current width \(w\) it returns the table of the first band whose threshold is at most \(w\), or nothing. The node is a <em>leaf</em> if there is no table, and also if the table would not shrink the width, so the recursion cannot fail to terminate.</p><p>The policy is checked once, before any circuit exists: thresholds strictly decrease and every table passes the contract (\(3k-2\) distinct points, consumed in order, registers returned to start). A stronger rule, <code>chainContractsTight</code>, requires every band the recursion reaches to shrink the width.</p>""",
        snips=[("PTPPolicy.choose", "Contract", None), ("PTPPolicy.check", "Contract", None)]),
    "split": dict(title="Split into limbs", role="three operands", kind="quantum",
        summary=r"""<p>Each operand is split in place into \(k\) limbs of about \(n/k\) bits: the lower limbs zero-extended and the top limb sign-extended to the child width \(C'\) (at exact widths, \(\mathtt{ptpTightWidth}\)), using a clean reserve. The three operands give \(3k\) slot registers, laid out so that no two overlap.</p><p>The width matters: it is the least one at which no register in the program ever overflows. One bit fewer and the circuit is provably wrong on a concrete state (<code>gate_fault_wrong</code>).</p>""",
        snips=[("SplitLayout", "Recursion", None), ("ptpTightWidth_spec", "Exact", None)]),
    "leaf": dict(title="Sandwich leaf", role="the base case", kind="quantum",
        summary=r"""<p>Where the recursion stops, the product is computed directly. For each pair of bits of \(y\) and \(z\), a Toffoli writes their product into a clean ancilla; one rotation then applies the phase for every bit of \(x\); the Toffoli is undone. One rotation per cell instead of five for the doubly-controlled phase it replaced.</p><p>The leaf costs \(O(n^3)\) cells at width \(n\), so the policy should take it only at small widths.</p>""",
        snips=[("ptpLeafSandwich", "LeafSandwich", None)]),
    "evaluate": dict(title="Evaluate at a point", role="register arithmetic", kind="quantum",
        summary=r"""<p>The table's program runs on the limb registers: additions of shifted registers, negations, shifts. Every operation is emitted three times, once per operand, so \(x\), \(y\) and \(z\) are moved to the same interpolation point together. When the program reaches a <code>phaseProduct i</code> checkpoint, register \(i\) of each operand holds that point's value; that is the contract's consumption condition.</p>""",
        snips=[("opGates", "Node", None)]),
    "children": dict(title="A smaller PTP per point", role="the recursion", kind="quantum",
        summary=r"""<p>At each of the \(3k-2\) checkpoints a phase triple product is taken on the three registers just prepared, at angle \(\varphi\,c_t\), where \(c_t\) is the point's interpolation weight at the limb radix. Each is the same problem at the smaller width, so control returns to <em>Choose a table</em> with \(w' < w\).</p><p>That the weighted sum is right is <code>node_identity</code>: \(\sum_t c_t\prod_s x_s(p_t) = x_0x_1x_2\). Children run one after another and share one workspace pool, which keeps the qubit count at \(3n\) plus a workspace term (<code>ptpWsTD</code>) instead of one workspace per child.</p>""",
        snips=[("ptpNode", "Node", None), ("node_identity", "Semantics", None)]),
    "restore": dict(title="Undo and merge", role="clean up", kind="quantum",
        summary=r"""<p>The program's last stretch returns every limb register to its own limb (<code>returnsToStartCheck</code>, part of the contract), and the split is undone. The net effect of the node on a basis state is the single phase \(\exp(i\pi\varphi\,xyz)\), with the basis state otherwise unchanged. <code>evalL_ptpNode_ket</code> states this for one node over leaf children; <code>PolicyImpl.specOn</code> lifts it through the whole recursion.</p>""",
        snips=[("evalL_ptpNode_ket", "Node", None), ("PolicyImpl.specOn", "Recursion", None)]),
    "count": dict(title="Count the gates", role="the cost", kind="classical",
        summary=r"""<p>The circuit's gates are counted exactly, by a census that follows the recursion (<code>ptp_gate_full_exact</code>): rotations, Toffolis, X, H, CNOTs and the number of uncomputing Toffolis. For a <em>constant</em> policy (one table at every width) the total is \(O(n^{\log_k(3k-2)})\): a node does work linear in its width and has \(3k-2\) children of about a \(k\)-th of it, and ForShor's shifted master theorem solves that recurrence. The count is in <code>shorGateResourceModel</code>, not T gates.</p>""",
        snips=[("ptpExponent", "Asymptotic", None), ("ptp_gateTotal_bound", "Asymptotic", None)]),
}


def build_flow(info, ptp, blob, root):
    layers = {}
    for lid, F in FLOW.items():
        snips = []
        for name, f, note in F["snips"]:
            P = info.get(f) or parse(os.path.join(ptp, f + ".lean"))
            d, code = statement(P, name)
            e = dict(name=name, file=f"PTP/{f}.lean", line=d["line"], code=code)
            if note:
                e["note"] = note
            snips.append(e)
        layers[lid] = dict(title=F["title"], role=F["role"], kind=F["kind"], summary=F["summary"], snippets=snips)
    edges = []
    for a, b, kind, lab, opt in FLOW_EDGES:
        e = {"from": a, "to": b, "kind": kind}
        if lab:
            e["label"] = lab
        for key in ("mono", "theorem", "side", "lane"):
            if key in opt:
                e[key] = opt[key]
        edges.append(e)
    return dict(root=root, repo=blob, rows=FLOW_ROWS, edges=edges, layers=layers)

# ----------------------------------------------------------------------------------------
def build(sto, repo_url, ref, root):
    rc = os.path.join(sto, "TableGeneration", "RecursiveCost")
    ptp = os.path.join(rc, "PTP")
    blob = f"{repo_url}/blob/{ref}"
    mod_of_layer, info = {}, {}
    for lid, L in LAYERS.items():
        for m in L["modules"]:
            mod_of_layer[m] = lid
            info[m] = parse(os.path.join(ptp, m + ".lean"))
    # PlanSeeds count
    seeds = sorted(os.listdir(os.path.join(ptp, "PlanSeeds")))
    seed_ids = sorted({re.match(r"(S[0-9a-f]+)", f).group(1) for f in seeds})
    # imports aggregated
    imp = {}
    ext = {"ForShor": set(), "STO": set()}
    for m, P in info.items():
        me = mod_of_layer[m]
        for i in P["imports"]:
            tgt = None
            if i.startswith("TableGeneration.RecursiveCost.PTP."):
                rel = i[len("TableGeneration.RecursiveCost.PTP."):].replace(".", "/")
                tgt = mod_of_layer.get(rel)
            elif i.startswith("ForShor."):
                tgt = "ForShor"; ext["ForShor"].add(i)
            elif i.startswith(("TableGeneration.RecursiveCost.BandedPolicy", "TableGeneration.ContractSoundness",
                               "TableGeneration.RecursiveCost.PlanCore")):
                tgt = "STO"; ext["STO"].add(i)
            if tgt and tgt != me:
                imp.setdefault((tgt, me), set()).add(m)
    # layer graph is acyclic and rows respect it
    rowof = {lid: r for r, row in enumerate(ROWS) for lid in row}
    for (a, b), _ in imp.items():
        assert rowof[a] < rowof[b], f"import {a} -> {b} points up the figure"
    for a, b, kind, lab, opt in EDGES:
        if not opt.get("generated"):
            assert (a, b) in imp, f"curated edge {a} -> {b} is not an import edge"
    edges = []
    for a, b, kind, lab, opt in EDGES:
        e = dict(OPT=0)
        e = {"from": a, "to": b, "kind": kind}
        if lab:
            e["label"] = lab
        for key in ("mono", "theorem", "side", "lane"):
            if key in opt:
                e[key] = opt[key]
        edges.append(e)
    imports = [{"from": a, "to": b, "files": len(s)} for (a, b), s in sorted(imp.items())]

    def link(m):
        return f"{blob}/{root}/PTP/{m}.lean"
    layers = {}
    for lid, L in LAYERS.items():
        mods = L["modules"]
        decls = sum(len(info[m]["decls"]) for m in mods)
        nlines = sum(info[m]["n"] for m in mods)
        h = ""
        if mods:
            extra = ""
            if lid == "Planner":
                extra = f" · plus <code>PlanSeeds/</code>: {len(seeds)} files, {len(seed_ids)} seeds with negative controls"
            h += f'<p class="lmeta">{len(mods)} module{"s" if len(mods)>1 else ""} · {decls} declarations · {nlines:,} lines{extra}</p>'
        s = SUMMARY[lid]
        s = s.replace("{FORSHORIMPORTS}", ", ".join(f"<code>{i.split('.',1)[1]}</code>" for i in sorted(ext["ForShor"])) or "none")
        s = s.replace("{STOIMPORTS}", ", ".join(f"<code>{i.replace('TableGeneration.RecursiveCost.','').replace('TableGeneration.','')}</code>" for i in sorted(ext["STO"])) or "none")
        h += s
        if mods:
            h += '<table class="ptp-mods">' + "".join(
                f'<tr><td><a href="{link(m)}">{m}.lean</a></td><td>{len(info[m]["decls"])} decls</td><td>{esc(info[m]["title"] or "")}</td></tr>'
                for m in mods) + "</table>"
        if lid == "Harness":
            h += '<table class="ptp-mods">' + "".join(
                f'<tr><td><a href="{blob}/{(root.rsplit("/TableGeneration",1)[0] + "/") if "/TableGeneration" in root else ""}{f}">{os.path.basename(f)}</a></td><td></td><td></td></tr>'
                for f in HARNESS_FILES) + "</table>"
        snips = []
        for name, f, note in SNIPS.get(lid, []):
            P = info.get(f) or parse(os.path.join(ptp, f + ".lean"))
            d, code = statement(P, name)
            e = dict(name=name, file=f"PTP/{f}.lean", line=d["line"], code=code)
            if note:
                e["note"] = note
            snips.append(e)
        layers[lid] = dict(title=lid if lid not in ("ForShor", "STO") else ("ForShor" if lid == "ForShor" else "STO contract"),
                           role=L["role"], kind=L["kind"], summary=h, snippets=snips)
    # every file quoted or linked must exist at the pinned commit (the harness writes git-ignored modules)
    tracked = set(subprocess.check_output(["git", "-C", sto, "ls-tree", "-r", "--name-only", ref], text=True).split())
    def need(rel):
        if f"TableGeneration/RecursiveCost/{rel}" not in tracked:
            raise SystemExit(f"{rel} is not tracked at {ref}: links to it would 404 and its content is not pinned")
    for m in info:
        need(f"PTP/{m}.lean")
    for L in layers.values():
        for sn in L["snippets"]:
            need(sn["file"])
    out_layers = dict(root=root, repo=blob.rsplit("/blob/", 1)[0] + "/blob/" + ref, rows=ROWS, edges=edges,
                      imports=imports, layers=layers)
    policy = json.load(open(os.path.join(sto, REFPOLICY)))
    fig = build_fig(sto, policy)
    # figure snippets
    FS = [("PTPTable", "Contract"), ("PTPTable.contract", "Contract"), ("pointCount", "Contract"), ("PTPPolicy.choose", "Contract"),
          ("PTPPolicy.check", "Contract"), ("childWidth3", "Contract"), ("node_identity", "Semantics"), ("PTPPolicy.evalPhase", "Semantics"),
          ("ptpTightWidth", "Exact"), ("ptpTightWidth_spec", "Exact"), ("ptpNode", "Node"), ("evalL_ptpNode_ket", "Node"),
          ("PolicyImpl", "Recursion"), ("ptp_gate_full_exact", "ExactBuild"), ("ptp_gateTotal_bound", "Asymptotic"),
          ("ptpExponent", "Asymptotic"), ("ptp_lowerExact_correct", "Main"), ("PTPPolicy.ladderX", "Exact")]
    sn = {}
    for name, f in FS:
        P = info.get(f) or parse(os.path.join(ptp, f + ".lean"))
        d, code = statement(P, name)
        sn[name.split(".")[-1] if name != "PTPPolicy.choose" else "choose"] = dict(name=name, file=f"PTP/{f}.lean", line=d["line"], code=code)
    for v in sn.values():
        need(v["file"])
    fig["snippets"] = sn
    fig["root"] = root
    fig["repo"] = out_layers["repo"]
    fig["policyFile"] = REFPOLICY
    ch = champions(sto)
    flow = build_flow(info, ptp, out_layers["repo"], root)
    for L in flow["layers"].values():
        for sn_ in L["snippets"]:
            need(sn_["file"])
    return out_layers, fig, ch, flow


def js(var, obj, banner):
    return f"// {banner}\n// Generated by scripts/gen_ptp_site.py from the PTP suite; regenerate, don't edit.\nwindow.{var} = " + \
        json.dumps(obj, indent=1, ensure_ascii=False) + ";\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sto", default=os.environ.get("PTP_SUITE", DEFAULT_STO))
    ap.add_argument("--repo-url", default="https://github.com/courtneyjzapata/ShorTableOptimization_temp")
    ap.add_argument("--ref", default=None)
    ap.add_argument("--root", default="TableGeneration/RecursiveCost")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--allow-dirty", action="store_true", help="quote a working tree that differs from --ref")
    a = ap.parse_args()
    ref = a.ref or subprocess.check_output(["git", "-C", a.sto, "rev-parse", "--short=12", "HEAD"], text=True).strip()
    # The links pin `ref`, so what is quoted must be exactly that commit. The suite's own checker
    # rewrites generated Lean files in the working tree while it runs; refuse to quote a dirty tree.
    if not a.allow_dirty:
        dirty = subprocess.check_output(["git", "-C", a.sto, "status", "--porcelain", "--", "TableGeneration", "scripts",
                                         "policies", "leaderboard"], text=True).strip()
        if dirty:
            sys.exit(f"{a.sto} has uncommitted changes (a checker may be running):\n{dirty}\nre-run when clean, or pass --allow-dirty")
    layers, fig, ch, flow = build(a.sto, a.repo_url, ref, a.root)
    files = {
        "layers.js": js("PTP_LAYERS", layers, "Data for the PhaseTripleProduct layer graph (docs/layers.js)."),
        "ptpfig.js": js("PTPFIG", fig, "Data for the PhaseTripleProduct recursion figure (ptpfig.js)."),
        "flow.js": js("PTP_FLOW", flow, "Data for the PhaseTripleProduct algorithm-flow diagram (docs/layers.js)."),
        "champions.js": js("PTP_CHAMPIONS", ch, "Benchmark champions (structural score) per target, from leaderboard/best-known.md."),
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
