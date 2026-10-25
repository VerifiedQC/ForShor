// The interactive PhaseProduct recursion figure on the project page.
// Data: data/pp.js (the k = 3 table, register contents computed by executing
// it with a mirror of the Lean semantics, and verbatim Lean snippets).
// Three panels drawn as one SVG; every labelled element is clickable and
// opens a panel below the figure with the explanation and the Lean source.
(function () {
  "use strict";
  var D = window.PPFIG;
  var root = document.getElementById("ppfig");
  if (!D || !root) return;
  var NS = "http://www.w3.org/2000/svg";
  var SUB = "₀₁₂₃₄₅₆₇₈₉";

  function esc(s) { return String(s).replace(/[&<>"]/g, function (c) { return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]; }); }
  function el(name, attrs, text) {
    var e = document.createElementNS(NS, name);
    for (var k in attrs) e.setAttribute(k, attrs[k]);
    if (text != null) e.textContent = text;
    return e;
  }
  function txt(parent, x, y, s, cls, anchor) {
    var t = el("text", { x: x, y: y, "class": cls || "pt", "text-anchor": anchor || "start" }, s);
    parent.appendChild(t); return t;
  }
  // a clickable group: rect + text lines
  function node(id, x, y, w, h, lines, cls) {
    var g = el("g", { "class": "pn " + (cls || ""), "data-id": id, tabindex: "0", role: "button" });
    g.appendChild(el("rect", { x: x, y: y, width: w, height: h, rx: 6 }));
    var lh = 17, y0 = y + h / 2 - (lines.length - 1) * lh / 2 + 5;
    lines.forEach(function (l, i) {
      var c = typeof l === "string" ? { s: l } : l;
      txt(g, x + w / 2, y0 + i * lh, c.s, c.cls || (i === 0 ? "pt pt-b" : "pt"), "middle");
    });
    svg.appendChild(g);
    return g;
  }
  function arrow(x1, y1, x2, y2, cls) {
    svg.appendChild(el("line", { x1: x1, y1: y1, x2: x2, y2: y2, "class": cls || "pa", "marker-end": "url(#pp-arrow)" }));
  }

  var W = 1240, H = 520;
  var svg = el("svg", { viewBox: "0 0 " + W + " " + H, "class": "ppsvg", role: "img",
    "aria-label": "The PhaseProduct recursion at k = 3; click any element for details" });
  svg.innerHTML = '<defs><marker id="pp-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z"/></marker></defs>';
  root.appendChild(svg);

  // ------------------------------------------------------------ ① the table
  txt(svg, 12, 24, "① Design: one table", "pt ph");
  var card = el("g", { "class": "pcard" });
  card.appendChild(el("rect", { x: 10, y: 38, width: 290, height: 124, rx: 8 }));
  svg.appendChild(card);
  txt(svg, 24, 60, "design parameters (k, p, Prog" + "ₖ)", "pt pt-b");
  function rowBtn(id, y, s) {
    var g = el("g", { "class": "pn prow", "data-id": id, tabindex: "0", role: "button" });
    g.appendChild(el("rect", { x: 16, y: y - 16, width: 278, height: 24, rx: 4 }));
    txt(g, 24, y, s, "pt");
    svg.appendChild(g);
  }
  rowBtn("k", 86, "k = " + D.k + "   (" + D.q + " = 2k − 1 points)");
  rowBtn("pts", 112, "p = (" + D.points.slice(0, 3).join(", ") + " | " + D.points.slice(3).join(", ") + ")");
  rowBtn("prog", 138, "Prog₃ = U₀, U₁, U₂  (" + D.segments.filter(function (s) { return s.kind === "U"; })
    .reduce(function (a, s) { return a + s.ops.length; }, 0) + " ops)");
  var lv = [
    { id: "width", y: 182, a: "level 0:  h₀ = n", b: "1 node" },
    { id: "width", y: 252, a: "level 1:  h₁", b: D.q + " nodes" },
    { id: "width", y: 322, a: "level 2:  h₂", b: D.q * D.q + " nodes" },
  ];
  lv.forEach(function (l, i) {
    var g = node(l.id, 10, l.y, 290, 40, [], "plevel");
    txt(g, 24, l.y + 25, l.a, "pt pt-b");
    txt(g, 288, l.y + 25, l.b, "pt pt-i", "end");
    if (i < 2) arrow(40, l.y + 40, 40, l.y + 68);
  });
  txt(svg, 52, 245, "next width ≤ ⌈h / k⌉ + c", "pt pt-s");
  txt(svg, 40, 385, "⋮", "pt pt-b");
  var gb = node("base", 10, 400, 290, 52, [], "plevel pbase");
  txt(gb, 24, 422, "base level D:  naive PP", "pt pt-b");
  txt(gb, 288, 422, D.q + "ᴰ leaves", "pt pt-i", "end");
  txt(gb, 24, 442, "stop once the width no longer shrinks", "pt pt-s");

  // ------------------------------------------------------------ ② one level
  txt(svg, 340, 24, "② PP(φ·x·z) → 2k − 1 = " + D.q + " phase products", "pt ph");
  var wy = function (w) { return 64 + w * 50; };           // wires x0 z0 x1 z1 x2 z2
  var names = ["x₀", "z₀", "x₁", "z₁", "x₂", "z₂"];
  for (var w = 0; w < 6; w++) {
    svg.appendChild(el("line", { x1: 362, y1: wy(w), x2: 892, y2: wy(w), "class": "pw" }));
    txt(svg, 356, wy(w) + 5, names[w], "pt pt-w", "end");
    txt(svg, 898, wy(w) + 5, names[w], "pt pt-w");
  }
  var cols = { U0: 372, PP1: 432, U1: 580, PP2: 640, U2: 790 };
  var segU = {}, ppIdx = 0, ppGroup = 0;
  D.segments.forEach(function (s) {
    if (s.kind === "U") {
      segU[s.name] = s;
      var x = cols[s.name];
      var g = node(s.name, x, wy(0) - 18, 44, wy(5) - wy(0) + 36, [], "pu");
      txt(g, x + 22, (wy(0) + wy(5)) / 2 + 6, s.name.replace(/(\d)/, function (d) { return SUB[+d]; }), "pt pt-b", "middle");
    } else {
      ppGroup++;
      var x0 = ppGroup === 1 ? cols.PP1 : cols.PP2;
      for (var j = 0; j < s.count; j++) {
        var p = D.pps[ppIdx++];
        var top = wy(2 * p.reg) - 20, h = wy(2 * p.reg + 1) - wy(2 * p.reg) + 40;
        var bx = x0 + (ppGroup === 1 ? 0 : 0);
        var g2 = node("pp" + p.n, bx, top, 132, h,
          [{ s: "PP at p = " + p.point, cls: "pt pt-b" }, { s: p.x, cls: "pt pt-m" }, { s: p.z, cls: "pt pt-m" }], "ppp");
        var c = el("g", { "class": "pnum" });
        c.appendChild(el("circle", { cx: bx + 4, cy: top + 2, r: 11 }));
        txt(c, bx + 4, top + 7, String(p.n), "pt pt-n", "middle");
        g2.appendChild(c);
      }
    }
  });
  // the operation band under the wires
  var band = [{ id: "U0", x: 340, w: 150 }, { id: "U1", x: 496, w: 250 }, { id: "U2", x: 752, w: 150 }];
  band.forEach(function (b) {
    var s = segU[b.id];
    var g = el("g", { "class": "pn pband", "data-id": b.id, tabindex: "0", role: "button" });
    g.appendChild(el("rect", { x: b.x, y: 368, width: b.w, height: 84, rx: 6 }));
    var lab = b.id.replace(/(\d)/, function (d) { return SUB[+d]; }) + ":";
    var per = b.id === "U1" ? 3 : 2, chunks = [];
    for (var i = 0; i < s.math.length; i += per) chunks.push(s.math.slice(i, i + per).join(", "));
    txt(g, b.x + 10, 390, lab, "pt pt-b");
    chunks.forEach(function (c, i) { txt(g, b.x + 10, 410 + i * 18, c, "pt pt-m"); });
    svg.appendChild(g);
  });
  txt(svg, 340, 474, "rᵢ = (xᵢ, zᵢ): each op acts on the x and z chunks alike", "pt pt-s");
  // the table as a strip
  var strip = el("g", { "class": "pn pstrip", "data-id": "prog", tabindex: "0", role: "button" });
  strip.appendChild(el("rect", { x: 340, y: 484, width: 562, height: 30, rx: 6 }));
  txt(strip, 352, 504, "table:  U₀ → p = " + D.points.slice(0, 3).join(", ") + " → U₁ → p = " +
    D.points.slice(3).join(", ") + " → U₂", "pt");
  svg.appendChild(strip);

  // ------------------------------------------------------------ ③ recursion
  txt(svg, 930, 24, "③ Recursive PP blocks", "pt ph");
  txt(svg, 975, 50, "h₁", "pt pt-i", "middle");
  txt(svg, 1090, 50, "h₂", "pt pt-i", "middle");
  txt(svg, 1201, 50, "level D", "pt pt-i", "middle");
  D.pps.forEach(function (p, i) {
    var y = 60 + i * 60;
    node("child", 930, y, 92, 40, ["PP at " + p.point], "pchild");
    var c = el("g", { "class": "pnum" });
    c.appendChild(el("circle", { cx: 930, cy: y, r: 10 }));
    txt(c, 930, y + 5, String(p.n), "pt pt-n", "middle");
    svg.appendChild(c);
    for (var t = -1; t <= 1; t++) arrow(1023, y + 20, 1046, y + 20 + t * 9, "pa pa-thin");
    node("child", 1048, y, 92, 40, [D.q + " PPs", { s: "same table", cls: "pt pt-s" }], "pchild");
    txt(svg, 1153, y + 25, "…", "pt pt-b", "middle");
  });
  node("base", 1168, 60, 66, 280, ["base", "case", "PP", "", D.q + "ᴰ", "leaves"], "pbase");
  txt(svg, 1090, 372, "sum over nodes", "pt pt-s", "middle");
  txt(svg, 1090, 388, "(arithmetic + PP leaves)", "pt pt-s", "middle");
  arrow(1200, 342, 1200, 410);
  node("bound", 930, 412, 304, 70,
    [{ s: "Output: gate count of PP(φ·x·z) on n bits", cls: "pt pt-b" },
     { s: "width ⌈h/k⌉ + c per level  ⇒  O(n^log_k(2k−1))", cls: "pt pt-m" }], "pout");

  // ------------------------------------------------------------ detail panels
  var S = D.snippets;
  function code(s, label) {
    var h = '<p class="lsnip-head"><code>' + esc(s.name) + "</code> · " +
      '<a href="' + D.repo + "/" + D.root + "/" + s.file + "#L" + s.line + '">' +
      esc(s.file.replace(/^Implementation\//, "")) + ":" + s.line + "</a></p>";
    h += '<pre class="lsnip lean"><code>' + (window.leanHL ? window.leanHL(s.code) : esc(s.code)) + "</code></pre>";
    if (label) h += '<p class="lsnip-note">' + label + "</p>";
    return h;
  }
  function stateTable(s) {
    var h = '<table class="pstate"><tr><th></th><th>before</th><th>after</th></tr>';
    for (var i = 0; i < s.before.length; i++)
      h += "<tr><td>r" + SUB[i] + "</td><td>" + esc(s.before[i]) + "</td><td>" + esc(s.after[i]) + "</td></tr>";
    return h + "</table>";
  }
  function uPanel(id) {
    var s = segU[id], n = id.replace(/(\d)/, function (d) { return SUB[+d]; });
    var t = "<p>" + n + " is the arithmetic between two rounds of phase products: " + s.ops.length +
      " in-place additions of a shifted register into another, applied to the <code>x</code> chunks and the " +
      "<code>z</code> chunks alike. In order: " + s.math.map(function (m) { return "<code>" + esc(m) + "</code>"; }).join(", ") + ".</p>" +
      stateTable(s) +
      "<p>Each <code>rᵢ</code> holds an integer combination of the chunks, and that is all the table manipulates; the " +
      "compiler turns each operation into gates on the actual qubits. " +
      (id === "U2" ? "U₂ brings every register back to its own chunk, which is admissibility condition C4: the program ends where it started, so the workspace is returned clean." :
       "Both columns are computed by running the table, not typed in.") + "</p>";
    var c = '<p class="lsnip-head">the same operations, as <code>valid_ops</code></p><pre class="lsnip lean"><code>' +
      window.leanHL(s.ops.join("\n")) + "</code></pre>" + code(S.addScaled);
    return { title: n, role: "register arithmetic", text: t, code: c };
  }
  function ppPanel(n) {
    var p = D.pps[n - 1];
    var t = "<p>Phase product " + n + " of " + D.q + ", taken on register <code>r" + SUB[p.reg] + "</code>, which at this moment holds " +
      "<code>" + esc(p.x) + "</code> on the <code>x</code> side and <code>" + esc(p.z) + "</code> on the <code>z</code> side: " +
      "the chunk polynomials evaluated at <code>p = " + esc(p.point) + "</code>" +
      (p.point === "∞" ? " (at infinity, the leading coefficient)" : "") + ".</p>" +
      "<p>That match is admissibility condition C3. <code>ProgConsumesPts</code> walks the program; at every " +
      "<code>phaseProduct i</code> it takes the next point and requires register <code>i</code> to equal " +
      "<code>expectedRow</code> of that point, here <code>[" + p.row.join(", ") + "]</code>. Kernel-checked tables " +
      "cannot get this wrong.</p><p>The angle is not <code>φ</code>: each of the " + D.q + " products gets its own " +
      "interpolation coefficient times <code>φ</code>, chosen so that the " + D.q + " phases multiply out to " +
      "<code>exp(i·φ·x·z)</code>. The product itself is a smaller phase product, which recurses (panel ③).</p>";
    return { title: "PP at p = " + p.point, role: "one of the " + D.q + " smaller products", text: t,
      code: code(S.consumes) + code(S.expectedRow) + code(S.phaseCoeff) };
  }
  var P = {
    k: function () { return { title: "k = " + D.k, role: "the arity", text:
      "<p>Each operand is split into <code>k</code> chunks of about <code>n/k</code> bits. A product of two " +
      "degree-<code>(k−1)</code> chunk polynomials has degree <code>2k−2</code>, so it is pinned down by its values at " +
      "<code>q k = 2k − 1</code> points: here " + D.q + " phase products on chunk-sized registers replace one on the full width.</p>" +
      "<p><code>k</code> is the only number that matters for the exponent: the gate count grows as " +
      "<code>n^(log_k(2k−1))</code>, which is <code>n^1.585</code> at <code>k = 2</code>, <code>n^1.465</code> at <code>k = 3</code>, and tends to <code>n</code>.</p>",
      code: code(S.q) + code(S.exponent) }; },
    pts: function () { return { title: "p = (" + D.points.join(", ") + ")", role: "the interpolation points", text:
      "<p>The " + D.q + " points, in the order the program consumes them: three after <code>U₀</code>, two after " +
      "<code>U₁</code>. A point is an integer or <code>frac m</code>, meaning <code>1/m</code>; <code>frac 0</code> is the point " +
      "at infinity, whose row picks out the leading coefficient.</p><p>Admissibility asks only that the points be distinct " +
      "(C2, equivalent to the interpolation matrix being invertible) and that they be consumed in this order (C3). The " +
      "points are submission data, not a function of <code>k</code>: the reference table uses " +
      "<code>genInterpolationPoints 3</code> = <code>0, −1, 1, −2, 2</code> on a single register.</p>",
      code: code(S.Point) + code(S.expectedRow) + code(S.genPts) }; },
    prog: function () { return { title: "Prog₃", role: "the table", text:
      "<p>The table is a straight-line program over <code>k</code> registers: <code>addScaled</code>, <code>negate</code>, " +
      "<code>shiftL</code>, <code>shiftR</code>, and <code>phaseProduct i</code> checkpoints. It is the one degree of freedom of " +
      "the whole construction; every theorem about the phase product takes it as a parameter, so one proof serves every " +
      "admissible table.</p><p>The table drawn here is one admissible <code>k = 3</code> table, picked because it reads well; " +
      "it is not a file in the repository. On the right it is written out as a <code>Prog 3</code>. It was checked by " +
      "executing it with a direct mirror of the Lean definitions of <code>run?</code> and <code>ProgConsumesPts</code>, which " +
      "agrees with the kernel's verdicts on the repository's own tables; it has not itself been through the kernel.</p>",
      code: '<p class="lsnip-head">this figure\'s table</p><pre class="lsnip lean"><code>' + window.leanHL(D.tableLean) +
        "</code></pre>" + code(S.valid_ops) + code(S.Prog) + code(S.run) }; },
    U0: function () { return uPanel("U0"); }, U1: function () { return uPanel("U1"); }, U2: function () { return uPanel("U2"); },
    width: function () { return { title: "Widths per level", role: "next width ≤ ⌈h/k⌉ + c", text:
      "<p>Level <code>d</code> has <code>" + D.q + "ᵈ</code> nodes, each a phase product of width <code>h_d</code>. The " +
      "width of a child is what the table's arithmetic needs: a <code>k</code>-th of the parent, plus a constant number of " +
      "carry bits, because adding shifted chunks grows them by a bounded amount. That is " +
      "<code>prog_balanced_nextSignedWidth</code>: for any table there is a <code>c</code> with " +
      "<code>nextSignedWidth ≤ ⌈w/k⌉ + c</code>.</p><p>The constant is why the recursion has to stop: once " +
      "<code>⌈w/k⌉ + c</code> is no smaller than <code>w</code>, splitting no longer helps.</p>",
      code: code(S.nextSignedWidth) + code(S.balanced) }; },
    base: function () { return { title: "Base case", role: "naive phase product", text:
      "<p>The recursion is <code>Policy.signedPlanOf</code>, the only recursive definition in the lowering. At each node it " +
      "asks the policy for a table at this width; if there is none, or if the table would not shrink the width " +
      "(<code>nextSignedWidth x z T.ops &lt; phaseInputSize x z</code> fails), it stops and emits the naive phase product " +
      "<code>LowGate.Naive_SignedPhaseProd</code>. Otherwise it takes one step of the table and calls itself on each of the " +
      "children.</p><p>Termination is by that same test (<code>termination_by phaseInputSize x z</code>), so the recursion " +
      "depth <code>D</code> is about <code>log_k n</code> and there are <code>" + D.q + "ᴰ</code> leaves.</p>",
      code: code(S.signedPlanOf) }; },
    child: function () { return { title: "Recursive PP blocks", role: "same table at every level", text:
      "<p>Each of the " + D.q + " products in panel ② is itself a phase product of width <code>h₁</code>, and is lowered the " +
      "same way: split into chunks, the same " + D.q + " points, the same program. In <code>signedPlanOf</code> this is the " +
      "<code>recurse</code> argument handed to the per-table step, one call per child.</p><p>“Same table” is the " +
      "constant policy, which is what the gate-count theorems are stated for: one table used at every width. The " +
      "correctness proof is more general and allows the policy to choose a table per width.</p>",
      code: code(S.signedPlanOf) + code(S.ppcorrect) }; },
    bound: function () { return { title: "The gate count", role: "O(n^log_k(2k−1))", text:
      "<p>Summing over the tree: a node of width <code>w</code> costs its own arithmetic, linear in <code>w</code> " +
      "(<code>phaseProgramOverhead_linear</code>), plus its " + D.q + " children of width at most <code>⌈w/k⌉ + c</code>. " +
      "That recurrence solves to <code>C · n^(log_k(2k−1))</code>, and <code>PhaseProductGateCountBound</code> is exactly that " +
      "statement about the lowered circuit's <code>LowGate.gateCount</code>, for one table at every width.</p>" +
      "<p>Modular exponentiation makes <code>O(n)</code> modular multiplications out of these, which is where the headline " +
      "<code>n^(2+ε)</code> comes from.</p>",
      code: code(S.overhead) + code(S.exponent) + code(S.bound) }; },
  };
  for (var i = 1; i <= D.pps.length; i++) (function (n) { P["pp" + n] = function () { return ppPanel(n); }; })(i);

  // ------------------------------------------------------------ interaction
  var panel = document.createElement("div");
  panel.className = "ldetail ppdetail";
  root.appendChild(panel);
  var openId = null;
  function mark(id) {
    svg.querySelectorAll(".pn").forEach(function (g) { g.classList.toggle("on", g.getAttribute("data-id") === id); });
  }
  function show(id, instant) {
    if (openId === id) { openId = null; mark(null); panel.classList.remove("open"); setHash(null); return; }
    var d = P[id]();
    openId = id; mark(id);
    panel.innerHTML = '<div class="ldetail-inner"><div class="ldetail-grid"><div class="ldetail-text"><h3>' + esc(d.title) +
      ' <span class="lrole">' + esc(d.role) + "</span></h3>" + d.text +
      '<p><a href="#layer-PhaseProduct">The PhaseProduct layer in the graph above</a></p></div><div class="ldetail-code">' +
      d.code + "</div></div></div>";
    if (instant) panel.classList.add("instant");
    void panel.offsetHeight;
    panel.classList.add("open");
    setHash(id);
  }
  function setHash(id) {
    if (!window.history || !history.replaceState) return;
    history.replaceState(null, "", location.pathname + location.search + (id ? "#pp-" + id : ""));
  }
  svg.querySelectorAll(".pn").forEach(function (g) {
    var id = g.getAttribute("data-id");
    g.addEventListener("click", function () { show(id); });
    g.addEventListener("keydown", function (e) { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); show(id); } });
  });
  var m = /^#pp-([A-Za-z0-9]+)$/.exec(location.hash || "");
  if (m && P[m[1]]) { show(m[1], true); setTimeout(function () { if (root.scrollIntoView) root.scrollIntoView({ block: "start" }); }, 0); }
})();
