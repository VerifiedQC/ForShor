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

  // ------------------------------------------------------------ ① the policy
  // The example follows the figure drawn for the page (n = 128); the widths are
  // illustrative, not computed by the compiler for a particular pair of tables.
  var POL = D.policy;
  txt(svg, 12, 24, "① Policy", "pt ph");
  var card = el("g", { "class": "pcard" });
  card.appendChild(el("rect", { x: 10, y: 34, width: 300, height: 446, rx: 10 }));
  svg.appendChild(card);
  function rowBtn(id, x, y, w, s, cls, tx) {
    var g = el("g", { "class": "pn prow", "data-id": id, tabindex: "0", role: "button" });
    g.appendChild(el("rect", { x: x, y: y - 16, width: w, height: 23, rx: 4 }));
    txt(g, tx || x + 8, y, s, cls || "pt");
    svg.appendChild(g);
    return g;
  }
  rowBtn("policy", 16, 58, 288, "policy  P = ((w̲₁, T⁽¹⁾), (w̲₂, T⁽²⁾), …)", "pt pt-b");
  var lg1 = rowBtn("prog", 16, 84, 288, "T⁽¹⁾ = (k, p, Π),  k = 3  (see ②)", null, 46);
  lg1.appendChild(el("rect", { x: 26, y: 73, width: 12, height: 12, "class": "psw psw1" }));
  var lg2 = rowBtn("band2", 16, 108, 288, "T⁽²⁾ = (k, p, Π),  k = 2", null, 46);
  lg2.appendChild(el("rect", { x: 26, y: 97, width: 12, height: 12, "class": "psw psw2" }));
  txt(svg, 160, 136, "Example: n = " + POL.n, "pt pt-b", "middle");
  txt(svg, 160, 154, "w̲₁ > w̲₂;  on width w use the first T⁽ʲ⁾ with w ≥ w̲ⱼ", "pt pt-s", "middle");
  // bands as shaded regions, widest first
  var top = 166, rowH = 44, bx = 24, bw = 272;
  var bandY = [], y = top;
  POL.bands.forEach(function (b, bi) {
    var rows = POL.levels.filter(function (l) { return l.band === bi; });
    var h = rows.length * rowH + 8;
    var g = el("g", { "class": "pn pbandreg pbr" + (bi + 1), "data-id": "band" + (bi + 1), tabindex: "0", role: "button" });
    g.appendChild(el("rect", { x: bx, y: y, width: bw, height: h }));
    txt(g, bx + 6, y + 30, "T⁽" + "¹²³"[bi] + "⁾", "pt pt-b");
    txt(g, bx + 6, y + 48, "k = " + b.k, "pt pt-b");
    txt(g, bx + 6, y + 64, bi === 0 ? "w ≥ w̲₁" : "w̲₂ ≤ w < w̲₁", "pt pt-s");
    svg.appendChild(g);
    bandY.push(y); y += h;
  });
  var gbase = el("g", { "class": "pn pbandreg pbr0", "data-id": "base", tabindex: "0", role: "button" });
  gbase.appendChild(el("rect", { x: bx, y: y, width: bw, height: rowH + 8 }));
  txt(gbase, bx + 6, y + 28, "base case", "pt pt-b");
  txt(gbase, bx + 6, y + 44, "w < w̲₂", "pt pt-s");
  svg.appendChild(gbase);
  var baseY = y;
  // width rows
  var ry = {};
  POL.levels.forEach(function (l, i) {
    var y0 = (l.band >= 0 ? bandY[l.band] + 4 + POL.levels.filter(function (m, j) { return j < i && m.band === l.band; }).length * rowH : baseY + 4) + 4;
    ry[i] = y0;
    var g = el("g", { "class": "pn pwrow", "data-id": l.band >= 0 ? "width" : "base", tabindex: "0", role: "button" });
    g.appendChild(el("rect", { x: 104, y: y0, width: 184, height: 32, rx: 6 }));
    txt(g, 114, y0 + 21, "w" + SUB[i] + (i === 0 ? " = n = " : " = ") + l.w, "pt pt-m");
    txt(g, 280, y0 + 21, l.band >= 0 ? "k" + SUB[i] + " = " + POL.bands[l.band].k : "D = " + i, "pt pt-m", "end");
    svg.appendChild(g);
    if (i > 0) arrow(196, ry[i - 1] + 32, 196, y0 - 1, "pa pa-thin");
  });
  // thresholds: dashed lines at band boundaries
  POL.bands.forEach(function (b, bi) {
    var yl = bi + 1 < POL.bands.length ? bandY[bi + 1] : baseY;
    svg.appendChild(el("line", { x1: bx, y1: yl, x2: bx + bw, y2: yl, "class": "pthr" }));
    var g = el("g", { "class": "pn pthrlab", "data-id": "thr", tabindex: "0", role: "button" });
    g.appendChild(el("rect", { x: bx + 4, y: yl - 10, width: 66, height: 20, rx: 10 }));
    txt(g, bx + 37, yl + 5, "w̲" + SUB[bi + 1] + " = " + b.threshold, "pt pt-s pt-thr", "middle");
    svg.appendChild(g);
  });
  var gf = el("g", { "class": "pn prow", "data-id": "width", tabindex: "0", role: "button" });
  gf.appendChild(el("rect", { x: 16, y: baseY + rowH + 14, width: 288, height: 44, rx: 4 }));
  txt(gf, 160, baseY + rowH + 32, "(k₀, k₁, …) = (" + POL.levels.filter(function (l) { return l.band >= 0; })
    .map(function (l) { return POL.bands[l.band].k; }).join(", ") + ")", "pt pt-b", "middle");
  txt(gf, 160, baseY + rowH + 51, "wᵢ₊₁ = W(wᵢ) < wᵢ", "pt pt-b", "middle");
  svg.appendChild(gf);

  // ------------------------------------------------------------ ② one level
  var tg = el("g", { "class": "pn ptitle", "data-id": "prog", tabindex: "0", role: "button" });
  tg.appendChild(el("rect", { x: 334, y: 6, width: 560, height: 26, rx: 4 }));
  txt(tg, 340, 24, "② T⁽¹⁾ (k = " + D.k + "):  PP(φxz) → 2k − 1 = " + D.q + " PhaseProducts", "pt ph");
  svg.appendChild(tg);
  function uName(id) { return "Π⁽" + "⁰¹²"[+id.slice(1)] + "⁾"; }
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
      // one bar on the x wires and one on the z wires: the same ops act on both
      [0, 1].forEach(function (side) {
        var g = node(s.name, x + side * 25, wy(side) - 16, 24, wy(4) - wy(0) + 32, [], "pu");
        txt(g, x + side * 25 + 12, (wy(side) + wy(side + 4)) / 2 + 5, uName(s.name), "pt pt-b pt-pi", "middle");
      });
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
    var lab = uName(b.id) + ":";
    var per = b.id === "U1" ? 3 : 2, chunks = [];
    for (var i = 0; i < s.math.length; i += per) chunks.push(s.math.slice(i, i + per).join(", "));
    txt(g, b.x + 10, 390, lab, "pt pt-b");
    chunks.forEach(function (c, i) { txt(g, b.x + 10, 410 + i * 18, c, "pt pt-m"); });
    svg.appendChild(g);
  });
  txt(svg, 340, 474, "rⱼ = (xⱼ, zⱼ): each op acts on the x and z chunks alike", "pt pt-s");
  // the table as a strip
  var strip = el("g", { "class": "pn pstrip", "data-id": "prog", tabindex: "0", role: "button" });
  strip.appendChild(el("rect", { x: 340, y: 484, width: 562, height: 30, rx: 6 }));
  txt(strip, 352, 504, "T⁽¹⁾:  Π⁽⁰⁾ → p = " + D.points.slice(0, 3).join(", ") + " → Π⁽¹⁾ → p = " +
    D.points.slice(3).join(", ") + " → Π⁽²⁾", "pt");
  svg.appendChild(strip);

  // ------------------------------------------------------------ ③ recursion
  txt(svg, 930, 24, "③ Recursive PP blocks", "pt ph");
  D.pps.forEach(function (p, i) {
    var y = 60 + i * 60;
    node("child", 930, y, 92, 40, ["PP at " + p.point], "pchild");
    var c = el("g", { "class": "pnum" });
    c.appendChild(el("circle", { cx: 930, cy: y, r: 10 }));
    txt(c, 930, y + 5, String(p.n), "pt pt-n", "middle");
    svg.appendChild(c);
    for (var t = -1; t <= 1; t++) arrow(1023, y + 20, 1046, y + 20 + t * 9, "pa pa-thin");
    node("child", 1048, y, 92, 40, [D.q + " PPs", { s: "via T⁽¹⁾", cls: "pt pt-s" }], "pchild");
    txt(svg, 1153, y + 25, "…", "pt pt-b", "middle");
  });
  var gB = node("base", 1168, 60, 66, 280, ["base", "case", "", "M", "leaves"], "pbase");
  var tM = gB.querySelectorAll("text")[3];
  tM.appendChild(el("tspan", { "baseline-shift": "sub", "font-size": "11px" }, "D"));
  txt(svg, 1090, 372, "sum over nodes", "pt pt-s", "middle");
  txt(svg, 1090, 388, "(arithmetic + PP leaves)", "pt pt-s", "middle");
  arrow(1200, 342, 1200, 410);
  node("bound", 930, 410, 304, 84,
    [{ s: "Output: gate count of PP(φxz)", cls: "pt pt-b" },
     { s: "Lean, one band: order finding", cls: "pt pt-m" },
     { s: "in O(n^(1+log_k(2k−1))) gates", cls: "pt pt-m" }], "pout");

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
  // Unicode math from data/pp.js ("x₀ − 2x₁ + 4x₂", "r₁ += r₀", "∞") as inline MathJax.
  function tex(u) {
    return "\\(" + String(u).replace(/−/g, "-").replace(/([+-])=/g, "\\mathrel{$1}=")
      .replace(/[₀-₉]/g, function (d) { return "_" + SUB.indexOf(d); }).replace(/∞/g, "\\infty") + "\\)";
  }
  function uTex(id) { return "\\(\\Pi^{(" + id.slice(1) + ")}\\)"; }
  function stateTable(s) {
    var h = '<table class="pstate"><tr><th></th><th>before</th><th>after</th></tr>';
    for (var i = 0; i < s.before.length; i++)
      h += "<tr><td>\\(r_" + i + "\\)</td><td>" + tex(s.before[i]) + "</td><td>" + tex(s.after[i]) + "</td></tr>";
    return h + "</table>";
  }
  function uPanel(id) {
    var s = segU[id], n = uTex(id);
    var t = "<p>" + n + " is the arithmetic between two rounds of phase products: " + s.ops.length +
      " in-place additions of a shifted register into another, applied to the \\(x\\) chunks and the " +
      "\\(z\\) chunks alike. In order: " + s.math.map(tex).join(", ") + ".</p>" +
      stateTable(s) +
      "<p>Each \\(r_i\\) holds an integer combination of the chunks, and that is all the table manipulates; the " +
      "compiler turns each operation into gates on the actual qubits. " +
      (id === "U2" ? "\\(\\Pi^{(2)}\\) brings every register back to its own chunk, which is admissibility condition C4: the program ends where it started, so the workspace is returned clean." :
       "Both columns are computed by running the table, not typed in.") + "</p>";
    var c = '<p class="lsnip-head">the same operations, as <code>valid_ops</code></p><pre class="lsnip lean"><code>' +
      window.leanHL(s.ops.join("\n")) + "</code></pre>" + code(S.addScaled);
    return { title: n, role: "register arithmetic", text: t, code: c };
  }
  function ppPanel(n) {
    var p = D.pps[n - 1];
    var t = "<p>Phase product " + n + " of " + D.q + ", taken on register \\(r_" + p.reg + "\\), which at this moment holds " +
      tex(p.x) + " on the \\(x\\) side and " + tex(p.z) + " on the \\(z\\) side: " +
      "the chunk polynomials evaluated at " + tex("p = " + p.point) +
      (p.point === "∞" ? " (at infinity, the leading coefficient)" : "") + ".</p>" +
      "<p>That match is admissibility condition C3. <code>ProgConsumesPts</code> walks the program; at every " +
      "<code>phaseProduct i</code> it takes the next point and requires register \\(i\\) to equal " +
      "<code>expectedRow</code> of that point, here <code>[" + p.row.join(", ") + "]</code>. Kernel-checked tables " +
      "cannot get this wrong.</p><p>The angle is not \\(\\varphi\\): each of the " + D.q + " products gets its own " +
      "interpolation coefficient times \\(\\varphi\\), chosen so that the " + D.q + " phases multiply out to " +
      "\\(\\exp(i \\varphi x z)\\). The product itself is a smaller phase product, which recurses (panel ③).</p>";
    return { title: "\\(\\mathrm{PP}\\) at " + tex("p = " + p.point), role: "one of the " + D.q + " smaller products", text: t,
      code: code(S.consumes) + code(S.expectedRow) + code(S.phaseCoeff) };
  }
  var P = {
    k: function () { return { title: "\\(k = " + D.k + "\\)", role: "the arity", text:
      "<p>Each operand is split into \\(k\\) chunks of about \\(n/k\\) bits. A product of two " +
      "degree-\\((k-1)\\) chunk polynomials has degree \\(2k-2\\), so it is pinned down by its values at " +
      "<code>q k</code> = \\(2k - 1\\) points: here " + D.q + " phase products on chunk-sized registers replace one on the full width.</p>" +
      "<p>\\(k\\) is the only number that matters for the exponent: the gate count grows as " +
      "\\(n^{\\log_k(2k-1)}\\), which is \\(n^{1.585}\\) at \\(k = 2\\), \\(n^{1.465}\\) at \\(k = 3\\), and tends to \\(n\\).</p>",
      code: code(S.q) + code(S.exponent) }; },
    pts: function () { return { title: tex("p = (" + D.points.join(", ") + ")"), role: "the interpolation points", text:
      "<p>The " + D.q + " points, in the order the program consumes them: three after \\(\\Pi^{(0)}\\), two after " +
      "\\(\\Pi^{(1)}\\). A point is an integer or <code>frac m</code>, meaning \\(1/m\\); <code>frac 0</code> is the point " +
      "at infinity, whose row picks out the leading coefficient.</p><p>Admissibility asks only that the points be distinct " +
      "(C2, equivalent to the interpolation matrix being invertible) and that they be consumed in this order (C3). The " +
      "points are submission data, not a function of \\(k\\): the reference table uses " +
      "<code>genInterpolationPoints 3</code> = \\(0, -1, 1, -2, 2\\) on a single register.</p>",
      code: code(S.Point) + code(S.expectedRow) + code(S.genPts) }; },
    prog: function () { return { title: "Prog 3", role: "the table", text:
      "<p>The table is a straight-line program over \\(k\\) registers: <code>addScaled</code>, <code>negate</code>, " +
      "<code>shiftL</code>, <code>shiftR</code>, and <code>phaseProduct i</code> checkpoints. It is the one degree of freedom of " +
      "the whole construction; every theorem about the phase product takes it as a parameter, so one proof serves every " +
      "admissible table.</p><p>The table drawn here is one admissible \\(k = 3\\) table, picked because it reads well; " +
      "it is not a file in the repository. On the right it is written out as a <code>Prog 3</code>. It was checked by " +
      "executing it with a direct mirror of the Lean definitions of <code>run?</code> and <code>ProgConsumesPts</code>, which " +
      "agrees with the kernel's verdicts on the repository's own tables; it has not itself been through the kernel.</p>",
      code: '<p class="lsnip-head">this figure\'s table</p><pre class="lsnip lean"><code>' + window.leanHL(D.tableLean) +
        "</code></pre>" + code(S.valid_ops) + code(S.Prog) + code(S.run) }; },
    U0: function () { return uPanel("U0"); }, U1: function () { return uPanel("U1"); }, U2: function () { return uPanel("U2"); },
    width: function () {
      var lv = POL.levels.map(function (l, i) { return "\\(w_" + i + " = " + l.w + "\\)" +
        (l.band >= 0 ? " (\\(T^{(" + (l.band + 1) + ")}\\), \\(k = " + POL.bands[l.band].k + "\\))" : " (base case)"); }).join(", ");
      return { title: "Widths per level", role: "\\(w_{i+1} = W_T(w_i) < w_i\\)", text:
      "<p>Each level is one phase product width. The policy looks at the width, picks a table, and the table's " +
      "arithmetic fixes the next width: a \\(k\\)-th of the current one, plus a constant number of carry bits, because " +
      "adding shifted chunks grows them by a bounded amount. That is <code>nextSignedWidth</code>, and " +
      "<code>prog_balanced_nextSignedWidth</code> shows that for any table there is a \\(c\\) with " +
      "<code>nextSignedWidth</code> \\(\\le \\lceil w/k \\rceil + c\\).</p><p>In the example: " + lv + ". The arities used, top to bottom, are the " +
      "list \\((k_0, \\ldots, k_{D-1})\\). These widths illustrate the shape of a two-band policy; they were not produced by " +
      "running the compiler on a particular pair of tables.</p><p>The constant \\(c\\) is why the recursion has to " +
      "stop: once \\(\\lceil w/k \\rceil + c\\) is no smaller than \\(w\\), splitting no longer helps.</p>",
      code: code(S.nextSignedWidth) + code(S.balanced) }; },
    policy: function () { return { title: "A policy", role: "a table for each range of widths", text:
      "<p>A policy is a list of bands \\((\\underline{w}_j, T^{(j)})\\), widest first, with strictly decreasing thresholds. At a node " +
      "of width \\(w\\), <code>choose</code> returns the table of the first band whose threshold is at most " +
      "\\(w\\); below the last threshold it returns <code>none</code>, the base case. The policy is keyed on width, " +
      "not depth, because the width at depth 3 depends on the choices made at depths 1 and 2.</p><p>A single-table " +
      "submission is the one-band policy at threshold 0 (<code>constPolicy</code>). Admissibility of a policy is " +
      "admissibility of every table it can pick; nothing else about it is trusted.</p>",
      code: code(S.band) + code(S.policy) + code(S.choose) + code(S.constPolicy) }; },
    band1: function () { var b = POL.bands[0]; return { title: "\\(T^{(1)}\\) band", role: "\\(k = " + b.k + ",\\ w \\ge " + b.threshold + "\\)", text:
      "<p>The widest band: every node of width at least \\(\\underline{w}_1 = " + b.threshold + "\\) is split with " +
      "\\(T^{(1)}\\), the \\(k = " + b.k + "\\) table drawn in panel ②, into " + (2 * b.k - 1) + " smaller phase products.</p>" +
      "<p>Click the title of panel ② or a \\(\\Pi\\) bar for the table itself.</p>",
      code: code(S.band) + code(S.choose) }; },
    band2: function () { var b = POL.bands[1]; return { title: "\\(T^{(2)}\\) band", role: "\\(k = " + b.k + ",\\ " + b.threshold + " \\le w < " + POL.bands[0].threshold + "\\)", text:
      "<p>The second band: nodes of width from \\(\\underline{w}_2 = " + b.threshold + "\\) up to \\(\\underline{w}_1\\) use a " +
      "\\(k = " + b.k + "\\) table, which splits into " + (2 * b.k - 1) + " phase products (Karatsuba-shaped). The " +
      "figure does not fix which \\(k = 2\\) table; any admissible one may fill this band.</p>",
      code: code(S.band) + code(S.choose) }; },
    thr: function () { return { title: "Thresholds", role: "\\(\\underline{w}_1 > \\underline{w}_2 > \\cdots\\)", text:
      "<p>The underlined \\(\\underline{w}_j\\) are the policy's thresholds; the plain \\(w_i\\) are the widths the recursion " +
      "actually reaches. The thresholds must strictly decrease (<code>sorted</code>, closed by <code>decide</code> in a " +
      "submission), so the bands partition the widths and the compiled dispatcher is a chain of guards.</p>" +
      "<p>Here " + POL.bands.map(function (b, i) { return "\\(\\underline{w}_" + (i + 1) + " = " + b.threshold + "\\)"; }).join(", ") +
      ": a width of " + POL.levels[2].w + " falls below \\(\\underline{w}_1\\) and switches to \\(T^{(2)}\\); a width of " +
      POL.levels[POL.levels.length - 1].w + " falls below \\(\\underline{w}_2\\) and takes the base case.</p>",
      code: code(S.policy) + code(S.choose) }; },
    base: function () { return { title: "Base case", role: "naive phase product", text:
      "<p>The recursion is <code>Policy.signedPlanOf</code>, the only recursive definition in the lowering. At each node it " +
      "asks the policy for a table at this width; if there is none, or if the table would not shrink the width " +
      "(<code>nextSignedWidth x z T.ops &lt; phaseInputSize x z</code> fails), it stops and emits the naive phase product " +
      "<code>LowGate.Naive_SignedPhaseProd</code>. Otherwise it takes one step of the table and calls itself on each of the " +
      "children.</p><p>Termination is by that same test (<code>termination_by phaseInputSize x z</code>), so the recursion " +
      "depth \\(D\\) is about \\(\\log_k n\\). \\(M_D\\) counts the leaves: the product of " +
      "\\(2k_i - 1\\) over the levels, which is \\(" + D.q + "^D\\) when one table is used throughout.</p>",
      code: code(S.signedPlanOf) }; },
    child: function () { return { title: "Recursive PP blocks", role: "each child is lowered again", text:
      "<p>Each of the " + D.q + " products in panel ② is itself a phase product, of the next width, and is lowered the same " +
      "way: the policy picks a table at that width and the step repeats. In <code>signedPlanOf</code> this is the " +
      "<code>recurse</code> argument handed to the per-table step, one call per child. In the example the children of the " +
      "top node have width " + POL.levels[1].w + ", still in the \\(T^{(1)}\\) band, hence “via \\(T^{(1)}\\)”.</p><p>Correctness " +
      "(<code>Policy.lowerSignedPhaseProduct_correct</code>) holds for any admissible policy. The gate-count theorems are " +
      "stated for one band, the constant policy: one table at every width.</p>",
      code: code(S.signedPlanOf) + code(S.ppcorrectPolicy) }; },
    bound: function () { return { title: "The gate count", role: "one band: \\(O(n^{1+\\log_k(2k-1)})\\)", text:
      "<p>Summing over the tree: a node of width \\(w\\) costs its own arithmetic, linear in \\(w\\) " +
      "(<code>phaseProgramOverhead_linear</code>), plus its children of width at most \\(\\lceil w/k \\rceil + c\\). With one table " +
      "at every width that recurrence solves to \\(C \\cdot n^{\\log_k(2k-1)}\\), and <code>PhaseProductGateCountBound</code> " +
      "is exactly that statement about the lowered circuit's <code>LowGate.gateCount</code>.</p><p>Order finding uses " +
      "\\(O(n)\\) modular multiplications built from these, so <code>ShorGateCountBound</code> bounds the whole " +
      "order-finding circuit by \\(C \\cdot n^{2+\\varepsilon}\\) whenever \\(\\log_k(2k-1) \\le 1 + \\varepsilon\\); the proof goes " +
      "through \\(n^{1 + \\log_k(2k-1)}\\). Both are stated for the constant policy.</p><p>The count is the gate " +
      "count of the repository's cost model (<code>shorGateCostModel</code>), not a T count.</p>",
      code: code(S.overhead) + code(S.exponent) + code(S.bound) + code(S.shorBound) }; },
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
    if (window.clearMath) window.clearMath(panel);
    panel.innerHTML = '<div class="ldetail-inner"><div class="ldetail-grid"><div class="ldetail-text"><h3>' + esc(d.title) +
      ' <span class="lrole">' + esc(d.role) + "</span></h3>" + d.text +
      '<p><a href="#layer-PhaseProduct">The PhaseProduct layer in the graph above</a></p></div><div class="ldetail-code">' +
      d.code + "</div></div></div>";
    if (instant) panel.classList.add("instant");
    void panel.offsetHeight;
    panel.classList.add("open");
    if (window.typesetMath) window.typesetMath(panel);
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
