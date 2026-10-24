// The interactive layer graph on the project page. Data: data/layers.js
// (rows, drawn edges, real import edges, per-layer text and verbatim Lean
// snippets). Click a layer and a panel unfolds below its row with what the
// layer proves, the theorem that carries it, and what it rests on / feeds.
(function () {
  "use strict";
  var D = window.LAYERS;
  var root = document.getElementById("layers");
  if (!D || !root) return;

  var byId = D.layers;
  var rowOf = {};
  D.rows.forEach(function (r, i) { r.forEach(function (id) { rowOf[id] = i; }); });

  // ---------------------------------------------------------------- DOM
  var rows = [];
  D.rows.forEach(function (ids, i) {
    var row = document.createElement("div");
    row.className = "lrow";
    ids.forEach(function (id) {
      var L = byId[id];
      var b = document.createElement("button");
      b.type = "button";
      b.className = "layer layer-" + id;
      b.dataset.id = id;
      b.setAttribute("aria-expanded", "false");
      b.innerHTML = '<span class="lname">' + L.title + '</span><span class="lrole">' + L.role + "</span>";
      b.addEventListener("click", function () { toggle(id); });
      row.appendChild(b);
    });
    root.appendChild(row);
    rows.push(row);
  });
  var svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
  svg.setAttribute("class", "larrows");
  svg.setAttribute("aria-hidden", "true");
  svg.innerHTML =
    '<defs>' +
    '<marker id="la-primary" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z"/></marker>' +
    '<marker id="la-secondary" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z"/></marker>' +
    '<marker id="la-dim" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z"/></marker>' +
    "</defs>";
  root.appendChild(svg);
  var gEdges = document.createElementNS("http://www.w3.org/2000/svg", "g");
  svg.appendChild(gEdges);

  function block(id) { return root.querySelector('.layer[data-id="' + id + '"]'); }

  // ---------------------------------------------------------------- arrows
  function rect(el) {
    var r = el.getBoundingClientRect(), b = root.getBoundingClientRect();
    return { left: r.left - b.left, right: r.right - b.left, top: r.top - b.top, bottom: r.bottom - b.top,
             cx: (r.left + r.right) / 2 - b.left, cy: (r.top + r.bottom) / 2 - b.top, w: r.width, h: r.height };
  }
  function clamp(v, lo, hi) { return Math.max(lo, Math.min(hi, v)); }
  function el(name, attrs, text) {
    var e = document.createElementNS("http://www.w3.org/2000/svg", name);
    for (var k in attrs) e.setAttribute(k, attrs[k]);
    if (text != null) e.textContent = text;
    return e;
  }

  function draw() {
    var W = root.scrollWidth, H = root.scrollHeight;
    svg.setAttribute("width", W); svg.setAttribute("height", H);
    svg.setAttribute("viewBox", "0 0 " + W + " " + H);
    while (gEdges.firstChild) gEdges.removeChild(gEdges.firstChild);
    if (window.matchMedia && window.matchMedia("(max-width: 760px)").matches) return;
    var pad = 24, R = 14;
    D.edges.forEach(function (e) {
      var a = rect(block(e.from)), b = rect(block(e.to));
      var ra = rowOf[e.from], rb = rowOf[e.to];
      var d, lx, ly, anchor = "start", lab = e.label;
      if (ra === rb) {                                   // same row: horizontal
        var y = a.cy;
        d = "M" + (a.right + 1) + "," + y + " L" + (b.left - 1) + "," + y;
        lx = (a.right + b.left) / 2; ly = y - 9; anchor = "middle";
      } else if (!e.side) {                              // down to the next row(s): S-curve
        var sx = clamp(b.cx, a.left + pad, a.right - pad);
        var ex = clamp(a.cx, b.left + pad, b.right - pad);
        var my = (a.bottom + b.top) / 2;
        d = "M" + sx + "," + (a.bottom + 1) + " C" + sx + "," + my + " " + ex + "," + my + " " + ex + "," + (b.top - 1);
        lx = Math.max(sx, ex) + 10; ly = my + 4;
        if (Math.abs(sx - ex) > 60 && sx > ex) { lx = Math.min(sx, ex) - 10; anchor = "end"; }
      } else {                                           // around the side, skipping rows
        var left = e.side === "left", lane = 30 + (e.lane || 0) * 32;
        var x0 = left ? Math.min(a.left, b.left) - lane : Math.max(a.right, b.right) + lane;
        var fx = left ? a.left - 1 : a.right + 1, tx = left ? b.left - 1 : b.right + 1;
        var fy = a.cy + (e.lane || 0) * 10, ty = b.cy - (e.lane || 0) * 10;
        var s = left ? -1 : 1;                           // direction towards the lane
        d = "M" + fx + "," + fy +
            " L" + (x0 - s * R) + "," + fy + " Q" + x0 + "," + fy + " " + x0 + "," + (fy + R) +
            " L" + x0 + "," + (ty - R) + " Q" + x0 + "," + ty + " " + (x0 - s * R) + "," + ty +
            " L" + tx + "," + ty;
        lx = x0 + s * 9; ly = (fy + ty) / 2 + 4; anchor = left ? "end" : "start";
      }
      var p = el("path", { d: d, "class": "ledge ledge-" + e.kind, "marker-end": "url(#la-" + e.kind + ")" });
      gEdges.appendChild(p);
      if (lab) {
        var t = el("text", { x: lx, y: ly, "text-anchor": anchor, "class": "llabel" + (e.mono ? " llabel-mono" : "") }, lab);
        gEdges.appendChild(t);
      }
    });
  }
  // redraw continuously while the layout is animating
  var animUntil = 0, animating = false;
  function animate(ms) {
    animUntil = Math.max(animUntil, performance.now() + (ms || 700));
    if (animating) return;
    animating = true;
    (function step() {
      draw();
      if (performance.now() < animUntil) requestAnimationFrame(step); else animating = false;
    })();
  }
  window.addEventListener("resize", function () { animate(50); });
  if (window.ResizeObserver) new ResizeObserver(function () { animate(50); }).observe(root);

  // ---------------------------------------------------------------- detail panel
  var openId = null, panel = null;
  function esc(s) { return String(s).replace(/[&<>"]/g, function (c) { return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]; }); }
  function viewHref(id) { return "./navigator.html#/" + encodeURIComponent(byId[id].view).replace(/%2F/g, "/"); }
  function ghHref(fsPath, line) {
    return D.repo + "/" + D.root + "/" + fsPath + (line ? "#L" + line : "");
  }
  function ghTree(fsPath) { return D.repo.replace("/blob/", "/tree/") + "/" + D.root + "/" + fsPath; }
  function via(from, to) {
    for (var i = 0; i < D.edges.length; i++) {
      var e = D.edges[i];
      if (e.from === from && e.to === to) return e.theorem || (e.mono ? e.label : null);
    }
    return null;
  }
  function chips(list, dir) {
    if (!list.length) return "<em>nothing in this tree</em>";
    return list.map(function (i) {
      var other = dir === "up" ? i.from : i.to;
      var v = dir === "up" ? via(i.from, i.to) : via(i.from, i.to);
      return '<button type="button" class="lchip" data-id="' + other + '">' + esc(byId[other].title) +
        '<span class="lchip-n">' + i.files + (i.files === 1 ? " file" : " files") + "</span>" +
        (v ? '<span class="lchip-via">' + esc(v) + "</span>" : "") + "</button>";
    }).join("");
  }
  function render(id) {
    var L = byId[id];
    var up = D.imports.filter(function (i) { return i.to === id; });
    var down = D.imports.filter(function (i) { return i.from === id; });
    var h = '<div class="ldetail-inner"><div class="ldetail-grid"><div class="ldetail-text">';
    h += "<h3>" + esc(L.title) + ' <span class="lrole">' + esc(L.role) + "</span></h3>";
    h += '<p class="lmeta">' + L.files + " files · " + L.decls + " declarations · " +
         '<a href="' + viewHref(id) + '">open in the map</a> · <a href="' + ghTree(L.fsPath) + '">folder on GitHub</a></p>';
    h += L.summary;
    h += '<div class="ldeps"><div><span class="ldeps-k">Rests on</span>' + chips(up, "up") + "</div>" +
         '<div><span class="ldeps-k">Feeds</span>' + chips(down, "down") + "</div></div>";
    h += '</div><div class="ldetail-code">';
    L.snippets.forEach(function (s) {
      h += '<p class="lsnip-head"><code>' + esc(s.name) + "</code> · " +
           '<a href="' + ghHref(s.file, s.line) + '">' + esc(s.file.replace(/^Implementation\//, "")) + ":" + s.line + "</a></p>";
      h += '<pre class="lsnip"><code>' + esc(s.code) + "</code></pre>";
      if (s.note) h += '<p class="lsnip-note">' + s.note + "</p>";
    });
    h += "</div></div></div>";
    return h;
  }
  function closePanel(immediate) {
    if (!panel) return;
    var p = panel; panel = null;
    if (openId) { var b = block(openId); b.classList.remove("open"); b.setAttribute("aria-expanded", "false"); }
    openId = null;
    if (immediate) { p.remove(); return; }
    p.classList.remove("open");
    p.addEventListener("transitionend", function onEnd() { p.removeEventListener("transitionend", onEnd); p.remove(); });
    setTimeout(function () { if (p.parentNode) p.remove(); }, 900);
  }
  function open(id, instant) {
    var b = block(id);
    openId = id;
    b.classList.add("open"); b.setAttribute("aria-expanded", "true");
    panel = document.createElement("div");
    panel.className = "ldetail";
    panel.innerHTML = render(id);
    rows[rowOf[id]].insertAdjacentElement("afterend", panel);
    var br = rect(b), pr = rect(panel);
    panel.style.setProperty("--caret-x", (br.cx - pr.left) + "px");
    panel.querySelectorAll(".lchip").forEach(function (c) {
      c.addEventListener("click", function () { toggle(c.dataset.id, true); });
    });
    if (instant) { panel.classList.add("open", "instant"); }
    else { void panel.offsetHeight; panel.classList.add("open"); }
  }
  function toggle(id, force) {
    var reopen = openId !== id || force;
    var was = openId;
    closePanel(false);
    if (was === id && !force) { setHash(null); animate(800); return; }
    if (reopen) { open(id, false); setHash(id); animate(900); }
    if (force) {
      var b = block(id);
      setTimeout(function () { if (b.scrollIntoView) b.scrollIntoView({ behavior: "smooth", block: "nearest" }); }, 50);
    }
  }
  function setHash(id) {
    if (!window.history || !history.replaceState) return;
    var base = location.pathname + location.search;
    history.replaceState(null, "", id ? base + "#layer-" + id : base);
  }

  // ---------------------------------------------------------------- init
  var m = /^#layer-([A-Za-z]+)$/.exec(location.hash || "");
  if (m && byId[m[1]]) {
    open(m[1], true);
    setTimeout(function () { var b0 = block(m[1]); if (b0.scrollIntoView) b0.scrollIntoView({ block: "center" }); }, 0);
  }
  draw();
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(function () { draw(); });
  window.addEventListener("load", draw);
})();
