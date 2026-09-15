// SVG drawing: nodes, curated/reduced edges (one arrow per pair, styled by
// emphasis), pan/zoom/drag, focus dimming. Stateless with respect to app
// logic — GraphView owns only view-independent UI mechanics (current
// transform, in-flight drag/pan) and calls back into app.js for everything
// that changes application state.
function createGraphView(svg, stage, handlers) {
  const ns = "http://www.w3.org/2000/svg";
  const ANN = window.ANNOTATIONS || { roles: {}, layers: {} };
  let scene = null;
  let transform = { x: 0, y: 0, scale: 1 };
  let dragging = null;
  let panning = null;
  let didDrag = false;
  let currentPositions = new Map();
  let pendingClick = null;

  function make(tag, attrs, parent) {
    const el = document.createElementNS(ns, tag);
    for (const [k, v] of Object.entries(attrs || {})) el.setAttribute(k, v);
    if (parent) parent.appendChild(el);
    return el;
  }

  function viewportRect() {
    return svg.getBoundingClientRect();
  }

  function applyTransform() {
    if (scene) scene.setAttribute("transform", `translate(${transform.x} ${transform.y}) scale(${transform.scale})`);
    handlers.onTransform && handlers.onTransform(transform);
  }

  function setScale(nextScale, center) {
    const rect = viewportRect();
    const old = transform.scale;
    const scale = Math.min(2.2, Math.max(0.28, nextScale));
    const cx = center ? center.x : rect.width / 2;
    const cy = center ? center.y : rect.height / 2;
    transform.x = cx - (cx - transform.x) * (scale / old);
    transform.y = cy - (cy - transform.y) * (scale / old);
    transform.scale = scale;
    applyTransform();
  }

  function colorFor(path) {
    const layer = Model.layer(path);
    if (layer && ANN.layers[layer]) return ANN.layers[layer].color;
    const role = Model.role(path);
    return (ANN.roles[role] || {}).color || "#7c899c";
  }

  function cubicPoint(p0, p1, p2, p3, t) {
    const mt = 1 - t;
    return {
      x: mt ** 3 * p0.x + 3 * mt ** 2 * t * p1.x + 3 * mt * t ** 2 * p2.x + t ** 3 * p3.x,
      y: mt ** 3 * p0.y + 3 * mt ** 2 * t * p1.y + 3 * mt * t ** 2 * p2.y + t ** 3 * p3.y,
    };
  }

  // Evenly spread each node's outgoing edges along its right edge (sorted by
  // target row) and incoming edges along its left edge (sorted by source
  // row), inset 14px from top/bottom, so no two arrows share a start/end
  // point. An edge whose endpoints share a column (e.g. two nodes a curated
  // `columns` override stacks vertically, like Framework/Shared) instead
  // gets a vertical port — top-to-bottom, not a left/right loop-back.
  // Returns edgeKey -> {sx,sy,ex,ey,vertical}.
  function assignPorts(children, positions, edges, columnOf) {
    const sameColumn = new Set(edges.filter((e) => columnOf.get(e.from) === columnOf.get(e.to)).map((e) => Model.edgeKey(e.from, e.to)));
    const horizontalEdges = edges.filter((e) => !sameColumn.has(Model.edgeKey(e.from, e.to)));

    const outOf = new Map(), inOf = new Map();
    horizontalEdges.forEach((e) => {
      if (!outOf.has(e.from)) outOf.set(e.from, []);
      outOf.get(e.from).push(e);
      if (!inOf.has(e.to)) inOf.set(e.to, []);
      inOf.get(e.to).push(e);
    });
    const ports = new Map();
    const inset = 14;

    function place(nodeId, list, isOut) {
      const p = positions.get(nodeId);
      if (!p || !list.length) return;
      const sorted = [...list].sort((a, b) => {
        const ap = positions.get(isOut ? a.to : a.from);
        const bp = positions.get(isOut ? b.to : b.from);
        return (ap ? ap.y : 0) - (bp ? bp.y : 0);
      });
      const usable = Math.max(0, p.h - inset * 2);
      sorted.forEach((e, i) => {
        const t = sorted.length === 1 ? 0.5 : i / (sorted.length - 1);
        const y = p.y + inset + t * usable;
        const x = isOut ? p.x + p.w : p.x;
        const key = Model.edgeKey(e.from, e.to);
        const port = ports.get(key) || {};
        if (isOut) { port.sx = x; port.sy = y; } else { port.ex = x; port.ey = y; }
        ports.set(key, port);
      });
    }

    children.forEach((id) => {
      place(id, outOf.get(id) || [], true);
      place(id, inOf.get(id) || [], false);
    });

    edges.forEach((e) => {
      const key = Model.edgeKey(e.from, e.to);
      if (!sameColumn.has(key)) return;
      const a = positions.get(e.from), b = positions.get(e.to); // a = from, b = to
      if (!a || !b) return;
      const sx = a.x + a.w / 2, ex = b.x + b.w / 2;
      const fromAbove = a.y <= b.y;
      ports.set(key, {
        sx, sy: fromAbove ? a.y + a.h : a.y,
        ex, ey: fromAbove ? b.y : b.y + b.h,
        vertical: true,
      });
    });

    return ports;
  }

  // A single cubic bezier with horizontal tangents at both ends for edges
  // within one column of each other; a two-segment smooth path routed
  // through a channel above/below the intermediate columns for longer
  // spans, so a long arrow reads as one clean curve rather than cutting
  // through unrelated nodes.
  function buildRoute(port, colFrom, colTo, columns, positions, band) {
    const { sx, sy, ex, ey } = port;
    if (port.vertical) {
      const gap = Math.max(20, (ey - sy) * 0.5);
      const p0 = { x: sx, y: sy }, p1 = { x: sx, y: sy + gap };
      const p2 = { x: ex, y: ey - gap }, p3 = { x: ex, y: ey };
      return {
        d: `M ${p0.x} ${p0.y} C ${p1.x} ${p1.y}, ${p2.x} ${p2.y}, ${p3.x} ${p3.y}`,
        pointAt: (t) => cubicPoint(p0, p1, p2, p3, t),
      };
    }
    const span = Math.abs(colTo - colFrom);
    if (span <= 1) {
      const gap = Math.max(40, (ex - sx) * 0.5);
      const p0 = { x: sx, y: sy }, p1 = { x: sx + gap, y: sy };
      const p2 = { x: ex - gap, y: ey }, p3 = { x: ex, y: ey };
      return {
        d: `M ${p0.x} ${p0.y} C ${p1.x} ${p1.y}, ${p2.x} ${p2.y}, ${p3.x} ${p3.y}`,
        pointAt: (t) => cubicPoint(p0, p1, p2, p3, t),
      };
    }

    const lo = Math.min(colFrom, colTo), hi = Math.max(colFrom, colTo);
    let minY = Infinity, maxY = -Infinity, xEnter = null, xExit = null;
    for (let c = lo + 1; c < hi; c++) {
      (columns[c] || []).forEach((id) => {
        const p = positions.get(id);
        if (!p) return;
        minY = Math.min(minY, p.y);
        maxY = Math.max(maxY, p.y + p.h);
        xEnter = xEnter === null ? p.x : Math.min(xEnter, p.x);
        xExit = xExit === null ? p.x + p.w : Math.max(xExit, p.x + p.w);
      });
    }
    const above = ey <= sy;
    // Each successive edge sharing a direction (above/below) gets pushed
    // further out from the row, so several long arrows fan into a stack of
    // parallel arcs instead of bundling on top of each other and cutting
    // back through the very nodes they're routed around.
    const clearance = 44 + (band || 0) * 46;
    const channelY = minY === Infinity
      ? (above ? Math.min(sy, ey) - 70 - (band || 0) * 46 : Math.max(sy, ey) + 70 + (band || 0) * 46)
      : (above ? minY - clearance : maxY + clearance);

    // Rise from the source to channel height *before* reaching the first
    // intermediate column (not partway through it — a rise proportional to
    // the total span, as a naive midpoint curve would give, stays at row
    // height for hundreds of pixels on a wide span and cuts straight
    // through whatever sits in the middle), travel flat across the whole
    // intermediate stretch, then descend into the target the same way.
    const riseX = xEnter === null ? (sx + ex) / 2 - 40 : Math.min(xEnter - 24, (sx + ex) / 2);
    const fallX = xExit === null ? (sx + ex) / 2 + 40 : Math.max(xExit + 24, (sx + ex) / 2);
    const tangent = 44;
    const p0 = { x: sx, y: sy };
    const p1 = { x: Math.min(sx + tangent, riseX), y: sy };
    const p2 = { x: Math.max(riseX - tangent, sx), y: channelY };
    const a = { x: riseX, y: channelY };
    const b = { x: fallX, y: channelY };
    const p3 = { x: Math.min(fallX + tangent, ex), y: channelY };
    const p4 = { x: Math.max(ex - tangent, fallX), y: ey };
    const p5 = { x: ex, y: ey };
    return {
      d: `M ${p0.x} ${p0.y} C ${p1.x} ${p1.y}, ${p2.x} ${p2.y}, ${a.x} ${a.y} `
        + `L ${b.x} ${b.y} `
        + `C ${p3.x} ${p3.y}, ${p4.x} ${p4.y}, ${p5.x} ${p5.y}`,
      pointAt: (t) => {
        if (t < 1 / 3) return cubicPoint(p0, p1, p2, a, t * 3);
        if (t < 2 / 3) { const lt = (t - 1 / 3) * 3; return { x: a.x + (b.x - a.x) * lt, y: a.y + (b.y - a.y) * lt }; }
        return cubicPoint(b, p3, p4, p5, (t - 2 / 3) * 3);
      },
    };
  }

  function rectsOverlap(a, b, pad) {
    return a.x < b.x + b.w + pad && a.x + a.w > b.x - pad && a.y < b.y + b.h + pad && a.y + a.h > b.y - pad;
  }

  function findLabelSpot(route, positions, placedLabels, w, h) {
    const candidates = [0.6, 0.55, 0.65, 0.5, 0.7, 0.45, 0.75, 0.4, 0.8, 0.35, 0.85, 0.3, 0.9, 0.25, 0.95, 0.2];
    const nodeRects = [...positions.values()];
    const clear = (rect) => !nodeRects.some((n) => rectsOverlap(rect, n, 6)) && !placedLabels.some((n) => rectsOverlap(rect, n, 3));

    for (const t of candidates) {
      const pt = route.pointAt(t);
      const rect = { x: pt.x - w / 2, y: pt.y - h / 2, w, h };
      if (clear(rect)) { placedLabels.push(rect); return pt; }
    }

    // A label this wide can't avoid a neighbour by sliding along a short
    // curve alone (e.g. a label between two adjacent columns, where the
    // whole visible curve sits inside the ~80px gap between their edges).
    // Nudge it perpendicular to the row instead, growing outward until
    // it clears — same idea as the channel routing above/below.
    const base = route.pointAt(0.5);
    for (let dy = 16; dy <= 160; dy += 16) {
      for (const sign of [-1, 1]) {
        const pt = { x: base.x, y: base.y + sign * dy };
        const rect = { x: pt.x - w / 2, y: pt.y - h / 2, w, h };
        if (clear(rect)) { placedLabels.push(rect); return pt; }
      }
    }

    const pt = route.pointAt(0.6);
    placedLabels.push({ x: pt.x - w / 2, y: pt.y - h / 2, w, h });
    return pt;
  }

  function classesFor(kind, extra) {
    return [kind, ...(extra || [])].filter(Boolean).join(" ");
  }

  function makeWrappedText(makeFn, parent, text, x, y, size, className, lineLimit, maxLines) {
    const words = String(text || "").split(/\s+/);
    const lines = [];
    let current = "";
    words.forEach((word) => {
      if (current && (current + " " + word).trim().length > lineLimit) {
        lines.push(current.trim());
        current = word;
      } else {
        current = `${current} ${word}`.trim();
      }
    });
    if (current) lines.push(current);
    lines.slice(0, maxLines).forEach((line, i) => {
      const el = makeFn("text", { x, y: y + i * (size + 3), "font-size": size, class: className }, parent);
      el.textContent = line + (maxLines && lines.length > maxLines && i === maxLines - 1 ? "…" : "");
    });
  }

  function render(vm) {
    svg.innerHTML = "";
    const defs = make("defs", {}, svg);
    ["framework", "subroutine", "assembly", "resource", "submission", "support"].forEach((role) => {
      const color = (ANN.roles[role] || {}).color || "#7c899c";
      const m = make("marker", { id: `arrow-${role}`, markerWidth: 9, markerHeight: 9, refX: 8, refY: 2.5, orient: "auto", markerUnits: "strokeWidth" }, defs);
      make("path", { d: "M 0 0 L 8 2.5 L 0 5 z", fill: color }, m);
    });
    ["math", "definitions", "lowering", "spec", "proofs", "main"].forEach((layer) => {
      const color = (ANN.layers[layer] || {}).color || "#7c899c";
      const m = make("marker", { id: `arrow-layer-${layer}`, markerWidth: 9, markerHeight: 9, refX: 8, refY: 2.5, orient: "auto", markerUnits: "strokeWidth" }, defs);
      make("path", { d: "M 0 0 L 8 2.5 L 0 5 z", fill: color }, m);
    });
    const secMarker = make("marker", { id: "arrow-secondary", markerWidth: 8, markerHeight: 8, refX: 7, refY: 2.2, orient: "auto", markerUnits: "strokeWidth" }, defs);
    make("path", { d: "M 0 0 L 7 2.2 L 0 4.4 z", fill: "#9aa7bc" }, secMarker);
    const dimMarker = make("marker", { id: "arrow-dim", markerWidth: 8, markerHeight: 8, refX: 7, refY: 2.2, orient: "auto", markerUnits: "strokeWidth" }, defs);
    make("path", { d: "M 0 0 L 7 2.2 L 0 4.4 z", fill: "#c3cad6" }, dimMarker);

    scene = make("g", { class: "scene" }, svg);
    currentPositions = vm.positions;

    const selType = vm.selection && vm.selection.type;
    const selId = selType === "node" ? vm.selection.id : null;
    const selEdgeKey = selType === "edge" ? vm.selection.key : null;
    const externalHighlight = vm.highlightExternal || null;

    const neighborIds = new Set();
    if (selId) {
      neighborIds.add(selId);
      vm.edges.forEach((e) => { if (e.from === selId) neighborIds.add(e.to); if (e.to === selId) neighborIds.add(e.from); });
    }

    const ports = assignPorts(vm.children, vm.positions, vm.edges, vm.columnOf);

    // Long (span >= 2) edges going the same direction (above/below the row)
    // are stacked into their own band, farthest-reaching first, so they fan
    // into parallel arcs instead of bundling on top of each other.
    const bandOf = new Map();
    {
      const above = [], below = [];
      vm.edges.forEach((e) => {
        const cf = vm.columnOf.get(e.from) ?? 0, ct = vm.columnOf.get(e.to) ?? 0;
        if (Math.abs(ct - cf) < 2) return;
        const port = ports.get(Model.edgeKey(e.from, e.to));
        if (!port || port.vertical) return;
        (port.ey <= port.sy ? above : below).push({ key: Model.edgeKey(e.from, e.to), span: Math.abs(ct - cf) });
      });
      above.sort((a, b) => b.span - a.span).forEach((e, i) => bandOf.set(e.key, i));
      below.sort((a, b) => b.span - a.span).forEach((e, i) => bandOf.set(e.key, i));
    }

    const placedLabels = [];
    const edgesLayer = make("g", { class: "edges" }, scene);
    const labelsLayer = make("g", { class: "edge-labels" }, scene);
    vm.edges.forEach((e) => {
      const a = vm.positions.get(e.from), b = vm.positions.get(e.to);
      const port = ports.get(Model.edgeKey(e.from, e.to));
      if (!a || !b || !port) return;
      const key = Model.edgeKey(e.from, e.to);
      const isSelected = selEdgeKey === key;
      const isNeighbor = selId && (e.from === selId || e.to === selId);
      const dim = (vm.focusMode && ((selEdgeKey && !isSelected) || (selId && !isNeighbor))) ||
        (vm.matches && !(vm.matches.has(e.from) || vm.matches.has(e.to)));
      const emphasis = e.emphasis || "secondary";

      const colFrom = vm.columnOf.get(e.from) ?? 0;
      const colTo = vm.columnOf.get(e.to) ?? 0;
      const route = buildRoute(port, colFrom, colTo, vm.columns, vm.positions, bandOf.get(key) || 0);

      const layer = Model.layer(e.from);
      const markerId = emphasis === "primary"
        ? (layer && ANN.layers[layer] ? `arrow-layer-${layer}` : `arrow-${Model.role(e.from)}`)
        : `arrow-${emphasis === "secondary" ? "secondary" : "dim"}`;
      const strokeColor = emphasis === "primary" ? colorFor(e.from) : (emphasis === "secondary" ? "#9aa7bc" : "#d5dbe4");

      const path = make("path", {
        class: classesFor("edge", [`edge-${emphasis}`, isSelected && "selected", isNeighbor && !isSelected && "neighbor", dim && "dimmed"]),
        d: route.d,
        style: `--edge-color:${strokeColor}`,
        "marker-end": `url(#${markerId})`,
      }, edgesLayer);
      const hit = make("path", { class: "edge-hit", d: route.d }, edgesLayer);
      [path, hit].forEach((el) => el.addEventListener("click", (ev) => { ev.stopPropagation(); handlers.onSelectEdge(e); }));

      if (emphasis === "primary" && e.label) {
        const text = e.label.length > 32 ? e.label.slice(0, 31) + "…" : e.label;
        const w = Math.min(190, Math.max(64, text.length * 6.1 + 18));
        const h = 24;
        const pt = findLabelSpot(route, vm.positions, placedLabels, w, h);
        const lg = make("g", { class: classesFor("edge-label-group", [dim && "dimmed"]), tabindex: "0", role: "button" }, labelsLayer);
        lg.addEventListener("click", (ev) => { ev.stopPropagation(); handlers.onSelectEdge(e); });
        make("rect", { class: "edge-label-bg", x: pt.x - w / 2, y: pt.y - h / 2, width: w, height: h, rx: 6, style: `--edge-color:${strokeColor}` }, lg);
        const t = make("text", { class: "edge-label", x: pt.x, y: pt.y + 4, "text-anchor": "middle" }, lg);
        t.textContent = text;
      }
    });

    const nodesLayer = make("g", { class: "nodes" }, scene);
    vm.children.forEach((id) => {
      const p = vm.positions.get(id);
      if (!p) return;
      const n = Model.node(id);
      const isFolder = n.kind === "folder";
      const role = Model.role(id);
      const layer = Model.layer(id);
      const isSupport = role === "support";
      const externallyLit = externalHighlight && externalHighlight.has(id);
      const dim = (vm.matches && !vm.matches.has(id)) ||
        (vm.focusMode && selId && selId !== id && !neighborIds.has(id)) ||
        (vm.focusMode && selEdgeKey && !vm.edges.some((e) => Model.edgeKey(e.from, e.to) === selEdgeKey && (e.from === id || e.to === id))) ||
        (externalHighlight && !externallyLit);
      const group = make("g", {
        class: classesFor("node", [isFolder && "node-folder", !isFolder && "node-file", id === selId && "selected", dim && "dimmed", isSupport && "role-support", externallyLit && "lit"]),
        "data-role": role, "data-layer": layer || "",
        transform: `translate(${p.x} ${p.y})`, tabindex: "0", role: "button", "aria-label": Model.label(id),
      }, nodesLayer);
      make("rect", { class: "node-card", width: p.w, height: p.h, rx: 8 }, group);
      make("rect", { class: "node-accent", width: 5, height: p.h, rx: 2.5 }, group);
      if (isFolder) {
        const badge = make("text", { class: "node-badge", x: p.w - 14, y: 20, "text-anchor": "end" }, group);
        badge.textContent = `▸ ${n.children.length}`;
      } else {
        make("path", { class: "node-file-glyph", d: `M ${p.w - 26} 10 h 10 l 4 4 v 10 h -14 z M ${p.w - 16} 10 v 4 h 4` }, group);
      }
      makeWrappedText(make, group, Model.label(id), 16, 34, 16, "node-title", 22, 2);
      const sub = Model.subtitle(id) || (isFolder ? `${n.fileCount} file${n.fileCount === 1 ? "" : "s"}` : `${n.lines} lines`);
      makeWrappedText(make, group, sub, 16, p.h - 14, 12.5, "node-subtitle", 30, 1);

      group.addEventListener("pointerdown", (ev) => {
        ev.stopPropagation();
        didDrag = false;
        svg.classList.add("dragging");
        dragging = { id, startX: ev.clientX, startY: ev.clientY, origin: { x: p.x, y: p.y } };
        try { group.setPointerCapture(ev.pointerId); } catch (e) { /* synthetic/inactive pointer id */ }
      });
      group.addEventListener("pointerup", () => { if (dragging && dragging.id === id) { dragging = null; svg.classList.remove("dragging"); } });
      group.addEventListener("click", (ev) => {
        ev.stopPropagation();
        if (didDrag) return;
        if (pendingClick) clearTimeout(pendingClick);
        pendingClick = setTimeout(() => { handlers.onSelectNode(id); pendingClick = null; }, 190);
      });
      group.addEventListener("dblclick", (ev) => {
        ev.stopPropagation();
        if (pendingClick) { clearTimeout(pendingClick); pendingClick = null; }
        if (isFolder) handlers.onOpenNode(id);
      });
      group.addEventListener("keydown", (ev) => {
        if (ev.key === "Enter" || ev.key === " ") { ev.preventDefault(); handlers.onSelectNode(id); }
        if ((ev.key === "d" || ev.key === "D") && isFolder) handlers.onOpenNode(id);
      });
    });

    applyTransform();
  }

  function fit(vm) {
    const rect = viewportRect();
    const all = [...vm.positions.values()];
    if (!all.length) { transform = { x: 0, y: 0, scale: 1 }; applyTransform(); return; }
    const minX = Math.min(...all.map((p) => p.x));
    const maxX = Math.max(...all.map((p) => p.x + p.w));
    const minY = Math.min(...all.map((p) => p.y));
    const maxY = Math.max(...all.map((p) => p.y + p.h));
    const w = maxX - minX || 1, h = maxY - minY || 1;
    const scale = Math.max(0.32, Math.min(1.1, (rect.width - 64) / w, (rect.height - 64) / h));
    transform = {
      scale,
      x: (rect.width - w * scale) / 2 - minX * scale,
      y: (rect.height - h * scale) / 2 - minY * scale,
    };
    applyTransform();
  }

  svg.addEventListener("pointerdown", (ev) => {
    if (ev.target !== svg) return;
    svg.classList.add("panning");
    panning = { startX: ev.clientX, startY: ev.clientY, origin: { ...transform } };
    try { svg.setPointerCapture(ev.pointerId); } catch (e) { /* synthetic/inactive pointer id */ }
  });
  svg.addEventListener("pointermove", (ev) => {
    if (dragging) {
      didDrag = didDrag || Math.abs(ev.clientX - dragging.startX) + Math.abs(ev.clientY - dragging.startY) > 4;
      const p = currentPositions.get(dragging.id);
      if (p) {
        p.x = dragging.origin.x + (ev.clientX - dragging.startX) / transform.scale;
        p.y = dragging.origin.y + (ev.clientY - dragging.startY) / transform.scale;
        handlers.onRerenderNeeded && handlers.onRerenderNeeded();
      }
      return;
    }
    if (panning) {
      transform.x = panning.origin.x + ev.clientX - panning.startX;
      transform.y = panning.origin.y + ev.clientY - panning.startY;
      applyTransform();
    }
  });
  svg.addEventListener("pointerup", () => { dragging = null; panning = null; svg.classList.remove("dragging", "panning"); });
  svg.addEventListener("click", (ev) => { if (ev.target === svg) handlers.onBackgroundClick && handlers.onBackgroundClick(); });
  svg.addEventListener("wheel", (ev) => {
    ev.preventDefault();
    const rect = viewportRect();
    setScale(transform.scale + Math.sign(ev.deltaY) * -0.08, { x: ev.clientX - rect.left, y: ev.clientY - rect.top });
  }, { passive: false });

  return {
    render,
    fit,
    setScale,
    getTransform: () => transform,
    resetTransform: () => { transform = { x: 0, y: 0, scale: 1 }; applyTransform(); },
  };
}
