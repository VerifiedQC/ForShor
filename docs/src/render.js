// SVG drawing: nodes, ghosts, import/bridge edges, pan/zoom/drag, focus dimming.
// Stateless with respect to app logic — GraphView owns only view-independent
// UI mechanics (current transform, in-flight drag/pan) and calls back into
// app.js for everything that changes application state.
function createGraphView(svg, stage, handlers) {
  const ns = "http://www.w3.org/2000/svg";
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

  function cubicPoint(p0, p1, p2, p3, t) {
    const mt = 1 - t;
    return {
      x: mt ** 3 * p0.x + 3 * mt ** 2 * t * p1.x + 3 * mt * t ** 2 * p2.x + t ** 3 * p3.x,
      y: mt ** 3 * p0.y + 3 * mt ** 2 * t * p1.y + 3 * mt * t ** 2 * p2.y + t ** 3 * p3.y,
    };
  }

  function edgeRoute(a, b, lane, vertical) {
    if (vertical) {
      const x1 = a.x + a.w / 2, y1 = a.y + a.h;
      const x2 = b.x + b.w / 2, y2 = b.y;
      const dy = Math.max(70, Math.abs(y2 - y1) * 0.42);
      const p0 = { x: x1, y: y1 }, p1 = { x: x1 + lane, y: y1 + dy };
      const p2 = { x: x2 + lane, y: y2 - dy }, p3 = { x: x2, y: y2 };
      return { d: `M ${p0.x} ${p0.y} C ${p1.x} ${p1.y}, ${p2.x} ${p2.y}, ${p3.x} ${p3.y}`, label: cubicPoint(p0, p1, p2, p3, 0.5) };
    }
    const x1 = a.x + a.w, y1 = a.y + a.h / 2;
    const x2 = b.x, y2 = b.y + b.h / 2;
    const dx = Math.max(80, Math.abs(x2 - x1) * 0.46);
    const p0 = { x: x1, y: y1 }, p1 = { x: x1 + dx, y: y1 + lane };
    const p2 = { x: x2 - dx, y: y2 + lane }, p3 = { x: x2, y: y2 };
    return { d: `M ${p0.x} ${p0.y} C ${p1.x} ${p1.y}, ${p2.x} ${p2.y}, ${p3.x} ${p3.y}`, label: cubicPoint(p0, p1, p2, p3, 0.5) };
  }

  function ghostRoute(node, ghost, vertical) {
    if (vertical) {
      if (ghost.side === "top") {
        const x = ghost.x + ghost.w / 2, y1 = ghost.y + ghost.h, y2 = node.y;
        return { d: `M ${x} ${y1} L ${x} ${y2}` };
      }
      const x = ghost.x + ghost.w / 2, y1 = node.y + node.h, y2 = ghost.y;
      return { d: `M ${x} ${y1} L ${x} ${y2}` };
    }
    if (ghost.side === "left") {
      const y = ghost.y + ghost.h / 2;
      return { d: `M ${ghost.x + ghost.w} ${y} L ${node.x} ${node.y + node.h / 2}` };
    }
    const y = ghost.y + ghost.h / 2;
    return { d: `M ${node.x + node.w} ${node.y + node.h / 2} L ${ghost.x} ${y}` };
  }

  function nearestNode(positions, ghost, vertical) {
    // Ghosts route to the geometric center of the current view's nodes,
    // which reads fine since ghosts summarize a whole external subtree
    // rather than a single sibling.
    let best = null, bestDist = Infinity;
    for (const [id, p] of positions.entries()) {
      const cx = p.x + p.w / 2, cy = p.y + p.h / 2;
      const gx = ghost.x + ghost.w / 2, gy = ghost.y + ghost.h / 2;
      const d = vertical ? Math.abs(cx - gx) : Math.abs(cy - gy);
      if (d < bestDist) { bestDist = d; best = { id, p }; }
    }
    return best;
  }

  function classesFor(kind, extra) {
    return [kind, ...(extra || [])].filter(Boolean).join(" ");
  }

  function render(vm) {
    const rect = viewportRect();
    svg.innerHTML = "";
    const defs = make("defs", {}, svg);
    const marker = make("marker", { id: "arrow", markerWidth: 10, markerHeight: 10, refX: 9, refY: 3, orient: "auto", markerUnits: "strokeWidth" }, defs);
    make("path", { d: "M 0 0 L 9 3 L 0 6 z", fill: "#8b98aa" }, marker);
    const bmarker = make("marker", { id: "arrow-bridge", markerWidth: 10, markerHeight: 10, refX: 9, refY: 3, orient: "auto", markerUnits: "strokeWidth" }, defs);
    make("path", { d: "M 0 0 L 9 3 L 0 6 z", fill: "currentColor" }, bmarker);

    scene = make("g", { class: "scene" }, svg);
    currentPositions = vm.positions;

    const selType = vm.selection && vm.selection.type;
    const selId = selType === "node" ? vm.selection.id : null;
    const selEdgeKey = selType === "edge" ? vm.selection.key : null;
    const selGhostKey = selType === "ghost" ? vm.selection.key : null;
    const matches = vm.matches;

    const neighborIds = new Set();
    if (selId) {
      neighborIds.add(selId);
      vm.edges.forEach((e) => { if (e.from === selId) neighborIds.add(e.to); if (e.to === selId) neighborIds.add(e.from); });
    }

    // --- import + bridge edges ---
    const edgesLayer = make("g", { class: "edges" }, scene);
    const labelsLayer = make("g", { class: "edge-labels" }, scene);
    vm.edges.forEach((e, idx) => {
      const a = vm.positions.get(e.from), b = vm.positions.get(e.to);
      if (!a || !b) return;
      const key = Model.edgeKey(e.from, e.to);
      const isSelected = selEdgeKey === key;
      const isNeighbor = selId && (e.from === selId || e.to === selId);
      const dim = vm.focusMode && ((selEdgeKey && !isSelected) || (selId && !isNeighbor)) ||
        (matches && !(matches.has(e.from) || matches.has(e.to)));

      if (vm.showImports) {
        const lane = (idx % 5 - 2) * 26;
        const route = edgeRoute(a, b, lane, vm.vertical);
        const width = Math.min(6, 1.4 + Math.log2(e.weight + 1));
        const path = make("path", { class: classesFor("edge", [isSelected && "selected", isNeighbor && !isSelected && "neighbor", dim && "dimmed"]), d: route.d, "stroke-width": width }, edgesLayer);
        const hit = make("path", { class: "edge-hit", d: route.d }, edgesLayer);
        [path, hit].forEach((el) => el.addEventListener("click", (ev) => { ev.stopPropagation(); handlers.onSelectEdge(e); }));
      }

      if (vm.showBridges && e.bridges && e.bridges.length) {
        e.bridges.forEach((bridge, bi) => {
          const lane = 40 + bi * 34;
          const route = edgeRoute(a, b, lane, vm.vertical);
          const role = Model.role(e.from);
          const path = make("path", {
            class: classesFor("bridge-edge", [isSelected && "selected", dim && "dimmed"]),
            d: route.d, "data-role": role, "marker-end": "url(#arrow-bridge)",
          }, edgesLayer);
          path.addEventListener("click", (ev) => { ev.stopPropagation(); handlers.onSelectEdge(e, bridge); });

          const text = bridge.label || bridge.theorem || "";
          const lg = make("g", { class: classesFor("edge-label-group bridge-label", [dim && "dimmed"]), tabindex: "0", role: "button" }, labelsLayer);
          lg.addEventListener("click", (ev) => { ev.stopPropagation(); handlers.onSelectEdge(e, bridge); });
          const w = Math.min(180, Math.max(70, text.length * 6.2 + 18));
          make("rect", { class: "edge-label-bg bridge-label-bg", x: route.label.x - w / 2, y: route.label.y - 13, width: w, height: 26, rx: 6 }, lg);
          const t = make("text", { class: "edge-label bridge-label-text", x: route.label.x, y: route.label.y + 4, "text-anchor": "middle" }, lg);
          t.textContent = text;
        });
      }
    });

    // --- ghost ports ---
    const ghostLayer = make("g", { class: "ghosts" }, scene);
    for (const [key, g] of vm.ghostPositions.entries()) {
      if (!vm.showGhosts) break;
      const near = nearestNode(vm.positions, g, vm.vertical);
      if (near) {
        const route = ghostRoute(near.p, g, vm.vertical);
        make("path", { class: "ghost-edge", d: route.d }, ghostLayer);
      }
      const isSelected = selGhostKey === key;
      const group = make("g", {
        class: classesFor("ghost", [isSelected && "selected"]),
        transform: `translate(${g.x} ${g.y})`, tabindex: "0", role: "button",
      }, ghostLayer);
      make("rect", { class: "ghost-card", width: g.w, height: g.h, rx: 8 }, group);
      const label1 = make("text", { class: "ghost-label", x: 12, y: 24 }, group);
      label1.textContent = Model.label(g.target);
      const label2 = make("text", { class: "ghost-weight", x: 12, y: 42 }, group);
      label2.textContent = `${g.weight} import${g.weight === 1 ? "" : "s"}`;
      group.addEventListener("click", (ev) => { ev.stopPropagation(); handlers.onSelectGhost(g); });
      group.addEventListener("dblclick", (ev) => { ev.stopPropagation(); handlers.onOpenGhost(g); });
    }

    // --- nodes ---
    const nodesLayer = make("g", { class: "nodes" }, scene);
    vm.children.forEach((id) => {
      const p = vm.positions.get(id);
      if (!p) return;
      const n = Model.node(id);
      const isFolder = n.kind === "folder";
      const role = Model.role(id);
      const layer = Model.layer(id);
      const dim = (matches && !matches.has(id)) || (vm.focusMode && selId && selId !== id && !neighborIds.has(id)) ||
        (vm.focusMode && selEdgeKey && !vm.edges.some((e) => Model.edgeKey(e.from, e.to) === selEdgeKey && (e.from === id || e.to === id)));
      const group = make("g", {
        class: classesFor("node", [isFolder && "node-folder", !isFolder && "node-file", id === selId && "selected", dim && "dimmed", role === "support" && "role-support"]),
        "data-role": role, "data-layer": layer || "",
        transform: `translate(${p.x} ${p.y})`, tabindex: "0", role: "button", "aria-label": Model.label(id),
      }, nodesLayer);
      make("rect", { class: "node-card", width: p.w, height: p.h, rx: 9 }, group);
      make("rect", { class: "node-accent", width: 6, height: p.h, rx: 3 }, group);
      const kicker = make("text", { class: "node-kind", x: 16, y: 18 }, group);
      kicker.textContent = isFolder ? (layer ? (ANN.layers[layer] || {}).label || layer : "folder") : "file";
      makeWrappedText(make, group, Model.label(id), 16, 42, 15.5, "node-title", 23, 2);
      const sub = Model.subtitle(id) || (isFolder ? `${n.fileCount} file${n.fileCount === 1 ? "" : "s"}` : `${n.lines} lines`);
      makeWrappedText(make, group, sub, 16, p.h - 16, 12, "node-subtitle", 30, 1);
      if (isFolder) {
        const chevron = make("text", { class: "node-open-hint", x: p.w - 22, y: 22 }, group);
        chevron.textContent = "→";
      }

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

  function fit(vm) {
    const rect = viewportRect();
    const all = [...vm.positions.values(), ...(vm.showGhosts ? [...vm.ghostPositions.values()] : [])];
    if (!all.length) { transform = { x: 0, y: 0, scale: 1 }; applyTransform(); return; }
    const minX = Math.min(...all.map((p) => p.x));
    const maxX = Math.max(...all.map((p) => p.x + p.w));
    const minY = Math.min(...all.map((p) => p.y));
    const maxY = Math.max(...all.map((p) => p.y + p.h));
    const w = maxX - minX || 1, h = maxY - minY || 1;
    const scale = Math.max(0.32, Math.min(1.05, (rect.width - 64) / w, (rect.height - 64) / h));
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

  const ANN = window.ANNOTATIONS && window.ANNOTATIONS.layers ? window.ANNOTATIONS : { layers: {} };

  return {
    render,
    fit,
    setScale,
    getTransform: () => transform,
    resetTransform: () => { transform = { x: 0, y: 0, scale: 1 }; applyTransform(); },
  };
}
