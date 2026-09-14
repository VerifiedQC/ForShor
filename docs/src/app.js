(() => {
  const state = {
    path: "",
    selection: null, // {type:"node",id} | {type:"edge",edge,bridge} | {type:"ghost",ghost,side}
    focusMode: true,
    showImports: true,
    showBridges: true,
    showGhosts: true,
    spineMode: false,
    query: "",
    expandedPaths: new Set(),
  };

  const els = {
    breadcrumb: document.getElementById("breadcrumb"),
    railTree: document.getElementById("railTree"),
    legend: document.getElementById("legend"),
    viewTitle: document.getElementById("viewTitle"),
    viewDescription: document.getElementById("viewDescription"),
    graphStats: document.getElementById("graphStats"),
    svg: document.getElementById("graph"),
    stage: document.querySelector(".graph-stage"),
    emptyState: document.getElementById("emptyState"),
    detailsContent: document.getElementById("detailsContent"),
    searchInput: document.getElementById("searchInput"),
    searchResults: document.getElementById("searchResults"),
    zoomIn: document.getElementById("zoomInButton"),
    zoomOut: document.getElementById("zoomOutButton"),
    fitBtn: document.getElementById("fitButton"),
    focusToggle: document.getElementById("focusToggleButton"),
    spineToggle: document.getElementById("spineToggleButton"),
    importsToggle: document.getElementById("importsToggleButton"),
    bridgesToggle: document.getElementById("bridgesToggleButton"),
    ghostsToggle: document.getElementById("ghostsToggleButton"),
    topBtn: document.getElementById("topButton"),
  };

  let lastLayout = null;

  const graphView = createGraphView(els.svg, els.stage, {
    onSelectNode: (id) => selectNode(id),
    onOpenNode: (id) => openPath(id),
    onOpenGhost: (g) => openPath(Model.parentOf(g.target) || g.target),
    onSelectEdge: (edge, bridge) => selectEdge(edge, bridge),
    onSelectGhost: (g) => selectGhost(g),
    onBackgroundClick: () => { state.selection = null; renderDetails(); renderGraphOnly(); },
    onRerenderNeeded: () => renderGraphOnly(),
    onTransform: () => {},
  });

  function ensureView(path) {
    return path === "" ? { path: "", children: Model.GRAPH.meta.order0, edges: Model.GRAPH.views[""].edges, ghosts: { providers: [], consumers: [] } } : Model.view(path);
  }

  function buildViewModel() {
    const view = ensureView(state.path);
    const viewport = els.svg.getBoundingClientRect();
    const layout = Layout.compute(view.children, view.edges, view.ghosts, { width: viewport.width || 1000, height: viewport.height || 700 });
    lastLayout = layout;

    const edges = view.edges.map((e) => ({ ...e, bridges: Model.bridgesFor(e.from, e.to) }));

    let matches = null;
    if (state.query.trim()) {
      const q = state.query.trim().toLowerCase();
      matches = new Set(view.children.filter((c) => Model.label(c).toLowerCase().includes(q)));
    }
    if (state.spineMode) {
      const spine = new Set((Model.ANN.intro || {}).spine || []);
      matches = new Set(view.children.filter((c) => spine.has(c)));
    }

    return {
      path: state.path,
      children: view.children,
      edges,
      ghosts: view.ghosts,
      positions: layout.positions,
      ghostPositions: layout.ghostPositions,
      vertical: layout.vertical,
      selection: state.selection,
      focusMode: state.focusMode,
      showImports: state.showImports,
      showBridges: state.showBridges,
      showGhosts: state.showGhosts,
      matches,
    };
  }

  function renderGraphOnly() {
    const vm = buildViewModel();
    graphView.render(vm);
    const anyChildren = vm.children.length > 0;
    els.emptyState.hidden = !vm.matches || vm.matches.size > 0 || !anyChildren;
  }

  function renderMeta() {
    const isRoot = state.path === "";
    els.viewTitle.textContent = isRoot ? "ShorVerification" : Model.label(state.path);
    els.viewDescription.textContent = isRoot
      ? (Model.ANN.intro || {}).summary || ""
      : Model.summary(state.path) || "";
    const view = ensureView(state.path);
    const bridgeCount = Model.bridgesTouchingView(state.path).length;
    els.graphStats.innerHTML = `
      <div class="stat"><strong>${view.children.length}</strong><span>children</span></div>
      <div class="stat"><strong>${view.edges.length}</strong><span>import edges</span></div>
      <div class="stat"><strong>${bridgeCount}</strong><span>bridges</span></div>
    `;
  }

  function renderBreadcrumb() {
    const parts = state.path === "" ? [] : state.path.split("/");
    const crumbs = [{ label: "ShorVerification", path: "" }];
    let acc = "";
    parts.forEach((p) => {
      acc = acc ? `${acc}/${p}` : p;
      crumbs.push({ label: Model.label(acc), path: acc });
    });
    els.breadcrumb.innerHTML = crumbs.map((c, i) => `<button class="crumb" type="button" data-action="goto-view" data-path="${c.path}">${escapeHtml(c.label)}</button>${i < crumbs.length - 1 ? '<span class="crumb-sep">/</span>' : ""}`).join("");
  }

  function escapeHtml(s) {
    return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
  }

  function renderLegend() {
    const isFramework = state.path === "Framework" || state.path.startsWith("Framework/");
    if (isFramework || state.path === "") {
      els.legend.innerHTML = Object.entries(Model.ANN.roles || {}).map(([key, r]) => `
        <div class="legend-item"><span class="legend-dot" style="--legend-color:${r.color}"></span><span>${escapeHtml(r.label)}</span></div>
      `).join("");
    } else {
      els.legend.innerHTML = Object.entries(Model.ANN.layers || {}).map(([key, r]) => `
        <div class="legend-item"><span class="legend-dot" style="--legend-color:${r.color}"></span><span>${escapeHtml(r.label)}</span></div>
      `).join("");
    }
  }

  function renderRailTree() {
    Model.ancestors(state.path).forEach((p) => state.expandedPaths.add(p));
    state.expandedPaths.add("");

    function nodeRow(path, depth) {
      const n = Model.node(path);
      const isFolder = path === "" || n.kind === "folder";
      const children = path === "" ? Model.GRAPH.meta.order0 : (n.children || []);
      const expanded = state.expandedPaths.has(path);
      const isActive = path === state.path;
      const label = path === "" ? "ShorVerification" : Model.label(path);
      let html = `<div class="tree-row${isActive ? " active" : ""}" style="--depth:${depth}">`;
      if (isFolder && children.length) {
        html += `<button class="tree-toggle" type="button" data-action="tree-toggle" data-path="${path}">${expanded ? "▾" : "▸"}</button>`;
      } else {
        html += `<span class="tree-toggle tree-toggle-spacer"></span>`;
      }
      html += `<button class="tree-label" type="button" data-action="${isFolder ? "goto-view" : "tree-select-file"}" data-path="${path}">${escapeHtml(label)}</button>`;
      html += `</div>`;
      if (isFolder && expanded && children.length) {
        html += children.map((c) => nodeRow(c, depth + 1)).join("");
      }
      return html;
    }

    els.railTree.innerHTML = nodeRow("", 0);
  }

  function selectNode(id) {
    if (!Model.node(id)) return;
    state.selection = { type: "node", id };
    Router.set(state.path, id);
    renderDetails();
    renderGraphOnly();
  }

  function selectEdge(edge, bridge) {
    state.selection = { type: "edge", edge, bridge: bridge || null };
    renderDetails();
    renderGraphOnly();
  }

  function selectGhost(g) {
    state.selection = { type: "ghost", ghost: g, side: g.side === "left" || g.side === "top" ? "providers" : "consumers" };
    renderDetails();
    renderGraphOnly();
  }

  function renderDetails() {
    Details.render(els.detailsContent, { viewPath: state.path, selection: state.selection });
  }

  function setView(path, sel, opts) {
    if (path !== "" && !Model.view(path)) return;
    state.path = path;
    state.selection = sel ? { type: "node", id: sel } : null;
    state.query = "";
    els.searchInput.value = "";
    els.searchResults.hidden = true;
    if (!(opts && opts.skipRouter)) Router.set(path, sel || null);
    renderBreadcrumb();
    renderMeta();
    renderLegend();
    renderRailTree();
    renderDetails();
    renderGraphOnly();
    graphView.fit(buildViewModel());
  }

  function openPath(path) {
    setView(path);
  }

  function goToNode(path) {
    const parent = Model.parentOf(path);
    setView(parent === null ? "" : parent, path);
  }

  // --- delegated clicks for dynamically-built HTML (rail, details, breadcrumb) ---
  document.addEventListener("click", (ev) => {
    const el = ev.target.closest("[data-action]");
    if (!el) return;
    const action = el.dataset.action;
    if (action === "goto-view") { setView(el.dataset.path); return; }
    if (action === "tree-select-file") { goToNode(el.dataset.path); return; }
    if (action === "tree-toggle") {
      const p = el.dataset.path;
      if (state.expandedPaths.has(p)) state.expandedPaths.delete(p); else state.expandedPaths.add(p);
      renderRailTree();
      return;
    }
    if (action === "goto") { goToNode(el.dataset.path); return; }
    if (action === "open") { setView(el.dataset.path); return; }
    if (action === "select-bridge") {
      const from = el.dataset.from, to = el.dataset.to;
      const parent = Model.parentOf(from) === Model.parentOf(to) ? Model.parentOf(from) : "";
      const view = ensureView(parent || "");
      const edge = view.edges.find((e) => e.from === from && e.to === to) || { from, to, weight: 0, pairs: [] };
      const bridge = (Model.ANN.bridges || []).find((b) => b.from === from && b.to === to && b.theorem === el.dataset.theorem);
      if (state.path !== (parent || "")) setView(parent || "");
      selectEdge(edge, bridge);
      return;
    }
    if (action === "select-edge-in") {
      const parent = el.dataset.path || "";
      const from = el.dataset.from, to = el.dataset.to;
      if (state.path !== parent) setView(parent);
      const view = ensureView(parent);
      const edge = view.edges.find((e) => e.from === from && e.to === to);
      if (edge) selectEdge(edge);
      return;
    }
  });

  // --- toolbar ---
  els.fitBtn.addEventListener("click", () => graphView.fit(buildViewModel()));
  els.topBtn.addEventListener("click", () => setView(""));
  els.zoomIn.addEventListener("click", () => graphView.setScale(graphView.getTransform().scale + 0.16));
  els.zoomOut.addEventListener("click", () => graphView.setScale(graphView.getTransform().scale - 0.16));
  els.focusToggle.addEventListener("click", () => {
    state.focusMode = !state.focusMode;
    els.focusToggle.classList.toggle("active", state.focusMode);
    els.focusToggle.textContent = state.focusMode ? "Focus on" : "Show all";
    renderGraphOnly();
  });
  els.spineToggle.addEventListener("click", () => {
    state.spineMode = !state.spineMode;
    els.spineToggle.classList.toggle("active", state.spineMode);
    renderGraphOnly();
  });
  [["showImports", els.importsToggle], ["showBridges", els.bridgesToggle], ["showGhosts", els.ghostsToggle]].forEach(([key, btn]) => {
    btn.addEventListener("click", () => {
      state[key] = !state[key];
      btn.classList.toggle("active", state[key]);
      renderGraphOnly();
    });
  });

  els.searchInput.addEventListener("input", () => {
    state.query = els.searchInput.value;
    const results = Model.search(state.query);
    if (!state.query.trim()) { els.searchResults.hidden = true; return; }
    els.searchResults.hidden = false;
    els.searchResults.innerHTML = results.length
      ? results.map((r) => `
        <button class="search-row" type="button" data-search-path="${r.path}" data-decl="${r.declName || ""}">
          <strong>${escapeHtml(r.declName || Model.label(r.path))}</strong>
          <span>${escapeHtml(r.path)} · ${escapeHtml(r.kind)}</span>
        </button>`).join("")
      : `<div class="search-row search-empty">No matches</div>`;
    renderGraphOnly();
  });
  els.searchResults.addEventListener("click", (ev) => {
    const row = ev.target.closest(".search-row[data-search-path]");
    if (!row) return;
    els.searchResults.hidden = true;
    goToNode(row.dataset.searchPath);
  });
  document.addEventListener("click", (ev) => {
    if (!ev.target.closest(".search-wrap")) els.searchResults.hidden = true;
  });

  window.addEventListener("keydown", (ev) => {
    if (ev.target === els.searchInput) {
      if (ev.key === "Escape") { els.searchInput.value = ""; state.query = ""; els.searchResults.hidden = true; renderGraphOnly(); }
      return;
    }
    if (ev.key === "f") graphView.fit(buildViewModel());
    if (ev.key === "Escape") {
      if (state.selection) { state.selection = null; renderDetails(); renderGraphOnly(); }
      else if (state.path !== "") setView(Model.parentOf(state.path) || "");
    }
    if (ev.key === "Backspace" && state.path !== "") { ev.preventDefault(); setView(Model.parentOf(state.path) || ""); }
  });

  window.addEventListener("resize", () => { renderGraphOnly(); graphView.fit(buildViewModel()); });

  Router.onChange((r) => setView(r.path || "", r.sel, { skipRouter: true }));

  const initial = Router.current();
  setView(initial.path || "", initial.sel, { skipRouter: true });
})();
