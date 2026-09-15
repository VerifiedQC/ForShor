(() => {
  const state = {
    path: "",
    selection: null, // {type:"node",id} | {type:"edge",edge} | {type:"external",target,side}
    focusMode: true,
    showAllImports: false,
    query: "",
    expandedPaths: new Set(),
    hoverExternal: null, // {target, side} while hovering a boundary-strip chip
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
    allImportsToggle: document.getElementById("allImportsToggleButton"),
    topBtn: document.getElementById("topButton"),
    usesStrip: document.getElementById("usesStrip"),
    usedByStrip: document.getElementById("usedByStrip"),
  };

  let lastLayout = null;

  const graphView = createGraphView(els.svg, els.stage, {
    onSelectNode: (id) => selectNode(id),
    onOpenNode: (id) => openPath(id),
    onSelectEdge: (edge) => selectEdge(edge),
    onBackgroundClick: () => { state.selection = null; renderDetails(); renderGraphOnly(); },
    onRerenderNeeded: () => renderGraphOnly(),
    onTransform: () => {},
  });

  function currentDrawn() {
    return Model.drawnEdgesFor(state.path);
  }

  function buildViewModel() {
    const drawn = currentDrawn();
    let edges = drawn.edges;
    if (state.showAllImports) {
      const raw = Model.rawView(state.path).edges;
      const drawnKeys = new Set(edges.map((e) => Model.edgeKey(e.from, e.to)));
      const extra = raw.filter((e) => !drawnKeys.has(Model.edgeKey(e.from, e.to))).map((e) => ({ ...e, emphasis: "secondary" }));
      edges = edges.concat(extra);
    }

    if (!lastLayout || lastLayout.path !== state.path || lastLayout.allImports !== state.showAllImports) {
      const viewport = els.svg.getBoundingClientRect();
      const layout = Layout.compute(drawn.children, edges, drawn.columns, { width: viewport.width || 1000, height: viewport.height || 700 });
      lastLayout = { path: state.path, allImports: state.showAllImports, ...layout };
    }

    let matches = null;
    if (state.query.trim()) {
      const q = state.query.trim().toLowerCase();
      matches = new Set(drawn.children.filter((c) => Model.label(c).toLowerCase().includes(q)));
    }

    const activeExternal = state.hoverExternal || (state.selection && state.selection.type === "external" ? state.selection : null);
    const highlightExternal = activeExternal ? Model.externalHighlightSet(state.path, activeExternal.target, activeExternal.side) : null;

    return {
      path: state.path,
      children: drawn.children,
      edges,
      backEdges: drawn.backEdges,
      totalCount: drawn.totalCount,
      positions: lastLayout.positions,
      columnOf: lastLayout.columnOf,
      columns: lastLayout.columns,
      vertical: lastLayout.vertical,
      selection: state.selection,
      focusMode: state.focusMode,
      matches,
      highlightExternal,
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
    const drawn = currentDrawn();
    els.graphStats.innerHTML = `
      <div class="stat"><strong>${drawn.children.length}</strong><span>nodes</span></div>
      <div class="stat"><strong>${drawn.edges.length} / ${drawn.totalCount}</strong><span>imports drawn</span></div>
      ${drawn.backEdges.length ? `<div class="stat"><strong>${drawn.backEdges.length}</strong><span>back edge${drawn.backEdges.length === 1 ? "" : "s"} hidden</span></div>` : ""}
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
    const drawn = currentDrawn();
    const isFramework = state.path === "Framework" || state.path.startsWith("Framework/") || state.path === "";
    const table = isFramework ? (Model.ANN.roles || {}) : (Model.ANN.layers || {});
    const present = new Set(drawn.children.map((c) => (isFramework ? Model.role(c) : Model.layer(c))));
    const entries = Object.entries(table).filter(([key]) => present.has(key));
    els.legend.innerHTML = (entries.length ? entries : Object.entries(table)).map(([, r]) => `
      <div class="legend-item"><span class="legend-dot" style="--legend-color:${r.color}"></span><span>${escapeHtml(r.label)}</span></div>
    `).join("");
  }

  function renderStrips() {
    const isRoot = state.path === "";
    const ghosts = isRoot ? { providers: [], consumers: [] } : (Model.view(state.path) || { ghosts: { providers: [], consumers: [] } }).ghosts;

    function chip(g, side) {
      const active = state.selection && state.selection.type === "external" && state.selection.target === g.target && state.selection.side === side;
      return `<button class="strip-chip${active ? " active" : ""}" type="button" data-action="external" data-side="${side}" data-target="${escapeHtml(g.target)}">
        <span class="strip-chip-label">${escapeHtml(Model.label(g.target))}</span>
        <span class="strip-chip-weight">${g.weight}</span>
      </button>`;
    }

    els.usesStrip.innerHTML = ghosts.providers.length
      ? `<div class="strip-title">Uses</div>${ghosts.providers.map((g) => chip(g, "providers")).join("")}`
      : "";
    els.usesStrip.hidden = !ghosts.providers.length;
    els.usedByStrip.innerHTML = ghosts.consumers.length
      ? `<div class="strip-title">Used by</div>${ghosts.consumers.map((g) => chip(g, "consumers")).join("")}`
      : "";
    els.usedByStrip.hidden = !ghosts.consumers.length;
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

  function selectEdge(edge) {
    state.selection = { type: "edge", edge };
    renderDetails();
    renderGraphOnly();
  }

  function selectExternal(target, side) {
    state.selection = { type: "external", target, side };
    renderDetails();
    renderStrips();
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
    renderStrips();
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

  // --- delegated clicks for dynamically-built HTML (rail, details, breadcrumb, strips) ---
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
    if (action === "external") { selectExternal(el.dataset.target, el.dataset.side); return; }
    if (action === "open-external") {
      const target = el.dataset.target;
      setView(Model.parentOf(target) || target);
      return;
    }
    if (action === "select-edge-in") {
      const parent = el.dataset.path || "";
      const from = el.dataset.from, to = el.dataset.to;
      if (state.path !== parent) setView(parent);
      const view = Model.rawView(parent);
      const edge = view.edges.find((e) => e.from === from && e.to === to);
      if (edge) selectEdge(edge);
      return;
    }
  });

  document.addEventListener("mouseover", (ev) => {
    const chip = ev.target.closest(".strip-chip");
    if (!chip) return;
    state.hoverExternal = { target: chip.dataset.target, side: chip.dataset.side };
    renderGraphOnly();
  });
  document.addEventListener("mouseout", (ev) => {
    const chip = ev.target.closest(".strip-chip");
    if (!chip) return;
    state.hoverExternal = null;
    renderGraphOnly();
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
  els.allImportsToggle.addEventListener("click", () => {
    state.showAllImports = !state.showAllImports;
    els.allImportsToggle.classList.toggle("active", state.showAllImports);
    renderGraphOnly();
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

  window.addEventListener("resize", () => { lastLayout = null; renderGraphOnly(); graphView.fit(buildViewModel()); });

  Router.onChange((r) => setView(r.path || "", r.sel, { skipRouter: true }));

  const initial = Router.current();
  setView(initial.path || "", initial.sel, { skipRouter: true });
})();
