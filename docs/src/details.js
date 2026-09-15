// Right-pane content: view (nothing selected), folder node, file node,
// edge, or boundary-strip external node. Pure rendering — everything here
// returns an HTML string; app.js wires up data-action clicks afterwards.
const Details = (() => {
  function esc(s) {
    return String(s == null ? "" : s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
  }

  function pill(text, cls) {
    return `<span class="pill${cls ? " " + cls : ""}">${esc(text)}</span>`;
  }

  function navChip(path, extraLabel) {
    const label = Model.label(path) + (extraLabel ? ` ${extraLabel}` : "");
    return `<button class="nav-chip" type="button" data-action="goto" data-path="${esc(path)}">${esc(label)}</button>`;
  }

  function section(title, html) {
    if (!html) return "";
    return `<div class="detail-section"><h3>${esc(title)}</h3>${html}</div>`;
  }

  function edgeChips(edges, viewPath) {
    if (!edges.length) return "";
    const rows = edges.map((e) => `
      <button class="edge-chip" type="button" data-action="select-edge-in" data-path="${esc(viewPath)}" data-from="${esc(e.from)}" data-to="${esc(e.to)}">
        <strong>${esc(e.label || e.theorem || `${Model.label(e.from)} → ${Model.label(e.to)}`)}</strong>
        <span>${esc(Model.label(e.from))} → ${esc(Model.label(e.to))}</span>
      </button>`).join("");
    return `<div class="edge-list">${rows}</div>`;
  }

  function pairsList(pairs) {
    if (!pairs || !pairs.length) return "";
    const rows = pairs.slice(0, 40).map(([f, t]) => `
      <div class="pair-row">
        <button class="file-link-btn" type="button" data-action="goto" data-path="${esc(f)}">${esc(f)}</button>
        <span class="pair-arrow">→</span>
        <button class="file-link-btn" type="button" data-action="goto" data-path="${esc(t)}">${esc(t)}</button>
      </div>`).join("");
    const more = pairs.length > 40 ? `<p class="muted-note">+${pairs.length - 40} more</p>` : "";
    return `<div class="pair-list">${rows}</div>${more}`;
  }

  function declRows(path, declarations) {
    const groups = {};
    declarations.forEach((d) => { (groups[d.kind] = groups[d.kind] || []).push(d); });
    return Object.entries(groups).map(([kind, decls]) => `
      <div class="decl-group">
        <h4>${esc(kind)}</h4>
        <div class="pill-list">
          ${decls.map((d) => `<a class="pill decl-pill" target="_blank" rel="noopener" href="${esc(Model.githubUrl(Model.node(path).fsPath, d.line))}">${esc(d.name)}</a>`).join("")}
        </div>
      </div>`).join("");
  }

  function viewCard(path) {
    const isRoot = path === "";
    const drawn = Model.drawnEdgesFor(path);
    const primary = drawn.edges.filter((e) => e.emphasis === "primary" && e.label);
    if (isRoot) {
      const intro = (Model.ANN.intro || {});
      const spine = (intro.spine || []).map((p) => navChip(p)).join(" → ");
      return `
        <div class="details-card">
          <div class="detail-kicker"><span class="detail-type">Map</span></div>
          <h2>${esc(intro.title || "ShorVerification")}</h2>
          <p>${esc(intro.summary || "")}</p>
          ${spine ? section("Reading spine", `<div class="spine-row">${spine}</div>`) : ""}
          ${section("Curated arrows in this view", edgeChips(primary, path))}
          ${Model.GRAPH.meta.implementationReadmeHtml ? `<a class="detail-action detail-action-inline" target="_blank" rel="noopener" href="${esc(Model.githubUrl("Implementation/README.md"))}">Read Implementation/README.md →</a>` : ""}
        </div>`;
    }
    const n = Model.node(path);
    return `
      <div class="details-card">
        <div class="detail-kicker">
          <span class="detail-type">${esc(Model.ANN.roles[Model.role(path)] ? Model.ANN.roles[Model.role(path)].label : "folder")}</span>
          <a class="detail-action detail-action-inline" target="_blank" rel="noopener" href="${esc(Model.githubTreeUrl(n.fsPath))}">View on GitHub</a>
        </div>
        <h2>${esc(Model.label(path))}</h2>
        <p>${esc(Model.summary(path) || "")}</p>
        ${section("Curated arrows in this view", edgeChips(primary, path))}
        ${n.readmeHtml ? `<a class="detail-action detail-action-inline" target="_blank" rel="noopener" href="${esc(Model.githubUrl(n.fsPath + "/README.md"))}">Read README.md →</a>` : ""}
      </div>`;
  }

  function folderCard(path) {
    const n = Model.node(path);
    const parent = Model.parentOf(path);
    const parentPath = parent === null ? "" : parent;
    const drawn = Model.drawnEdgesFor(parentPath);
    const edges = drawn.edges.filter((e) => e.from === path || e.to === path);
    const rawEdges = Model.rawView(parentPath).edges.filter((e) => e.from === path || e.to === path);
    const drawnKeys = new Set(edges.map((e) => Model.edgeKey(e.from, e.to)));
    const undrawn = rawEdges.filter((e) => !drawnKeys.has(Model.edgeKey(e.from, e.to)));
    const classes = Model.classesUnder(path);
    return `
      <div class="details-card">
        <div class="detail-kicker">
          <span class="detail-type">${esc((Model.ANN.roles[Model.role(path)] || {}).label || "folder")}</span>
          <a class="detail-action detail-action-inline" target="_blank" rel="noopener" href="${esc(Model.githubTreeUrl(n.fsPath))}">View on GitHub</a>
        </div>
        <h2>${esc(Model.label(path))}</h2>
        <p>${esc(Model.summary(path) || "A folder in the proof tree.")}</p>
        ${n.readmeHtml ? `<a class="detail-action detail-action-inline" target="_blank" rel="noopener" href="${esc(Model.githubUrl(n.fsPath + "/README.md"))}">Read README.md →</a>` : ""}
        <div class="pill-list">
          ${pill(`${n.children.length} children`)}
          ${pill(`${n.fileCount} files`)}
          ${pill(`${n.declCount} declarations`)}
        </div>
        <button class="detail-action" type="button" data-action="open" data-path="${esc(path)}">Open →</button>
        ${section("Arrows drawn here", edgeChips(edges, parentPath))}
        ${section("Also imports / also imported by", undrawn.length ? `<div class="pill-list">${undrawn.map((e) => {
          const other = e.from === path ? e.to : e.from;
          const dir = e.from === path ? "→" : "←";
          return `<button class="pill nav-pill" type="button" data-action="goto" data-path="${esc(other)}">${dir} ${esc(Model.label(other))} (${e.weight})</button>`;
        }).join("")}</div>` : "")}
        ${section("Lean classes declared under this folder", classes.length ? `<div class="pill-list">${classes.slice(0, 60).map((c) => `<a class="pill class-pill" target="_blank" rel="noopener" href="${esc(Model.githubUrl(Model.node(c.path).fsPath, c.line))}">${esc(c.name)}</a>`).join("")}</div>${classes.length > 60 ? `<p class="muted-note">+${classes.length - 60} more</p>` : ""}` : "")}
      </div>`;
  }

  function fileCard(path) {
    const n = Model.node(path);
    return `
      <div class="details-card">
        <div class="detail-kicker">
          <span class="detail-type">file · ${esc(Model.layer(path) || "")}</span>
          <a class="detail-action detail-action-inline" target="_blank" rel="noopener" href="${esc(Model.githubUrl(n.fsPath))}">View on GitHub</a>
        </div>
        <h2>${esc(Model.label(path))}</h2>
        <p>${esc(Model.summary(path) || "")}</p>
        <div class="pill-list">${pill(`${n.lines} lines`)}${pill(`${n.declarations.length} declarations`)}</div>
        ${section("Declarations", declRows(path, n.declarations))}
        ${section("Imports", n.imports.length ? `<div class="pill-list">${n.imports.map((i) => navChip(i)).join("")}</div>` : '<p class="muted-note">none in-repo</p>')}
        ${section("Imported by", n.importedBy.length ? `<div class="pill-list">${n.importedBy.map((i) => navChip(i)).join("")}</div>` : '<p class="muted-note">nothing yet</p>')}
      </div>`;
  }

  function edgeCard(edge) {
    const isCurated = edge.emphasis === "primary" && (edge.theorem || edge.why);
    return `
      <div class="details-card">
        <div class="detail-kicker"><span class="detail-type">${esc(edge.emphasis || "import")} edge</span></div>
        <h2>${esc(edge.theorem || (edge.label ? edge.label : `${Model.label(edge.from)} → ${Model.label(edge.to)}`))}</h2>
        ${isCurated ? `<p>${esc(edge.why || "")}</p>` : `<p>${edge.weight} file-level import${edge.weight === 1 ? "" : "s"} justify this arrow.</p>`}
        <div class="pill-list">${navChip(edge.from)}<span class="pair-arrow">→</span>${navChip(edge.to)}</div>
        ${section("Contributing imports", pairsList(edge.pairs))}
      </div>`;
  }

  function externalCard(target, side) {
    const parent = Model.parentOf(target) || "";
    const g = (side === "providers" ? "provides to" : "is used by");
    return `
      <div class="details-card">
        <div class="detail-kicker"><span class="detail-type">${side === "providers" ? "Uses" : "Used by"}</span></div>
        <h2>${esc(Model.label(target))}</h2>
        <p>This external folder ${g} the current view. Its internal counterparts are highlighted in the graph.</p>
        <button class="detail-action" type="button" data-action="open-external" data-target="${esc(target)}">Go to ${esc(Model.label(parent) || "map")} →</button>
      </div>`;
  }

  function render(container, ctx) {
    const { viewPath, selection } = ctx;
    let html;
    if (!selection || selection.type === null) {
      html = viewCard(viewPath);
    } else if (selection.type === "node") {
      html = Model.isFolder(selection.id) ? folderCard(selection.id) : fileCard(selection.id);
    } else if (selection.type === "edge") {
      html = edgeCard(selection.edge);
    } else if (selection.type === "external") {
      html = externalCard(selection.target, selection.side);
    } else {
      html = viewCard(viewPath);
    }
    container.innerHTML = html;
  }

  return { render };
})();
