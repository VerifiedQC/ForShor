// Merges window.GRAPH (generated) with window.ANNOTATIONS (curated) into a
// single queryable model. Nothing here mutates GRAPH/ANNOTATIONS.
const Model = (() => {
  const GRAPH = window.GRAPH;
  const ANN = window.ANNOTATIONS || { nodes: {}, bridges: [], roles: {}, layers: {}, repo: {} };
  const annNodes = ANN.nodes || {};
  const repo = ANN.repo || { owner: "", repo: "", branch: "main" };

  function node(path) {
    return GRAPH.nodes[path] || null;
  }

  function parentOf(path) {
    if (!path) return null;
    const idx = path.lastIndexOf("/");
    return idx === -1 ? "" : path.slice(0, idx);
  }

  function depth0Of(path) {
    if (!path) return null;
    return path.split("/")[0];
  }

  function view(path) {
    return GRAPH.views[path] || null;
  }

  function isFolder(path) {
    const n = node(path);
    return !!n && n.kind === "folder";
  }

  function role(path) {
    if (annNodes[path] && annNodes[path].role) return annNodes[path].role;
    const d0 = depth0Of(path);
    if (d0 && annNodes[d0] && annNodes[d0].role) return annNodes[d0].role;
    return "framework";
  }

  const DEFINITION_FOLDERS = new Set(["Compiler", "Gates", "Circuit", "Lowering"]);

  function layer(path) {
    if (annNodes[path] && annNodes[path].layer) return annNodes[path].layer;
    const d0 = depth0Of(path);
    if (d0 === "Framework") return null;
    const n = node(path);
    if (!n) return null;
    const name = n.name.replace(/\.lean$/, "");
    if (name === "Main") return "main";
    if (name === "Spec") return "spec";
    if (name === "Proofs") return "proofs";
    if (DEFINITION_FOLDERS.has(name)) return "definitions";
    if (name === "Math" || name.startsWith("Math")) return "math";
    return null;
  }

  function firstParagraphFromHtml(html) {
    if (!html) return null;
    const m = html.match(/<p>([\s\S]*?)<\/p>/);
    if (!m) return null;
    return m[1].replace(/<[^>]+>/g, "");
  }

  function firstParagraphFromDocstring(doc) {
    if (!doc) return null;
    const blocks = doc.split(/\n\s*\n/).map((b) => b.trim()).filter(Boolean);
    for (const b of blocks) {
      if (/^#/.test(b)) continue;
      return b.replace(/\s+/g, " ");
    }
    return null;
  }

  function summary(path) {
    if (annNodes[path] && annNodes[path].summary) return annNodes[path].summary;
    const n = node(path);
    if (!n) return null;
    if (n.kind === "folder") {
      return firstParagraphFromHtml(n.readmeHtml);
    }
    return firstParagraphFromDocstring(n.docstring);
  }

  function subtitle(path) {
    if (annNodes[path] && annNodes[path].subtitle) return annNodes[path].subtitle;
    const l = layer(path);
    if (l && ANN.layers && ANN.layers[l]) return ANN.layers[l].label;
    return null;
  }

  function label(path) {
    const n = node(path);
    if (!n) return path;
    if (annNodes[path] && annNodes[path].label) return annNodes[path].label;
    return n.name;
  }

  function githubUrl(fsPath, line) {
    const base = `https://github.com/${repo.owner}/${repo.repo}/blob/${repo.branch}/${GRAPH.meta.root}/${fsPath}`;
    return line ? `${base}#L${line}` : base;
  }

  function githubTreeUrl(fsPath) {
    return `https://github.com/${repo.owner}/${repo.repo}/tree/${repo.branch}/${GRAPH.meta.root}/${fsPath}`;
  }

  function edgeKey(fromPath, toPath) {
    return `${fromPath}=>${toPath}`;
  }

  function bridgesFor(fromPath, toPath) {
    return (ANN.bridges || []).filter((b) => b.from === fromPath && b.to === toPath);
  }

  function bridgesTouchingView(viewPath) {
    const childSet = new Set(viewPath === null ? [] : (view(viewPath) || { children: [] }).children);
    return (ANN.bridges || []).filter((b) => childSet.has(b.from) && childSet.has(b.to));
  }

  // Every declaration in the tree, for global search. Built lazily.
  let _searchIndex = null;
  function searchIndex() {
    if (_searchIndex) return _searchIndex;
    const rows = [];
    for (const [path, n] of Object.entries(GRAPH.nodes)) {
      rows.push({ path, kind: n.kind, matchText: n.name.toLowerCase(), declName: null });
      if (n.kind === "file") {
        for (const d of n.declarations) {
          rows.push({ path, kind: "declaration", matchText: d.name.toLowerCase(), declName: d.name, declKind: d.kind, line: d.line });
        }
      }
    }
    _searchIndex = rows;
    return rows;
  }

  function search(query) {
    const q = query.trim().toLowerCase();
    if (!q) return [];
    return searchIndex().filter((r) => r.matchText.includes(q)).slice(0, 60);
  }

  function ancestors(path) {
    if (!path) return [];
    const parts = path.split("/");
    const out = [];
    for (let i = 1; i <= parts.length; i++) out.push(parts.slice(0, i).join("/"));
    return out;
  }

  function classesUnder(path) {
    const n = node(path);
    if (!n) return [];
    if (n.kind === "file") {
      return n.declarations
        .filter((d) => d.kind === "class" || d.kind === "structure")
        .map((d) => ({ ...d, path }));
    }
    const out = [];
    for (const c of n.children) out.push(...classesUnder(c));
    return out;
  }

  return {
    GRAPH, ANN, repo,
    node, view, parentOf, depth0Of, isFolder,
    role, layer, summary, subtitle, label,
    githubUrl, githubTreeUrl,
    edgeKey, bridgesFor, bridgesTouchingView,
    search, ancestors, classesUnder,
  };
})();
