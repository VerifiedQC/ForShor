// Merges window.GRAPH (generated) with window.ANNOTATIONS (curated) into a
// single queryable model. Nothing here mutates GRAPH/ANNOTATIONS.
const Model = (() => {
  const GRAPH = window.GRAPH;
  const ANN = window.ANNOTATIONS || { nodes: {}, views: {}, roles: {}, layers: {}, repo: {} };
  const annNodes = ANN.nodes || {};
  const annViews = ANN.views || {};
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

  function rawView(viewPath) {
    if (viewPath === "") {
      return { path: "", children: GRAPH.meta.order0, edges: GRAPH.views[""].edges, ghosts: { providers: [], consumers: [] } };
    }
    return view(viewPath);
  }

  // Longest-path-from-source rank, tolerant of aggregate cycles (same
  // approach as layout.js's computeRanks) — used only to decide which
  // edges run "backwards" against the folder's own layer order, so the
  // automatic fallback below can drop them before reducing.
  function longestPathRank(children, edges) {
    const indegree = new Map(children.map((c) => [c, 0]));
    const adj = new Map(children.map((c) => [c, []]));
    edges.forEach((e) => {
      if (adj.has(e.from) && indegree.has(e.to)) {
        adj.get(e.from).push(e.to);
        indegree.set(e.to, indegree.get(e.to) + 1);
      }
    });
    const rank = new Map(children.map((c) => [c, 0]));
    const done = new Set();
    const queue = children.filter((c) => indegree.get(c) === 0);
    queue.forEach((c) => done.add(c));
    while (done.size < children.length) {
      if (!queue.length) {
        let best = null, bestDeg = Infinity;
        for (const c of children) {
          if (!done.has(c) && indegree.get(c) < bestDeg) { bestDeg = indegree.get(c); best = c; }
        }
        if (best === null) break;
        queue.push(best);
        done.add(best);
      }
      const id = queue.shift();
      for (const t of adj.get(id) || []) {
        rank.set(t, Math.max(rank.get(t), rank.get(id) + 1));
        indegree.set(t, indegree.get(t) - 1);
        if (indegree.get(t) <= 0 && !done.has(t)) { done.add(t); queue.push(t); }
      }
    }
    return rank;
  }

  function splitBackEdges(children, edges) {
    const rank = longestPathRank(children, edges);
    const forward = [], back = [];
    edges.forEach((e) => {
      if ((rank.get(e.to) ?? 0) > (rank.get(e.from) ?? 0)) forward.push(e);
      else back.push(e);
    });
    return { forward, back };
  }

  // Drop edge (a,b) when some other path a -> ... -> b exists using the
  // remaining edges, so only the non-redundant structure is drawn.
  function transitiveReduction(children, edges) {
    const adj = new Map(children.map((c) => [c, []]));
    edges.forEach((e) => { if (adj.has(e.from)) adj.get(e.from).push(e.to); });
    function reachableAvoiding(skipFrom, skipTo, target) {
      const seen = new Set([skipFrom]);
      const stack = [skipFrom];
      while (stack.length) {
        const u = stack.pop();
        for (const v of adj.get(u) || []) {
          if (u === skipFrom && v === skipTo) continue;
          if (v === target) return true;
          if (!seen.has(v)) { seen.add(v); stack.push(v); }
        }
      }
      return false;
    }
    return edges.filter((e) => !reachableAvoiding(e.from, e.to, e.to));
  }

  // The edges a view actually draws: the curated list in annotations.js if
  // present (each merged with its real weight/pairs so the details pane can
  // still show contributing imports), else an automatic fallback — drop
  // back edges against the folder's own layer order, then transitively
  // reduce what remains, drawn as unlabelled primary edges.
  function drawnEdgesFor(viewPath) {
    const v = rawView(viewPath);
    if (!v) return { children: [], edges: [], columns: null, totalCount: 0, backEdges: [] };
    const curated = annViews[viewPath];
    const realByKey = new Map(v.edges.map((e) => [edgeKey(e.from, e.to), e]));

    if (curated && curated.edges && curated.edges.length) {
      const edges = curated.edges
        .map((ce) => {
          const real = realByKey.get(edgeKey(ce.from, ce.to));
          return real ? { ...real, ...ce } : null;
        })
        .filter(Boolean);
      return { children: v.children, edges, columns: curated.columns || null, totalCount: v.edges.length, backEdges: [] };
    }

    const { forward, back } = splitBackEdges(v.children, v.edges);
    const reduced = transitiveReduction(v.children, forward);
    const edges = reduced.map((e) => ({ ...e, emphasis: "primary" }));
    return { children: v.children, edges, columns: null, totalCount: v.edges.length, backEdges: back };
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

  function subtreeFiles(path) {
    const n = node(path);
    if (!n) return [];
    if (n.kind === "file") return [path];
    return n.children.flatMap(subtreeFiles);
  }

  // Which of a view's children actually import from (side="providers") or
  // are imported by (side="consumers") the given external node's subtree —
  // powers the boundary strips' hover/select highlight.
  function externalHighlightSet(viewPath, target, side) {
    const v = rawView(viewPath);
    if (!v) return new Set();
    const targetFiles = new Set(subtreeFiles(target));
    const result = new Set();
    v.children.forEach((c) => {
      const hit = subtreeFiles(c).some((f) => {
        const fn = node(f);
        const list = side === "providers" ? fn.imports : fn.importedBy;
        return list.some((other) => targetFiles.has(other));
      });
      if (hit) result.add(c);
    });
    return result;
  }

  return {
    GRAPH, ANN, repo,
    node, view, rawView, parentOf, depth0Of, isFolder,
    role, layer, summary, subtitle, label,
    githubUrl, githubTreeUrl,
    edgeKey, drawnEdgesFor, transitiveReduction,
    search, ancestors, classesUnder, subtreeFiles, externalHighlightSet,
  };
})();
