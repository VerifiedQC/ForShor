// Column assignment + node positioning for one view's *drawn* edges (see
// Model.drawnEdgesFor). Strictly left to right: column = dependency rank
// (or a curated override), a column may hold several nodes stacked
// vertically. Pure functions: given children + drawn edges (+ optional
// columns override) + a viewport size, return positions.
const Layout = (() => {
  const NODE_WIDTH = 220;
  const NODE_HEIGHT = 92;
  const VERTICAL_BREAKPOINT = 640;
  const COL_GAP = 300;
  const ROW_GAP = 40;

  // Longest-path-from-source rank, tolerant of the rare aggregate cycle. By
  // the time this runs the edge set is already curated or transitively
  // reduced (see model.js), so in practice this always terminates cleanly,
  // but the force-release keeps it robust regardless.
  function computeRanks(children, edges) {
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
        let best = null;
        let bestDeg = Infinity;
        for (const c of children) {
          if (!done.has(c) && indegree.get(c) < bestDeg) {
            bestDeg = indegree.get(c);
            best = c;
          }
        }
        if (best === null) break;
        queue.push(best);
        done.add(best);
      }
      const id = queue.shift();
      for (const t of adj.get(id)) {
        rank.set(t, Math.max(rank.get(t), rank.get(id) + 1));
        indegree.set(t, indegree.get(t) - 1);
        if (indegree.get(t) <= 0 && !done.has(t)) {
          done.add(t);
          queue.push(t);
        }
      }
    }
    return rank;
  }

  function groupByRank(children, rank) {
    const groups = new Map();
    children.forEach((c) => {
      const r = rank.get(c) || 0;
      if (!groups.has(r)) groups.set(r, []);
      groups.get(r).push(c);
    });
    return [...groups.entries()].sort((a, b) => a[0] - b[0]).map(([, ids]) => ids);
  }

  // Two-pass barycenter heuristic (Sugiyama-style) to reduce edge crossings
  // by reordering nodes *within* their column: one pass left-to-right using
  // each node's predecessors (already-settled, lower columns), one pass
  // right-to-left using successors (already-settled, higher columns). Column
  // assignment itself never changes — only the top-to-bottom order within it.
  function orderByBarycenter(columns, edges) {
    const order = new Map();
    columns.forEach((ids) => ids.forEach((id, i) => order.set(id, i)));

    const succ = new Map(), pred = new Map();
    edges.forEach((e) => {
      if (!succ.has(e.from)) succ.set(e.from, []);
      succ.get(e.from).push(e.to);
      if (!pred.has(e.to)) pred.set(e.to, []);
      pred.get(e.to).push(e.from);
    });

    function pass(cols, neighborMap) {
      cols.forEach((ids) => {
        if (ids.length < 2) return;
        const scored = ids.map((id) => {
          const nbrs = neighborMap.get(id) || [];
          const key = nbrs.length ? nbrs.reduce((s, n) => s + (order.get(n) ?? 0), 0) / nbrs.length : order.get(id);
          return { id, key };
        });
        scored.sort((a, b) => a.key - b.key);
        scored.forEach((s, i) => { order.set(s.id, i); });
        ids.sort((a, b) => order.get(a) - order.get(b));
      });
    }

    pass(columns, pred); // left to right, using predecessors (lower columns)
    pass([...columns].reverse(), succ); // right to left, using successors (higher columns)
    return columns;
  }

  function isVertical(width) {
    return width < VERTICAL_BREAKPOINT;
  }

  // Returns { positions: Map<id,{x,y,w,h}>, columnOf: Map<id,number>,
  //           columns: string[][], vertical: bool }
  function compute(children, drawnEdges, columnsOverride, viewport) {
    const vertical = isVertical(viewport.width);
    let columns;
    if (columnsOverride && columnsOverride.length) {
      columns = columnsOverride.map((col) => col.slice());
    } else {
      const rank = computeRanks(children, drawnEdges);
      columns = orderByBarycenter(groupByRank(children, rank), drawnEdges);
    }

    const positions = new Map();
    const columnOf = new Map();
    columns.forEach((ids, ci) => ids.forEach((id) => columnOf.set(id, ci)));

    if (vertical) {
      // Narrow screens: stack columns top to bottom instead of left to
      // right, each column's own members side by side.
      let y = 40;
      columns.forEach((ids) => {
        const rowWidth = ids.length * NODE_WIDTH + Math.max(0, ids.length - 1) * ROW_GAP;
        const startX = Math.max(20, (viewport.width - rowWidth) / 2);
        ids.forEach((id, i) => positions.set(id, { x: startX + i * (NODE_WIDTH + ROW_GAP), y, w: NODE_WIDTH, h: NODE_HEIGHT }));
        y += NODE_HEIGHT + 64;
      });
    } else {
      // A long chain of mostly single-node columns (e.g. the root map:
      // Framework -> PhaseProduct -> QFT -> ... -> Reference) would
      // otherwise land every one of those nodes on the exact same y —
      // a dead-flat line. A gentle single-arc vertical offset per column
      // (a "rainbow" shape, biggest in the middle, zero at both ends) is
      // enough to read as a flowing pipeline instead, without touching the
      // left-to-right column/edge semantics at all.
      const singleNodeCols = columns.filter((ids) => ids.length === 1).length;
      const arcAmplitude = columns.length > 2 && singleNodeCols >= columns.length - 2 ? 64 : 0;

      columns.forEach((ids, ci) => {
        const arc = arcAmplitude ? -Math.sin((ci / (columns.length - 1)) * Math.PI) * arcAmplitude : 0;
        const groupHeight = ids.length * NODE_HEIGHT + Math.max(0, ids.length - 1) * ROW_GAP;
        const startY = Math.max(30, (viewport.height - groupHeight) / 2) + arc;
        ids.forEach((id, i) => {
          positions.set(id, { x: 40 + ci * COL_GAP, y: startY + i * (NODE_HEIGHT + ROW_GAP), w: NODE_WIDTH, h: NODE_HEIGHT });
        });
      });
    }

    return { positions, columnOf, columns, vertical };
  }

  return { compute, NODE_WIDTH, NODE_HEIGHT, COL_GAP, ROW_GAP, VERTICAL_BREAKPOINT, isVertical };
})();
