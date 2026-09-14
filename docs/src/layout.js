// Rank assignment + node/ghost positioning for one view. Pure functions:
// given a view's children/edges/ghosts and a viewport size, return positions.
const Layout = (() => {
  const NODE_WIDTH = 220;
  const NODE_HEIGHT = 104;
  const GHOST_WIDTH = 168;
  const GHOST_HEIGHT = 60;
  const VERTICAL_BREAKPOINT = 640;

  // Longest-path-from-source rank, tolerant of the rare aggregate cycle
  // (see scripts/gen_docs_graph.py: folder aggregation of an acyclic file
  // graph can still show a 2-cycle when a folder's children don't line up
  // with the true dependency layering). A stuck node is force-released so
  // the algorithm always terminates instead of looping forever.
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
    return [...groups.entries()].sort((a, b) => a[0] - b[0]);
  }

  function isVertical(width) {
    return width < VERTICAL_BREAKPOINT;
  }

  // Returns { positions: Map<id,{x,y,w,h}>, ghostPositions: Map<key,{x,y,w,h,side,target}>,
  //           ranks: Map<id,number>, vertical: bool, bounds: {minX,minY,maxX,maxY} }
  function compute(children, edges, ghosts, viewport) {
    const vertical = isVertical(viewport.width);
    const rank = computeRanks(children, edges);
    const groups = groupByRank(children, rank);
    const positions = new Map();

    const hasGhosts = ghosts && (ghosts.providers.length || ghosts.consumers.length);
    const ghostMargin = hasGhosts ? (vertical ? GHOST_HEIGHT + 56 : GHOST_WIDTH + 80) : 0;

    if (vertical) {
      const colX = Math.max(40, (viewport.width - NODE_WIDTH) / 2);
      const rowGap = 108;
      let y = 40 + ghostMargin;
      groups.forEach(([, ids]) => {
        ids.forEach((id, i) => positions.set(id, { x: colX, y: y + i * (NODE_HEIGHT + 40), w: NODE_WIDTH, h: NODE_HEIGHT }));
        y += ids.length * NODE_HEIGHT + Math.max(0, ids.length - 1) * 40 + rowGap;
      });
    } else {
      const levelCount = Math.max(1, groups.length);
      const colGap = Math.max(320, (viewport.width - 2 * ghostMargin - NODE_WIDTH) / Math.max(1, levelCount - 1 || 1));
      groups.forEach(([r, ids]) => {
        const rowGap = Math.max(150, (viewport.height - NODE_HEIGHT) / Math.max(1, ids.length));
        ids.forEach((id, i) => {
          const x = ghostMargin + 40 + r * colGap;
          const y = Math.max(30, (viewport.height - rowGap * (ids.length - 1)) / 2 + i * rowGap - NODE_HEIGHT / 2);
          positions.set(id, { x, y, w: NODE_WIDTH, h: NODE_HEIGHT });
        });
      });
    }

    const ghostPositions = new Map();
    if (hasGhosts) {
      const xs = [...positions.values()].map((p) => p.x);
      const ys = [...positions.values()].map((p) => p.y);
      const minX = xs.length ? Math.min(...xs) : 40;
      const maxX = xs.length ? Math.max(...xs) : 40;
      const minY = ys.length ? Math.min(...ys) : 40;
      const maxY = ys.length ? Math.max(...ys) : 40;

      if (vertical) {
        ghosts.providers.forEach((g, i) => {
          ghostPositions.set(`providers:${g.target}`, {
            x: (viewport.width - GHOST_WIDTH) / 2, y: 8 + i * (GHOST_HEIGHT + 10),
            w: GHOST_WIDTH, h: GHOST_HEIGHT, side: "top", target: g.target, weight: g.weight,
          });
        });
        const bottomY = maxY + NODE_HEIGHT + 24;
        ghosts.consumers.forEach((g, i) => {
          ghostPositions.set(`consumers:${g.target}`, {
            x: (viewport.width - GHOST_WIDTH) / 2, y: bottomY + i * (GHOST_HEIGHT + 10),
            w: GHOST_WIDTH, h: GHOST_HEIGHT, side: "bottom", target: g.target, weight: g.weight,
          });
        });
      } else {
        ghosts.providers.forEach((g, i) => {
          ghostPositions.set(`providers:${g.target}`, {
            x: 16, y: minY + i * (GHOST_HEIGHT + 20),
            w: GHOST_WIDTH, h: GHOST_HEIGHT, side: "left", target: g.target, weight: g.weight,
          });
        });
        const rightX = maxX + NODE_WIDTH + 40;
        ghosts.consumers.forEach((g, i) => {
          ghostPositions.set(`consumers:${g.target}`, {
            x: rightX, y: minY + i * (GHOST_HEIGHT + 20),
            w: GHOST_WIDTH, h: GHOST_HEIGHT, side: "right", target: g.target, weight: g.weight,
          });
        });
      }
    }

    return { positions, ghostPositions, ranks: rank, vertical };
  }

  return { compute, NODE_WIDTH, NODE_HEIGHT, GHOST_WIDTH, GHOST_HEIGHT, VERTICAL_BREAKPOINT, isVertical };
})();
