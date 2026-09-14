# ShorVerification proof graph

Interactive map of `FastMultiplication/ShorVerification`: the outermost view
is `Framework` (the specification) alongside the `Implementation/` subsystems
(`Shared`, `PhaseProduct`, `QFT`, `ModularExponentiation`, `Shor`, `GateCount`,
`Reference`); opening any folder descends into its own graph of children,
down to individual `.lean` files.

Open `index.html` directly in a browser, or serve this directory locally:

```sh
python3 -m http.server 8765
```

Then visit `http://localhost:8765`. If that port is already busy, use
another port such as `8766`.

## How the data is built

* `data/graph.js` is **generated** by `scripts/gen_docs_graph.py`: it walks
  the tree, parses `import` lines, docstrings, and declarations out of every
  `.lean` file, converts every `README.md` to HTML, and aggregates import
  edges (and cross-folder "ghost port" edges) for every view in the tree.
  Never edit it by hand — regenerate it instead:

  ```sh
  scripts/gen_docs_graph.py
  ```

* `data/annotations.js` is **curated** by hand: role/layer colors, node
  summaries that override the generated fallback, and "bridge" edges that
  name the theorem crossing a folder boundary and explain why. Every bridge
  must name a real declaration and line up with a real generated import
  edge, or the check below fails:

  ```sh
  scripts/gen_docs_graph.py --check
  ```

  Run `--check` after any rename or move under `ShorVerification/` that
  might affect a curated bridge — that's the mechanism that keeps this site
  from going stale the way the previous hand-maintained version did (see
  `git log` for `REDESIGN_PLAN.md` if you want the full rationale).

## Viewer source

`src/model.js` merges the generated and curated data into one queryable
model; `src/layout.js` ranks and positions one view; `src/render.js` draws
it (SVG, pan/zoom/drag, focus dimming); `src/details.js` renders the right
pane; `src/router.js` keeps the URL hash (`#/PhaseProduct/Proofs?sel=...`)
in sync with the open view and selection; `src/app.js` wires it all
together. Plain `<script>` tags, no build step, so `file://` still works.
