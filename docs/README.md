# ShorVerification proof graph

Interactive map of `FastMultiplication/ShorVerification`: the outermost view
is `Framework` (the specification) alongside the `Implementation/` subsystems
(`Shared`, `PhaseProduct`, `QFT`, `ModularExponentiation`, `Shor`, `GateCount`,
`Reference`); opening any folder descends into its own graph of children,
down to individual `.lean` files. Every view is strictly left to right:
columns are dependency rank, a column may hold several nodes stacked
vertically.

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
  edges (and cross-folder provider/consumer "boundary" edges) for every view
  in the tree. Never edit it by hand — regenerate it instead:

  ```sh
  scripts/gen_docs_graph.py
  ```

* `data/annotations.js` is **curated** by hand under its `views` key, one
  entry per view path. A view entry can set:
  * `columns` (optional) — pins the left-to-right grid explicitly, one array
    per column, top to bottom. Every child of the view must appear exactly
    once, or `--check` fails. Omit it to let the viewer rank automatically
    (longest path from a source, then a two-pass barycenter ordering to
    reduce crossings).
  * `edges` — the hand-picked import edges to actually draw. Each is
    `{from, to, emphasis, label?, theorem?, why?}` with `emphasis` one of
    `"primary"` (full role/layer colour, labelled if `label` is set),
    `"secondary"` (thin grey, unlabelled — real structure that isn't the
    story), or `"dim"` (light dashed — Shared's edges). Every curated edge
    must be a real import edge in that view, and every `theorem` must
    resolve to a real declaration, or `--check` fails. Edges left out are
    not lost: a selected node's "Also imports / also imported by" section
    lists them, and the **All imports** toolbar toggle overlays every import
    edge as unlabelled secondary on top of the curated set.

  A view with no `views[path]` entry (or an empty `edges` list) falls back
  automatically: back edges (against the folder's own rank order — the one
  real case today is `Shor`'s `Spec ⇄ Proofs`) are dropped, then the
  remaining DAG is transitively reduced, and drawn as unlabelled primary
  edges. This is what every view deeper than the nine curated ones gets, so
  they can't turn into spaghetti even unmaintained.

  Validate curation against the generated graph:

  ```sh
  scripts/gen_docs_graph.py --check
  ```

  Run `--check` after any rename or move under `ShorVerification/` that
  might affect a curated view — that's the mechanism that keeps this site
  from going stale. It also prints an informational (non-failing) note when
  a curated view leaves a weight-10-or-more import undrawn, so a curator
  notices a big arrow they didn't mean to drop.

## Viewer source

`src/model.js` merges the generated and curated data into one queryable
model, including the automatic fallback (back-edge splitting + transitive
reduction) described above; `src/layout.js` assigns columns (rank or a
curated override) and positions one view; `src/render.js` draws it (SVG,
distributed ports, curved routing with a channel for arrows spanning
multiple columns, pan/zoom/drag, focus dimming); `src/details.js` renders
the right pane; `src/router.js` keeps the URL hash
(`#/PhaseProduct/Proofs?sel=...`) in sync with the open view and selection;
`src/app.js` wires it all together, including the left/right boundary
strips ("Uses" / "Used by") that replace connector lines with a
hover-to-highlight chip list. Plain `<script>` tags, no build step, so
`file://` still works.
