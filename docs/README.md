# ForShor project website

This directory is the project website, published by GitHub Pages at
<https://verifiedqc.github.io/ForShor/>. It has two tracks, joined by the site navigation
(`<nav class="site-nav">`, styled in `site.css`, repeated in each page's markup; keep the
links in step when adding a page):

* `index.html` (below): order finding, the ForShor proofs.
* `phasetripleproduct/`: the PhaseTripleProduct development, which lives in this repository under
  `ForShor/ShorVerification/Implementation/PhaseTripleProduct/` (`Statement.lean`, `Proofs/`,
  `Main.lean`). `index.html` has an algorithm-flow diagram and a layer graph (the shared `layers.js`,
  mounted with `window.mountLayerGraph`), the recursion figure (`ptpfig.js`) and the theorem table.
  Its data in `data/` is **generated** by `scripts/gen_ptp_site.py` from the Lean sources, with
  edges read from the `import` lines and quotations copied verbatim at a recorded `file:line`.
  Arguments: `--suite` is a ForShor checkout (a git repository) holding the development; `--ref`
  (default `HEAD` of it), `--repo-url` and `--root` set where the source links point; `--sto` is
  the ShorTableOptimization fork, still read for three inputs that are not part of the Lean
  development (the benchmark's `leaderboard/best-known.md`, and `policies/ref_ptp_2048.json` with
  `scripts/ptp_exact_width.py` for the figure's ladder). The generator refuses a dirty checkout
  (`--allow-dirty` overrides it while developing) and any file not tracked at `--ref`. Run it with
  `--check` to see whether the data is stale. It must be re-run when the Lean files change, and
  once the branch is pushed so the pinned commit exists on the remote.

The pages below describe the order-finding track.

The order-finding track has two pages:

* `index.html` — the project page, written as a short technical-blog post:
  what ForShor is, what the site is for, where to start, how to check the
  development and how to cite it.
  It also carries an interactive **layer graph** of the proof architecture
  (`layers.js`, data in `data/layers.js`): the top-level folders as five
  layers, the real import edges between them, and, on click, a panel with the
  layer's role, the theorem that carries it (copied verbatim from the source
  at a recorded `file:line`, so regenerate rather than edit a snippet), and
  what it rests on and feeds. `#layer-<Folder>` deep-links to an open layer.
  The quoted Lean statements are syntax-highlighted by a small tokenizer in
  `layers.js` (`leanHL`; colours in `site.css`). The page is always light,
  even when the reader's system is in dark mode.
  Plain HTML in [Tufte CSS](https://edwardtufte.github.io/tufte-css/) (`tufte.css` + the `et-book/` fonts, MIT, vendored unchanged; `site.css` holds our few additions); every claim about the proofs is taken
  from the [top-level README](../README.md).
  **Math is MathJax** (v3, `tex-chtml`, configured in the `<head>` of
  `index.html`): write TeX between `\(` and `\)` inline or `\[` and `\]` for
  display, in the page and in the curated `summary`/`note` text of
  `data/*.js` (escape the backslashes there: `"\\(n^{2+\\varepsilon}\\)"`).
  Lean names and Lean expressions stay in `<code>`, which MathJax skips.
  Panels the figures open after load are typeset by `window.typesetMath`
  (`layers.js`). Labels drawn inside the SVG figures (edge labels, the
  PhaseProduct diagram itself) are SVG `<text>` and stay Unicode.
* `navigator.html` — the interactive proof map described below. **Not linked
  from the project page for now** (2026-10-24; the layer graph replaces it);
  the page and its screenshots in `img/` are kept so it can come back. It is
  still in the dark theme of the earlier project page (`styles.css`; node, edge and legend colours
  are the `--role-*` / `--layer-*` / `--edge-*` variables there, the colours
  in `data/annotations.js` are only a fallback). Deep links
  of the old form `index.html#/Folder?sel=...` are redirected to
  `navigator.html` by a one-line script in `index.html`, so existing links
  keep working.

Interactive map of `ForShor/ShorVerification`: the outermost view
is `Framework` (the specification) alongside the `Implementation/` subsystems
(`PhaseProduct`, `QFT`, `ModularExponentiation`, `Compiler`, `Shor`, `QubitCount`,
`Reference`); opening any folder descends into its own graph of children,
down to individual `.lean` files. Every view is strictly left to right:
columns are dependency rank, a column may hold several nodes stacked
vertically.

Open `index.html` (or `navigator.html`) directly in a browser, or serve this directory locally:

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

* `data/layers.js`, `data/algorithm.js` and `data/pp.js` quote Lean declarations (file, line, code) for
  the project page, and `index.html` links to source lines inline. When files move or declarations are
  reformatted those quotes go stale; `scripts/reanchor_docs_data.py` finds each declaration again by
  name (namespace- and kind-aware, no guessing: an ambiguous name is an error), rewrites file, line
  and, where the code changed beyond whitespace, the code, keeping each snippet's trimming convention,
  and prints an old/new diff for every changed snippet so the caption next to it can be re-read.
  `scripts/reanchor_docs_data.py --check` exits 1 if anything is stale or unresolved. The folder blocks
  in `data/layers.js` (rows, curated edges, counts, summaries) are hand-curated; its `imports` are the
  real folder-to-folder imports, and every curated edge must be one of them.

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
    story), or `"dim"` (light dashed — real but incidental edges). Every curated edge
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
