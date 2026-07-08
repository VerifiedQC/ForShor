# ShorVerification Proof Graph

Static prototype for visualizing the `FastMultiplication/ShorVerification` proof architecture.

Open `index.html` directly in a browser, or serve this directory locally:

```sh
python3 -m http.server 8765
```

Then visit `http://localhost:8765`.
If that port is already busy, use another port such as `8766`.

The graph data currently lives in `app.js` as a curated model. A natural next step is to generate part of that model from Lean imports and declarations, then keep the human-written summaries as annotations.
Nodes can also carry curated Lean class metadata; the detail pane lists class names for the current view and for the selected node.
