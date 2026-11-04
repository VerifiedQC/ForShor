// URL hash <-> {path, sel}. Format: #/PhaseProduct/Proofs?sel=Lowering
// (root view is just "#/"). Logical paths only (no "Implementation/" prefix,
// Framework/... unchanged), same ids used throughout Model/Layout/Render.
const Router = (() => {
  function parse(hash) {
    let raw = (hash || "").replace(/^#\/?/, "");
    let sel = null;
    const qIdx = raw.indexOf("?");
    if (qIdx !== -1) {
      const query = new URLSearchParams(raw.slice(qIdx + 1));
      sel = query.get("sel");
      raw = raw.slice(0, qIdx);
    }
    const path = decodeURIComponent(raw);
    return { path, sel: sel ? decodeURIComponent(sel) : null };
  }

  function build(path, sel) {
    let hash = "#/" + encodeURIComponent(path).replace(/%2F/g, "/");
    if (sel) hash += `?sel=${encodeURIComponent(sel)}`;
    return hash;
  }

  function set(path, sel) {
    const next = build(path, sel);
    if (location.hash !== next) location.hash = next;
  }

  function current() {
    return parse(location.hash);
  }

  function onChange(cb) {
    window.addEventListener("hashchange", () => cb(current()));
  }

  return { parse, build, set, current, onChange };
})();
