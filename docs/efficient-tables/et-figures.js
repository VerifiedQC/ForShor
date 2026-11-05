// Mounts the two interactive figures of the efficient-tables page with ForShor's layer-graph machinery
// (../layers.js): the suite map (data/suite.js), the Fortran solver (data/fortran.js) and the three complexity graphs (data/complexity.js).
(function () {
  "use strict";
  if (!window.mountLayerGraph) return;
  window.mountLayerGraph(window.ET_SUITE, document.getElementById("suite"), "suite");
  window.mountLayerGraph(window.ET_FORTRAN, document.getElementById("fortran"), "fortran");
  // The complexity results: three claim-dependency graphs (data/complexity.js).
  if (window.ET_COMPLEXITY) {
    window.mountLayerGraph(window.ET_COMPLEXITY.upper, document.getElementById("cxupper"), "cxupper");
    window.mountLayerGraph(window.ET_COMPLEXITY.barrier, document.getElementById("cxbarrier"), "cxbarrier");
    window.mountLayerGraph(window.ET_COMPLEXITY.chain, document.getElementById("cxchain"), "cxchain");
  }

  // layers.js highlights every quoted snippet as Lean unless the file is .md. Here the snippets include
  // Fortran, Python and LaTeX, so when a panel opens, strip the Lean colouring from those.
  function fixPanel(panel) {
    panel.querySelectorAll("pre.lsnip.lean").forEach(function (pre) {
      var head = pre.previousElementSibling;
      var a = head && head.querySelector("a");
      var name = a ? a.getAttribute("href") : "";
      if (!/\.(f90|py|tex|json)(#|$)/.test(name)) return;
      var code = pre.querySelector("code");
      if (code) code.textContent = code.textContent;
      pre.classList.remove("lean");
    });
  }
  ["suite", "fortran", "cxupper", "cxbarrier", "cxchain"].forEach(function (id) {
    var root = document.getElementById(id);
    if (!root) return;
    new MutationObserver(function (muts) {
      muts.forEach(function (m) {
        m.addedNodes.forEach(function (n) {
          if (n.nodeType === 1 && n.classList.contains("ldetail")) fixPanel(n);
        });
      });
    }).observe(root, { childList: true });
    root.querySelectorAll(".ldetail").forEach(fixPanel);
  });
})();
