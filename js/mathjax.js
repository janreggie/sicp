window.MathJax = {
  tex: {
    inlineMath: [["\\(", "\\)"]],
    displayMath: [["\\[", "\\]"]],
    processEscapes: true,
    processEnvironments: true
  },
  options: {
    ignoreHtmlClass: ".*|",
    processHtmlClass: "arithmatex",
    enableMenu: true,          // set to false to disable the menu
    menuOptions: {
      settings: {
        texHints: true,        // put TeX-related attributes on MathML
        semantics: false,      // put original format in <semantic> tag in MathML
        zoom: 'Click',         // 'None, 'Click' or 'DoubleClick' as zoom trigger
        zscale: '200%',        // zoom scaling factor
        renderer: 'SVG',       // or 'CHTML'
        alt: false,            // true if ALT required for zooming
        cmd: false,            // true if CMD required for zooming
        ctrl: false,           // true if CTRL required for zooming
        shift: false,          // true if SHIFT required for zooming
        scale: 1,              // scaling factor for all math
        collapsible: false,    // true if complex math should be collapsible
        inTabOrder: true,      // true if tabbing includes math
      },
  }
};
