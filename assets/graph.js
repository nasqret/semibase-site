// SemiBase census: the inclusion graph of the varieties, on the varieties page.
// Each variety is drawn below the varieties that contain it, and a line joins it to each variety directly
// above it. The layout comes from Graphviz (dot) with the data in graph-data.js, which is loaded when the
// graph is first shown. Selecting a variety colours everything above and below it; the view "around" it
// lays out only those varieties, up to a number of steps.
(function () {
  "use strict";
  var box = document.getElementById("graph");
  if (!box) return;
  var listView = document.getElementById("list-view"), graphView = document.getElementById("graph-view");
  var tabs = Array.prototype.slice.call(document.querySelectorAll(".tabs a"));
  var stage = box.querySelector(".view"), canvas = box.querySelector("canvas"), ctx = canvas.getContext("2d");
  var msgBox = box.querySelector(".msg"), tip = box.querySelector(".tip"), info = box.querySelector(".info");
  var form = box.querySelector("form"), input = form.querySelector("input");
  var btnAll = document.getElementById("g-all"), btnAround = document.getElementById("g-around");
  var stepsSel = document.getElementById("g-steps"), btnFull = document.getElementById("g-full");
  var reduceMotion = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
  var NONFINITE = [3843, 8564, 8878, 13747];       // of order six
  var NAMED = { "l": [6, 3843], "b21": [6, 8564], "b2^1": [6, 8564], "a2g": [6, 8878], "a2^g": [6, 8878],
                "a21": [6, 13747], "a2^1": [6, 13747], "c8": [6, 3842], "b2": [5, 415], "a2": [5, 868] };
  var DX = 90, DY = 110, READABLE = 0.72;  // spacing of the view around a variety, and a scale at which it reads well

  var G = null, loading = false, pending = null;
  var N = 0, E = 0, name = [], label = [], gx, gy, rad, gens, members, up = [], down = [], edgeLo, edgeHi, edgeD = [];
  var byName = {};
  var GLOBAL = null, L = null, paths = {};
  var view = { s: 1, x: 0, y: 0 }, cssW = 0, cssH = 0, dpr = 1, fitted = false;
  var mode = "all", steps = 2, sel = -1, hover = -1, group = null, cone = null;
  var colors = {}, font = "12px sans-serif", raf = 0, anim = 0, msgTimer = 0, lastHint = 0, touched = false;

  // ------------------------------------------------------------------ tabs and the address

  function parseHash() {
    var h = decodeURIComponent(window.location.hash.slice(1));
    var m = /^graph(?:=([\w-]+))?(?:&around=(\d+|all))?$/.exec(h);
    if (!m) return null;
    return { sel: m[1] || null, around: m[2] ? (m[2] === "all" ? 0 : parseInt(m[2], 10)) : null };
  }

  function route() {
    var h = parseHash();
    listView.hidden = !!h;
    graphView.hidden = !h;
    tabs.forEach(function (a) {
      a.setAttribute("aria-selected", String((a.getAttribute("href") === "#graph") === !!h));
    });
    if (!h) { if (box.classList.contains("full")) setFull(false); return; }
    if (G) { resize(); applyHash(h); } else { pending = h; load(); }
  }

  function setHash() {
    var h = "#graph" + (sel >= 0 ? "=" + name[sel] + (mode === "around" ? "&around=" + (steps || "all") : "") : "");
    try { history.replaceState(history.state, "", h); } catch (e) { }
  }

  function applyHash(h) {
    if (h.around !== null && [0, 1, 2, 3].indexOf(h.around) >= 0) { steps = h.around; stepsSel.value = String(steps); }
    if (h.sel !== null && byName[h.sel] === undefined && G.alias[h.sel]) h.sel = G.alias[h.sel];
    if (h.sel !== null && byName[h.sel] !== undefined) {
      mode = h.around !== null ? "around" : "all";
      select(byName[h.sel], true);
    }
  }

  // ------------------------------------------------------------------ data

  function load() {
    if (G || loading) return;
    loading = true;
    say("Loading the graph …");
    var s = document.createElement("script");
    s.src = box.getAttribute("data-src");
    s.onload = function () { G = window.SB_GRAPH; prepare(); start(); };
    s.onerror = function () { say("The graph could not be loaded."); };
    document.head.appendChild(s);
  }

  function prepare() {
    N = G.nodes.length; E = G.edges.length;
    gx = new Float64Array(N); gy = new Float64Array(N); rad = new Float64Array(N);
    gens = new Int32Array(N); members = new Int32Array(N);
    edgeLo = new Int32Array(E); edgeHi = new Int32Array(E);
    G.nodes.forEach(function (n, i) {
      name[i] = n[0]; gx[i] = n[1]; gy[i] = n[2]; rad[i] = n[3]; gens[i] = n[4]; members[i] = n[5]; label[i] = n[6];
      byName[n[0]] = i; up[i] = []; down[i] = [];
    });
    G.edges.forEach(function (e, j) {
      edgeLo[j] = e[0]; edgeHi[j] = e[1]; edgeD[j] = e[2];
      up[e[0]].push(e[1]); down[e[1]].push(e[0]);
    });
    up.forEach(function (list) { list.sort(function (a, b) { return a - b; }); });
    down.forEach(function (list) { list.sort(function (a, b) { return a - b; }); });
    GLOBAL = { x: gx, y: gy, vis: null, curve: false };
  }

  function start() {
    readColors();
    L = GLOBAL;
    buildPaths();
    if (window.ResizeObserver) new ResizeObserver(function () { resize(); }).observe(stage);
    window.addEventListener("resize", resize);
    resize();
    say(window.matchMedia("(pointer: coarse)").matches
      ? "Find a variety above, or zoom in and tap one. Full screen lets you pinch and drag."
      : "Click a variety to select it, or find one above. Drag to move; Ctrl + scroll or the buttons zoom.", 7000);
    if (pending) { var h = pending; pending = null; applyHash(h); }
  }

  // ------------------------------------------------------------------ relations and layouts

  function related(c, k) {
    var g = new Int8Array(N), limit = k > 0 ? k : 1e9;
    g[c] = 1;
    function spread(adj, mark) {
      var frontier = [c];
      for (var d = 0; frontier.length && d < limit; d++) {
        var next = [];
        frontier.forEach(function (v) {
          adj[v].forEach(function (u) { if (!g[u]) { g[u] = mark; next.push(u); } });
        });
        frontier = next;
      }
    }
    spread(up, 2);
    spread(down, 3);
    return g;
  }

  // The varieties related to c, in rows by the longest chain from c to each: the first row above c holds the
  // varieties directly above it, the first row below those directly below it. Each row is ordered so that the
  // lines cross little.
  function aroundLayout(c, k) {
    var vis = related(c, k), level = new Int32Array(N), rows = {};
    var ups = [], downs = [];
    for (var i = 0; i < N; i++) { if (vis[i] === 2) ups.push(i); else if (vis[i] === 3) downs.push(i); }
    ups.sort(function (a, b) { return gy[b] - gy[a]; });       // lower first: every line goes up the page
    downs.sort(function (a, b) { return gy[a] - gy[b]; });     // higher first
    ups.forEach(function (v) {
      var l = 0;
      down[v].forEach(function (u) { if ((vis[u] === 1 || vis[u] === 2) && level[u] + 1 > l) l = level[u] + 1; });
      level[v] = l;
    });
    downs.forEach(function (v) {
      var l = 0;
      up[v].forEach(function (u) { if ((vis[u] === 1 || vis[u] === 3) && level[u] - 1 < l) l = level[u] - 1; });
      level[v] = l;
    });
    [c].concat(ups, downs).forEach(function (v) { (rows[level[v]] = rows[level[v]] || []).push(v); });
    var keys = Object.keys(rows).map(Number).sort(function (a, b) { return b - a; });   // top row first
    var x = new Float64Array(N), y = new Float64Array(N);
    function place(row) { row.forEach(function (v, i) { x[v] = (i - (row.length - 1) / 2) * DX; }); }
    keys.forEach(function (l) { rows[l].sort(function (a, b) { return gx[a] - gx[b]; }); place(rows[l]); });
    function mean(v, adj) {
      var s = 0, m = 0;
      adj[v].forEach(function (u) { if (vis[u]) { s += x[u]; m++; } });
      return m ? s / m : x[v];
    }
    function sweep(l, adj) {
      var key = {};
      rows[l].forEach(function (v) { key[v] = mean(v, adj); });
      rows[l].sort(function (a, b) { return key[a] - key[b]; });
      place(rows[l]);
    }
    var above = keys.filter(function (l) { return l > 0; }).sort(function (a, b) { return a - b; });
    var below = keys.filter(function (l) { return l < 0; }).sort(function (a, b) { return b - a; });
    for (var pass = 0; pass < 4; pass++) {
      // outwards from c, each row following the row nearer to c; then back, each row following the farther one
      above.forEach(function (l) { sweep(l, down); });
      below.forEach(function (l) { sweep(l, up); });
      above.slice(0, -1).reverse().forEach(function (l) { sweep(l, up); });
      below.slice(0, -1).reverse().forEach(function (l) { sweep(l, down); });
    }
    above.forEach(function (l) { sweep(l, down); });
    below.forEach(function (l) { sweep(l, up); });
    keys.forEach(function (l) { rows[l].forEach(function (v) { y[v] = -l * DY; }); });
    return { x: x, y: y, vis: vis, curve: true };
  }

  function nodeR(i) { return L.curve ? Math.max(rad[i], 6) : rad[i]; }

  function curve(a, b) {
    var x1 = L.x[a], y1 = L.y[a], x2 = L.x[b], y2 = L.y[b], ym = (y1 + y2) / 2;
    return "M" + x1 + " " + y1 + "C" + x1 + " " + ym + " " + x2 + " " + ym + " " + x2 + " " + y2;
  }

  function buildPaths() {
    var all = [], other = [], ups = [], downs = [];
    for (var j = 0; j < E; j++) {
      var a = edgeLo[j], b = edgeHi[j];
      if (L.vis && (!L.vis[a] || !L.vis[b])) continue;
      var d = L.curve ? curve(a, b) : edgeD[j];
      if (!group) { all.push(d); continue; }
      var ga = group[a], gb = group[b];
      if (ga && gb && ga !== 3 && gb !== 3) ups.push(d);
      else if (ga && gb && ga !== 2 && gb !== 2) downs.push(d);
      else other.push(d);
    }
    function make(list) { return list.length ? new Path2D(list.join(" ")) : null; }
    paths = { all: make(all), other: make(other), up: make(ups), down: make(downs) };
  }

  // ------------------------------------------------------------------ drawing

  function readColors() {
    var cs = getComputedStyle(box);
    ["fg", "bg", "muted", "line", "accent", "good", "warn", "edge", "node", "soft"].forEach(function (k) {
      colors[k] = cs.getPropertyValue("--" + k).trim();
    });
    font = "12px " + getComputedStyle(document.body).fontFamily;
  }

  function redraw() { if (!raf) raf = requestAnimationFrame(draw); }

  function stroke(path, color, width, alpha) {
    if (!path) return;
    ctx.globalAlpha = alpha;
    ctx.strokeStyle = color;
    ctx.lineWidth = width / view.s;
    ctx.stroke(path);
  }

  function draw() {
    raf = 0;
    if (!G) return;
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    ctx.setTransform(dpr * view.s, 0, 0, dpr * view.s, dpr * view.x, dpr * view.y);
    ctx.lineCap = "round";
    if (group) {
      stroke(paths.other, colors.edge, 1, L.curve ? 1 : 0.35);
      stroke(paths.up, colors.good, 2, 0.9);
      stroke(paths.down, colors.warn, 2, 0.9);
    } else {
      stroke(paths.all, colors.edge, 1, Math.min(0.9, Math.max(0.45, 0.35 + view.s)));
    }
    var fills = [colors.node, colors.accent, colors.good, colors.warn];
    for (var g = 0; g < 4; g++) {
      ctx.beginPath();
      for (var i = 0; i < N; i++) {
        if (L.vis && !L.vis[i]) continue;
        if ((group ? group[i] : 0) !== g) continue;
        var r = nodeR(i);
        ctx.moveTo(L.x[i] + r, L.y[i]);
        ctx.arc(L.x[i], L.y[i], r, 0, 2 * Math.PI);
      }
      ctx.globalAlpha = g === 0 && group && !L.curve ? 0.3 : 1;
      ctx.fillStyle = fills[g];
      ctx.fill();
    }
    ctx.globalAlpha = 1;
    [sel, hover].forEach(function (i, n) {
      if (i < 0) return;
      ctx.beginPath();
      ctx.arc(L.x[i], L.y[i], nodeR(i) + 4 / view.s, 0, 2 * Math.PI);
      ctx.strokeStyle = n ? colors.fg : colors.accent;
      ctx.lineWidth = (n ? 1.5 : 2.5) / view.s;
      ctx.stroke();
    });
    labels();
  }

  function labels() {
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.font = font;
    ctx.textBaseline = "middle";
    ctx.lineJoin = "round";
    var all = L.curve ? view.s * DX >= 62 : view.s >= 1.6;
    var few = group && !L.curve && countGroup() <= 40;
    for (var i = 0; i < N; i++) {
      if (L.vis && !L.vis[i]) continue;
      if (!(all || i === sel || i === hover || (few && group[i]))) continue;
      var sx = L.x[i] * view.s + view.x, sy = L.y[i] * view.s + view.y;
      if (sx < -80 || sy < -20 || sx > cssW + 20 || sy > cssH + 20) continue;
      var text = label[i], r = nodeR(i) * view.s, tx = sx + r + 4, ty = sy;
      ctx.textAlign = "left";
      if (L.curve && i !== sel) {      // around a variety: names above the larger ones, below the smaller ones
        ctx.textAlign = "center";
        tx = sx;
        ty = group[i] === 2 ? sy - r - 9 : sy + r + 10;
      }
      ctx.lineWidth = 3;
      ctx.strokeStyle = colors.bg;
      ctx.strokeText(text, tx, ty);
      ctx.fillStyle = i === sel ? colors.accent : colors.fg;
      ctx.fillText(text, tx, ty);
    }
  }

  var groupCount = -1;
  function countGroup() {
    if (groupCount < 0) { groupCount = 0; for (var i = 0; i < N; i++) if (group[i]) groupCount++; }
    return groupCount;
  }

  // ------------------------------------------------------------------ the view

  function resize() {
    var r = stage.getBoundingClientRect();
    if (r.width < 2 || r.height < 2) return;               // hidden
    var oldW = cssW, oldH = cssH;
    cssW = r.width; cssH = r.height; dpr = window.devicePixelRatio || 1;
    canvas.width = Math.round(cssW * dpr); canvas.height = Math.round(cssH * dpr);
    if (!G) return;
    if (!fitted) { fitted = true; fit(false); return; }
    view.x += (cssW - oldW) / 2; view.y += (cssH - oldH) / 2;  // keep the centre in place
    redraw();
  }

  function clampScale(s) { return Math.min(8, Math.max(0.04, s)); }

  function panel() {        // the part of the stage that the information panel covers, if it lies over it
    if (info.hidden || getComputedStyle(info).position !== "absolute") return { right: 0, bottom: 0 };
    var r = info.getBoundingClientRect(), st = stage.getBoundingClientRect();
    return r.left - st.left < 20 ? { right: 0, bottom: st.bottom - r.top + 8 } : { right: st.right - r.left + 12, bottom: 0 };
  }

  function go(target, animate) {
    cancelAnimationFrame(anim);
    if (!animate || reduceMotion) { view = target; redraw(); return; }
    var from = { s: view.s, x: view.x, y: view.y }, t0 = performance.now(), T = 320;
    function step(now) {
      var p = Math.min(1, (now - t0) / T), e = 1 - Math.pow(1 - p, 3);
      view = { s: from.s + (target.s - from.s) * e, x: from.x + (target.x - from.x) * e, y: from.y + (target.y - from.y) * e };
      draw();
      if (p < 1) anim = requestAnimationFrame(step);
    }
    anim = requestAnimationFrame(step);
  }

  function fit(animate, readable) {
    var x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    for (var i = 0; i < N; i++) {
      if (L.vis && !L.vis[i]) continue;
      var r = nodeR(i);
      x0 = Math.min(x0, L.x[i] - r); x1 = Math.max(x1, L.x[i] + r);
      y0 = Math.min(y0, L.y[i] - r); y1 = Math.max(y1, L.y[i] + r);
    }
    var p = panel(), pad = 24, w = cssW - 2 * pad - p.right, h = cssH - 2 * pad - p.bottom;
    var labelRoom = L.curve ? 30 : 0;
    if (x0 === Infinity) return;
    var s = clampScale(Math.min(w / (x1 - x0 + labelRoom + 1), h / (y1 - y0 + 1)));
    if (L.curve) s = Math.min(s, 1.4);
    if (readable && L.curve && sel >= 0 && s < READABLE) {   // too small to read: show the middle, readably
      say("Drag to see the rest, or press Fit to see it all.", 4000);
      go({ s: READABLE, x: (cssW - p.right) / 2 - L.x[sel] * READABLE, y: (cssH - p.bottom) / 2 - L.y[sel] * READABLE }, animate);
      return;
    }
    go({ s: s, x: pad + (w - (x1 - x0 + labelRoom) * s) / 2 - x0 * s, y: pad + (h - (y1 - y0) * s) / 2 - y0 * s }, animate);
  }

  function centreOn(i, minScale) {
    var p = panel(), s = Math.max(view.s, minScale || 0);
    go({ s: s, x: (cssW - p.right) / 2 - L.x[i] * s, y: (cssH - p.bottom) / 2 - L.y[i] * s }, true);
  }

  function zoomAt(px, py, factor) {
    var s = clampScale(view.s * factor), f = s / view.s;
    view = { s: s, x: px - (px - view.x) * f, y: py - (py - view.y) * f };
    redraw();
  }

  // ------------------------------------------------------------------ selection

  function select(i, centre) {
    sel = i;
    groupCount = -1;
    if (i < 0) {
      group = cone = null;
      info.hidden = true;
      if (mode === "around") { mode = "all"; L = GLOBAL; buildPaths(); fit(true); }
      else buildPaths();
    } else {
      cone = related(i, 0);
      if (mode === "around") { L = aroundLayout(i, steps); group = L.vis; }
      else { L = GLOBAL; group = cone; }
      buildPaths();
      showInfo(i);
      if (mode === "around") fit(true, true);
      else if (centre) centreOn(i, 1.2);
    }
    buttons();
    setHash();
    redraw();
  }

  function setMode(m) {
    if (m === mode || (m === "around" && sel < 0)) return;
    mode = m;
    if (sel >= 0) select(sel, true);
    else { buttons(); setHash(); }
  }

  function buttons() {
    btnAll.setAttribute("aria-pressed", String(mode === "all"));
    btnAround.setAttribute("aria-pressed", String(mode === "around"));
    btnAround.disabled = sel < 0;
    stepsSel.disabled = mode !== "around";
  }

  function fmt(n) { return n.toLocaleString("en"); }
  function plural(n, word, words) { return fmt(n) + " " + (n === 1 ? word : (words || word + "s")); }
  function esc(s) { return String(s).replace(/[&<>"]/g, function (c) { return { "&": "&amp;", "<": "&lt;", ">": "&gt;", "\"": "&quot;" }[c]; }); }

  function chips(title, list, cls) {
    if (!list.length) return "";
    return "<p>" + title + " (" + list.length + "):</p><div class=\"chips\">" + list.map(function (u) {
      return "<button type=\"button\" class=\"" + cls + "\" data-i=\"" + u + "\">" + label[u] + "</button>";
    }).join("") + "</div>";
  }

  function showInfo(i) {
    var above = 0, below = 0;
    for (var j = 0; j < N; j++) { if (cone[j] === 2) above++; else if (cone[j] === 3) below++; }
    var basis = G.bases[i].slice(1), k = G.bases[i][0];
    info.innerHTML = "<button type=\"button\" class=\"close\" aria-label=\"Close\">×</button>" +
      "<h3><a href=\"v/" + name[i] + ".html\">" + label[i] + "</a></h3>" +
      "<p>" + plural(gens[i], "semigroup") + " of order at most six generate" + (gens[i] === 1 ? "s" : "") + " it; " +
      plural(members[i], "semigroup") + " of order at most six lie" + (members[i] === 1 ? "s" : "") + " in it." +
      (G.nodes[i][7] === i ? " It is self-dual." : " Its dual is " + label[G.nodes[i][7]] + ".") + "</p>" +
      "<p>" + (above ? "It lies in " + plural(above, "other variety", "other varieties") : "It is maximal") + " and " +
      (below ? "contains " + plural(below, "other", "others") : "is minimal") + " among the " + fmt(N) + ".</p>" +
      "<p><b>Basis in the fewest variables</b>, " + plural(basis.length, "identity", "identities") + " in " +
      plural(k, "variable") + ":</p>" +
      "<ol class=\"basis\">" + basis.map(function (e) { return "<li>" + esc(e) + "</li>"; }).join("") + "</ol>" +
      chips("Directly above", up[i], "up") + chips("Directly below", down[i], "down") +
      "<div class=\"actions\"><a class=\"btn\" href=\"v/" + name[i] + ".html\">Variety page</a>" +
      "<a class=\"btn\" href=\"browse.html?variety=" + name[i] + "\">Semigroups generating it</a>" +
      (mode === "around" ? "<button type=\"button\" class=\"btn\" data-act=\"all\">Whole order</button>"
                         : "<button type=\"button\" class=\"btn\" data-act=\"around\">Around it</button>") + "</div>";
    info.hidden = false;
    info.scrollTop = 0;
  }

  info.addEventListener("click", function (e) {
    var t = e.target.closest("button");
    if (!t) return;
    if (t.classList.contains("close")) select(-1);
    else if (t.hasAttribute("data-i")) select(parseInt(t.getAttribute("data-i"), 10), true);
    else if (t.getAttribute("data-act")) setMode(t.getAttribute("data-act"));
  });

  // ------------------------------------------------------------------ messages and the tooltip

  function say(text, ms) {
    clearTimeout(msgTimer);
    msgBox.innerHTML = text ? "<span>" + esc(text) + "</span>" : "";
    if (ms) msgTimer = setTimeout(function () { msgBox.innerHTML = ""; }, ms);
  }

  function relation(i) {
    if (sel < 0 || i === sel) return "";
    var a = label[i], b = label[sel];
    if (cone[i] === 2) return "; contains " + b;
    if (cone[i] === 3) return "; lies in " + b;
    return "; " + a + " and " + b + " are not comparable";
  }

  function showTip(i, px, py) {
    if (i < 0) { tip.hidden = true; return; }
    tip.textContent = label[i] + ": " + plural(gens[i], "generator") + ", " + plural(members[i], "semigroup") + relation(i);
    tip.hidden = false;
    var w = tip.offsetWidth, h = tip.offsetHeight;
    tip.style.left = Math.max(4, Math.min(cssW - w - 4, px + 14)) + "px";
    tip.style.top = Math.max(4, Math.min(cssH - h - 4, py + 14)) + "px";
  }

  // ------------------------------------------------------------------ pointer, wheel and keys

  function hit(px, py, tolerance) {
    var lx = (px - view.x) / view.s, ly = (py - view.y) / view.s, best = -1, bestD = Infinity;
    for (var i = 0; i < N; i++) {
      if (L.vis && !L.vis[i]) continue;
      var dx = L.x[i] - lx, dy = L.y[i] - ly, d = Math.sqrt(dx * dx + dy * dy) - nodeR(i);
      if (d < bestD) { bestD = d; best = i; }
    }
    return bestD * view.s <= tolerance ? best : -1;
  }

  var pointers = {}, gesture = null;
  function pts() { return Object.keys(pointers).map(function (k) { return pointers[k]; }); }
  function local(e) { var r = canvas.getBoundingClientRect(); return { x: e.clientX - r.left, y: e.clientY - r.top }; }

  canvas.addEventListener("pointerdown", function (e) {
    if (!G) return;
    touched = true;
    say("");
    try { canvas.setPointerCapture(e.pointerId); } catch (err) { }
    pointers[e.pointerId] = local(e);
    var list = pts();
    if (list.length === 1) {
      gesture = { type: "pan", sx: list[0].x, sy: list[0].y, vx: view.x, vy: view.y, moved: false, t: Date.now(), touch: e.pointerType !== "mouse" };
    } else if (list.length === 2) {
      var a = list[0], b = list[1];
      gesture = { type: "pinch", d: Math.hypot(a.x - b.x, a.y - b.y) || 1, mx: (a.x + b.x) / 2, my: (a.y + b.y) / 2, s: view.s, vx: view.x, vy: view.y };
    }
  });

  canvas.addEventListener("pointermove", function (e) {
    if (!G) return;
    var p = local(e);
    if (!(e.pointerId in pointers)) {
      if (e.pointerType === "mouse") {
        var i = hit(p.x, p.y, 6);
        if (i !== hover) { hover = i; redraw(); }
        canvas.classList.toggle("over", i >= 0);
        showTip(i, p.x, p.y);
      }
      return;
    }
    pointers[e.pointerId] = p;
    var list = pts();
    if (gesture && gesture.type === "pan" && list.length === 1) {
      var dx = p.x - gesture.sx, dy = p.y - gesture.sy;
      if (Math.abs(dx) + Math.abs(dy) > 5) { gesture.moved = true; canvas.classList.add("dragging"); tip.hidden = true; }
      if (gesture.moved) { view.x = gesture.vx + dx; view.y = gesture.vy + dy; redraw(); }
    } else if (gesture && gesture.type === "pinch" && list.length === 2) {
      var a = list[0], b = list[1], d = Math.hypot(a.x - b.x, a.y - b.y) || 1;
      var mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2, s = clampScale(gesture.s * d / gesture.d);
      var lx = (gesture.mx - gesture.vx) / gesture.s, ly = (gesture.my - gesture.vy) / gesture.s;
      view = { s: s, x: mx - lx * s, y: my - ly * s };
      redraw();
    }
  });

  function release(e, cancelled) {
    if (!(e.pointerId in pointers)) return;
    var p = pointers[e.pointerId];
    delete pointers[e.pointerId];
    canvas.classList.remove("dragging");
    var list = pts();
    if (gesture && gesture.type === "pan" && !gesture.moved && !cancelled && Date.now() - gesture.t < 700) {
      var i = hit(p.x, p.y, gesture.touch ? 14 : 6);
      if (i >= 0) select(i === sel && mode !== "around" ? -1 : i, false);
      else if (sel >= 0 && mode !== "around") select(-1);
    }
    if (list.length === 1) gesture = { type: "pan", sx: list[0].x, sy: list[0].y, vx: view.x, vy: view.y, moved: true, t: 0 };
    else if (!list.length) gesture = null;
  }
  canvas.addEventListener("pointerup", function (e) { release(e, false); });
  canvas.addEventListener("pointercancel", function (e) { release(e, true); });
  canvas.addEventListener("pointerleave", function (e) {
    if (e.pointerType === "mouse" && !(e.pointerId in pointers)) { hover = -1; tip.hidden = true; redraw(); }
  });

  canvas.addEventListener("wheel", function (e) {
    if (!G) return;
    if (!(box.classList.contains("full") || e.ctrlKey || e.metaKey)) {
      if (Date.now() - lastHint > 4000) { lastHint = Date.now(); say("Hold Ctrl (or ⌘) and scroll to zoom, or use + and −.", 2500); }
      return;
    }
    e.preventDefault();
    var p = local(e);
    zoomAt(p.x, p.y, Math.exp(-e.deltaY * (e.deltaMode === 1 ? 0.05 : 0.002)));
  }, { passive: false });

  canvas.addEventListener("keydown", function (e) {
    var step = 60, k = e.key;
    if (k === "+" || k === "=") zoomAt(cssW / 2, cssH / 2, 1.4);
    else if (k === "-" || k === "_") zoomAt(cssW / 2, cssH / 2, 1 / 1.4);
    else if (k === "0") fit(true);
    else if (k === "ArrowLeft") { view.x += step; redraw(); }
    else if (k === "ArrowRight") { view.x -= step; redraw(); }
    else if (k === "ArrowUp") { view.y += step; redraw(); }
    else if (k === "ArrowDown") { view.y -= step; redraw(); }
    else if (k === "Escape") { if (box.classList.contains("full")) setFull(false); else select(-1); }
    else return;
    e.preventDefault();
  });

  // ------------------------------------------------------------------ toolbar

  document.getElementById("g-in").addEventListener("click", function () { zoomAt(cssW / 2, cssH / 2, 1.5); });
  document.getElementById("g-out").addEventListener("click", function () { zoomAt(cssW / 2, cssH / 2, 1 / 1.5); });
  document.getElementById("g-fit").addEventListener("click", function () { fit(true); });
  btnAll.addEventListener("click", function () { setMode("all"); });
  btnAround.addEventListener("click", function () { setMode("around"); });
  stepsSel.addEventListener("change", function () {
    steps = parseInt(stepsSel.value, 10);
    if (mode === "around" && sel >= 0) select(sel, true);
  });

  function setFull(on, fromHistory) {
    box.classList.toggle("full", on);
    document.body.classList.toggle("noscroll", on);
    btnFull.setAttribute("aria-pressed", String(on));
    btnFull.textContent = on ? "Exit full screen" : "Full screen";
    if (on && !fromHistory) { try { history.pushState({ sbFull: 1 }, "", window.location.hash); } catch (e) { } }
    if (!on && !fromHistory && history.state && history.state.sbFull) { try { history.back(); } catch (e) { } }
    resize();
  }
  btnFull.addEventListener("click", function () { setFull(!box.classList.contains("full")); });
  window.addEventListener("popstate", function (e) {
    if (box.classList.contains("full") && !(e.state && e.state.sbFull)) setFull(false, true);
  });

  // A variety by its name ("V[5, 540]ᵒᵖ", "5-540-op", "7390"), or the variety of a semigroup ("[6, 3842]", "C8").
  function classIndex(n, k) {
    var i = 0;
    for (var m = 1; m < n; m++) i += G.orders[m - 1];
    return i + k - 1;
  }

  form.addEventListener("submit", function (e) {
    e.preventDefault();
    if (!G) return;
    var q = input.value.trim(), t = q.toLowerCase().replace(/ᵒᵖ/g, "op").replace(/[\s_₂¹ᵍ₈]/g, function (c) {
      return { "₂": "2", "¹": "1", "ᵍ": "g", "₈": "8" }[c] || "";
    });
    var v = /^v\[?(?:(\d)[,\-])?(\d+)\]?-?(op)?$/.exec(t) || /^(?:(\d)-)?(\d+)-(op)$/.exec(t);
    if (v) {
      var slug = (v[1] && v[1] !== "6" ? v[1] + "-" : "") + v[2] + (v[3] ? "-op" : "");
      if (byName[slug] === undefined && G.alias[slug]) slug = G.alias[slug];
      if (byName[slug] !== undefined) { say(""); input.blur(); select(byName[slug], true); return; }
    }
    var s = NAMED[t] || /^(?:s|\[|\()?(\d)[,\-](\d+)[\])]?$/.exec(q.toLowerCase().replace(/[\s_]/g, function (c) {
      return c === "_" ? "," : "";
    }));
    var n, k;
    if (s && s.length === 2) { n = s[0]; k = s[1]; }
    else if (s) { n = parseInt(s[1], 10); k = parseInt(s[2], 10); }
    else { var m = /(\d+)\D*$/.exec(q); n = 6; k = m ? parseInt(m[1], 10) : NaN; }
    if (!(n >= 1 && n <= 6 && k >= 1 && k <= G.orders[n - 1])) {
      say("Enter a variety V[n, k], or a semigroup [n, k] of order n at most six.", 4000);
      return;
    }
    if (n === 6 && NONFINITE.indexOf(k) >= 0) {
      say("[6, " + k + "] has no finite basis; it lies in none of the " + fmt(N) + " varieties.", 5000);
      return;
    }
    var i = parseInt(G.cls.substr(2 * classIndex(n, k), 2), 36);
    say("[" + n + ", " + k + "] generates " + label[i] + ".", 4000);
    input.blur();
    select(i, true);
  });

  var mq = window.matchMedia("(prefers-color-scheme: dark)");
  var recolour = function () { readColors(); redraw(); };
  if (mq.addEventListener) mq.addEventListener("change", recolour); else if (mq.addListener) mq.addListener(recolour);

  route();
  window.addEventListener("hashchange", route);
})();
