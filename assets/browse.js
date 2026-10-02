// SemiBase census: the filterable list of all semigroups (browse.html).
// data.js holds one column per property, packed into strings: base-36 digits, one or more per semigroup.
(function () {
  var D = window.SEMIBASE, n = D.n;
  var basis = new Uint8Array(n), variety = new Int32Array(n), nil = new Uint8Array(n), idem = new Uint8Array(n);
  var flags = new Uint8Array(n), kind = new Uint8Array(n), lines = new Uint32Array(n);
  for (var i = 0; i < n; i++) {
    basis[i] = parseInt(D.basis.charAt(i), 36);
    var v = D.variety.substr(2 * i, 2);
    variety[i] = v === "--" ? 0 : D.varieties[parseInt(v, 36)];
    nil[i] = D.nil.charCodeAt(i) - 48;
    idem[i] = D.idem.charCodeAt(i) - 48;
    flags[i] = parseInt(D.flags.charAt(i), 36);
    kind[i] = parseInt(D.kind.charAt(i), 36);
    lines[i] = parseInt(D.lines.substr(4 * i, 4), 36);
  }
  var FLAG = { monoid: 1, comm: 2, band: 4, selfdual: 8, regular: 16 };
  var KEYS = {
    id: function (i) { return i; },
    basis: function (i) { return basis[i] || Infinity; },
    variety: function (i) { return variety[i] || Infinity; },
    idem: function (i) { return idem[i]; },
    nil: function (i) { return nil[i]; },
    kind: function (i) { return D.kinds[kind[i]]; },
    lines: function (i) { return lines[i]; }
  };
  var FILTERS = ["from", "to", "status", "bmin", "bmax", "variety", "idem", "nil", "monoid", "comm", "band",
                 "regular", "selfdual", "kind"];
  var PAGE = 300, shown = PAGE, sortKey = "id", sortDir = 1;

  function el(id) { return document.getElementById(id); }
  function val(id) { return el("f-" + id).value; }
  function num(id) { return parseInt(val(id), 10); }

  function filter() {
    var lo = num("from"), hi = num("to"), st = val("status"), bmin = num("bmin"), bmax = num("bmax");
    var vv = num("variety"), ide = val("idem") === "" ? -1 : parseInt(val("idem"), 10), nl = val("nil");
    var kd = val("kind") === "" ? -1 : parseInt(val("kind"), 10);
    var need = 0, forbid = 0;
    Object.keys(FLAG).forEach(function (f) {
      if (val(f) === "yes") need |= FLAG[f];
      if (val(f) === "no") forbid |= FLAG[f];
    });
    var out = [];
    for (var i = 0; i < n; i++) {
      var k = i + 1;
      if (!isNaN(lo) && k < lo) continue;
      if (!isNaN(hi) && k > hi) continue;
      if (st === "fb" && !basis[i]) continue;
      if (st === "nfb" && basis[i]) continue;
      if (!isNaN(bmin) && (!basis[i] || basis[i] < bmin)) continue;
      if (!isNaN(bmax) && (!basis[i] || basis[i] > bmax)) continue;
      if (!isNaN(vv) && variety[i] !== vv) continue;
      if (ide >= 0 && idem[i] !== ide) continue;
      if (nl === "yes" && !nil[i]) continue;
      if (nl === "no" && nil[i]) continue;
      if ((flags[i] & need) !== need || (flags[i] & forbid)) continue;
      if (kd >= 0 && kind[i] !== kd) continue;
      out.push(i);
    }
    return out;
  }

  function yes(x) { return x ? "yes" : "–"; }

  function render() {
    var list = filter(), key = KEYS[sortKey];
    list.sort(function (a, b) {
      var x = key(a), y = key(b);
      return (x < y ? -1 : x > y ? 1 : 0) * sortDir || a - b;
    });
    el("count").textContent = list.length.toLocaleString("en") + " of " + n.toLocaleString("en") + " semigroups";
    var html = [];
    list.slice(0, shown).forEach(function (i) {
      var k = i + 1, f = flags[i];
      html.push("<tr><td><a href=\"s/" + k + ".html\">[6, " + k + "]</a>" +
        (basis[i] ? "" : " <span class=\"badge nfb\">no finite basis</span>") + "</td>" +
        "<td class=\"num\">" + (basis[i] || "–") + "</td>" +
        "<td>" + (variety[i] ? "<a href=\"v/" + variety[i] + ".html\">V[" + variety[i] + "]</a>" : "–") + "</td>" +
        "<td class=\"num opt\">" + idem[i] + "</td>" +
        "<td class=\"num opt\">" + (nil[i] || "–") + "</td>" +
        "<td class=\"opt\">" + yes(f & 1) + "</td><td class=\"opt\">" + yes(f & 2) + "</td>" +
        "<td class=\"opt\">" + yes(f & 4) + "</td><td class=\"opt\">" + yes(f & 8) + "</td>" +
        "<td>" + D.kinds[kind[i]] + "</td>" +
        "<td class=\"num opt\">" + lines[i].toLocaleString("en") + "</td></tr>");
    });
    el("rows").innerHTML = html.join("");
    el("more").hidden = list.length <= shown;
    document.querySelectorAll("th.sort").forEach(function (th) {
      th.setAttribute("data-dir", th.getAttribute("data-key") === sortKey ? String(sortDir) : "");
    });
    var active = FILTERS.filter(function (p) { return val(p) !== ""; }).length;
    el("active").textContent = active ? " (" + active + " active)" : "";
  }

  function saveState() {
    var params = new URLSearchParams();
    FILTERS.forEach(function (p) { if (val(p) !== "") params.set(p, val(p)); });
    if (sortKey !== "id" || sortDir !== 1) params.set("sort", (sortDir < 0 ? "-" : "") + sortKey);
    var query = params.toString();
    try { history.replaceState(null, "", query ? "?" + query : window.location.pathname); } catch (e) { }
  }

  function update() { shown = PAGE; render(); saveState(); }

  FILTERS.forEach(function (p) {
    el("f-" + p).addEventListener("input", update);
    el("f-" + p).addEventListener("change", update);
  });
  document.querySelectorAll("th.sort").forEach(function (th) {
    function sort() {
      var key = th.getAttribute("data-key");
      sortDir = sortKey === key ? -sortDir : (key === "id" || key === "variety" || key === "kind" ? 1 : -1);
      sortKey = key;
      render();
      saveState();
    }
    th.setAttribute("tabindex", "0");
    th.addEventListener("click", sort);
    th.addEventListener("keydown", function (e) { if (e.key === "Enter") sort(); });
  });
  el("more").addEventListener("click", function () { shown += 2 * PAGE; render(); });
  el("reset").addEventListener("click", function () {
    FILTERS.forEach(function (p) { el("f-" + p).value = ""; });
    sortKey = "id"; sortDir = 1;
    update();
  });

  var params = new URLSearchParams(window.location.search);
  FILTERS.forEach(function (p) { if (params.has(p)) el("f-" + p).value = params.get(p); });
  if (params.has("sort")) {
    var s = params.get("sort");
    sortDir = s.charAt(0) === "-" ? -1 : 1;
    sortKey = s.replace(/^-/, "");
    if (!KEYS[sortKey]) { sortKey = "id"; sortDir = 1; }
  }
  // On a phone the filters start folded; the summary line counts those that are set.
  if (window.matchMedia("(max-width: 760px)").matches) el("filterbox").open = false;
  render();
})();
