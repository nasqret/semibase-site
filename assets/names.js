// SemiBase census: the lookup on names.html. A Cayley table of order at most six is renumbered in every way, and so
// is its transpose; the least renumbering, compared with those of the Smallsemi tables in forms.js, gives the
// semigroup [n, k], the triple (n, k, o) and the name of the variety it generates. build.py packs the least
// renumbering the same way (packed_form), two entries a, b per base-36 digit a * n + b.
(function (root) {
  var DIGITS = "0123456789abcdefghijklmnopqrstuvwxyz";
  var perms = {}, maps = {};

  function permutations(n) {
    if (perms[n]) return perms[n];
    var out = [];
    (function extend(prefix, rest) {
      if (!rest.length) { out.push(prefix); return; }
      rest.forEach(function (x, i) { extend(prefix.concat([x]), rest.slice(0, i).concat(rest.slice(i + 1))); });
    })([], Array.apply(null, Array(n)).map(function (_, i) { return i; }));
    return (perms[n] = out);
  }

  // The least renumbering of a 0-based table: over all permutations p, the table q(T[p(a)][p(b)]) with q the
  // inverse of p, read row by row and compared entry by entry, then packed.
  function canonical(T) {
    var n = T.length, best = null, cur = new Array(n * n);
    permutations(n).forEach(function (p) {
      var q = [], i = 0, a, b;
      for (a = 0; a < n; a++) q[p[a]] = a;
      for (a = 0; a < n; a++) for (b = 0; b < n; b++) cur[i++] = q[T[p[a]][p[b]]];
      if (best) {
        for (i = 0; i < cur.length && cur[i] === best[i]; i++);
        if (i === cur.length || cur[i] > best[i]) return;
      }
      best = cur.slice();
    });
    var s = "";
    for (var j = 0; j < best.length; j += 2) s += DIGITS.charAt(best[j] * n + (j + 1 < best.length ? best[j + 1] : 0));
    return s;
  }

  function transpose(T) {
    return T.map(function (row, a) { return row.map(function (_, b) { return T[b][a]; }); });
  }

  // Numbers 1 to n, or 0 to n - 1 when an entry is 0, row by row; anything else between them is ignored, so a
  // table copied from GAP works as it is. Returns {table} with a 0-based table, or {error}.
  function parse(text) {
    var numbers = (text.match(/\d+/g) || []).map(Number), count = numbers.length;
    var n = Math.round(Math.sqrt(count));
    if (!count) return { error: "Enter a Cayley table." };
    if (n * n !== count) return { error: count + " numbers: a table of order n has n² entries." };
    if (n > 6) return { error: "The census covers the orders one to six." };
    var base = numbers.indexOf(0) >= 0 ? 0 : 1;
    if (Math.max.apply(null, numbers) - base >= n) {
      return { error: "The entries must be the numbers 1 to " + n + ", or 0 to " + (n - 1) + "." };
    }
    var T = [];
    for (var a = 0; a < n; a++) T.push(numbers.slice(a * n, a * n + n).map(function (x) { return x - base; }));
    for (a = 0; a < n; a++) for (var b = 0; b < n; b++) for (var c = 0; c < n; c++) {
      if (T[T[a][b]][c] !== T[a][T[b][c]]) {
        var name = function (x) { return String(x + base); };
        return { error: "Not a semigroup: (" + name(a) + "·" + name(b) + ")·" + name(c) + " = " + name(T[T[a][b]][c]) +
                 " but " + name(a) + "·(" + name(b) + "·" + name(c) + ") = " + name(T[a][T[b][c]]) + "." };
      }
    }
    return { table: T };
  }

  // The semigroup [n, k] and orientation o of a table, with the name of its variety, from the data of forms.js.
  function lookup(T, data) {
    var n = T.length, w = Math.ceil(n * n / 2), width = w + 4, forms = data.forms[n], k, o = 0;
    if (!maps[n]) {
      maps[n] = {};
      for (k = 1; k * width <= forms.length; k++) maps[n][forms.substr((k - 1) * width, w)] = k;
    }
    k = maps[n][canonical(T)];
    if (!k) { k = maps[n][canonical(transpose(T))]; o = 1; }
    if (!k) return null;
    var v = parseInt(forms.substr((k - 1) * width + w + 2 * o, 2), 36);
    return { n: n, k: k, o: o, name: data.names[v], finite: data.nonfinite.indexOf(data.names[v]) < 0 };
  }

  // The triple (n, k, o) and the label of a name, from its address: "5-540", "5-540-op", "3842", "3842-op".
  function nameOf(slug) {
    var m = /^(?:(\d)-)?(\d+)(-op)?$/.exec(slug), n = m[1] ? parseInt(m[1], 10) : 6, k = parseInt(m[2], 10);
    return { n: n, k: k, o: m[3] ? 1 : 0, label: "V[" + n + ", " + k + "]" + (m[3] ? "ᵒᵖ" : "") };
  }

  root.sbCanonical = canonical;
  root.sbParseTable = parse;
  root.sbLookup = lookup;
  root.sbNameOf = nameOf;
  if (typeof document === "undefined") return;

  var form = document.getElementById("lookup"), out = document.getElementById("lookup-out");
  if (!form) return;
  function semigroup(n, k, o) {
    return "<a href=\"s/" + sbSlug(n, k) + ".html\">[" + n + ", " + k + "]</a>" + (o ? "ᵒᵖ" : "");
  }
  function show(html) { out.innerHTML = html; out.hidden = false; }
  function withForms(then) {
    if (root.SB_FORMS) return then();
    show("<p>Loading the tables …</p>");
    var script = document.createElement("script");
    script.src = form.getAttribute("data-forms");
    script.onload = then;
    script.onerror = function () { show("<p>The tables could not be loaded.</p>"); };
    document.head.appendChild(script);
  }
  function run() {
    var parsed = parse(form.table.value);
    if (parsed.error) return show("<p>" + parsed.error + "</p>");
    withForms(function () {
      var r = lookup(parsed.table, root.SB_FORMS);
      if (!r) return show("<p>This table matches no semigroup of the census.</p>");
      var v = nameOf(r.name), self = v.n === r.n && v.k === r.k && v.o === r.o;
      show("<p>This is " + (r.o ? "the opposite of " + semigroup(r.n, r.k, 0) + ", with the transposed table"
                                : "the semigroup " + semigroup(r.n, r.k, 0)) +
           ", up to renumbering: the triple (" + r.n + ", " + r.k + ", " + r.o + ").</p>" +
           "<p>It generates the variety <a href=\"v/" + r.name + ".html\"><b>" + v.label + "</b></a>" +
           (self ? ", which is named after it." : ", named after its least generator " + semigroup(v.n, v.k, v.o) + ".") +
           (r.finite ? "" : " This variety has no finite basis.") + "</p>");
    });
  }
  form.addEventListener("submit", function (event) { event.preventDefault(); run(); });
  var example = document.getElementById("lookup-example");
  if (example) {
    example.addEventListener("click", function () { form.table.value = example.getAttribute("data-table"); run(); });
  }
})(typeof window !== "undefined" ? window : globalThis);
