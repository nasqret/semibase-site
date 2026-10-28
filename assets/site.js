// SemiBase census: the search box of every page, lists drawn from bit sets, sortable tables,
// the column switch of wide tables on phones, and a random semigroup.
// build.py fills in the names of the varieties, the named semigroups and the number of semigroups of each order.
var SB_VARIETIES = /*VARIETIES*/[];
var SB_NAMES = /*NAMES*/{};
var SB_COUNTS = /*COUNTS*/[];

function sbSlug(n, k) { return n === 6 ? String(k) : n + "-" + k; }

// Accepts "3842", "[6, 3842]", "S6_3842", "5-415", "[5, 415]", "V[5, 540]", "V[7390]ᵒᵖ", "7390-op",
// or one of the names L, B21, A2g, A21, C8, B2, A2.
function sbGo(form) {
  var root = form.getAttribute("data-root") || "";
  var raw = (form.q.value || "").trim();
  var key = raw.toLowerCase().replace(/ᵒᵖ/g, "op").replace(/[\s_₂¹ᵍ₈]/g, function (c) {
    return { "₂": "2", "¹": "1", "ᵍ": "g", "₈": "8" }[c] || "";
  });
  var go = function (url) { window.location.href = root + url; return false; };
  if (SB_NAMES[key]) return go("s/" + SB_NAMES[key] + ".html");
  var v = /^v\[?(?:(\d)[,\-])?(\d+)\]?-?(op)?$/.exec(key);
  if (v) {
    var vn = v[1] ? parseInt(v[1], 10) : 6, vk = parseInt(v[2], 10);
    var slug = sbSlug(vn, vk) + (v[3] ? "-op" : "");
    if (SB_VARIETIES.indexOf(slug) >= 0 || (vn === 6 && !v[3])) return go("v/" + slug + ".html");
    if (vk >= 1 && vk <= (SB_COUNTS[vn - 1] || 0)) return go("s/" + sbSlug(vn, vk) + ".html#variety");
  }
  var s = /^(?:s|\[|\()?(\d)[,\-_](\d+)[\])]?$/.exec(raw.toLowerCase().replace(/\s/g, ""));
  if (s) {
    var n = parseInt(s[1], 10), k = parseInt(s[2], 10);
    if (n >= 1 && n <= 6 && k >= 1 && k <= SB_COUNTS[n - 1]) return go("s/" + sbSlug(n, k) + ".html");
  }
  var numbers = raw.match(/\d+/g);
  if (numbers && numbers.length === 1) {
    var m = parseInt(numbers[0], 10);
    if (m >= 1 && m <= SB_COUNTS[5]) return go("s/" + m + ".html");
  }
  return go("browse.html");
}

// A random semigroup of order at most six, for the curious.
function sbRandom(root) {
  var total = SB_COUNTS.reduce(function (a, b) { return a + b; }, 0);
  var i = Math.floor(Math.random() * total), n = 1;
  while (i >= SB_COUNTS[n - 1]) { i -= SB_COUNTS[n - 1]; n++; }
  window.location.href = (root || "") + "s/" + sbSlug(n, i + 1) + ".html";
  return false;
}

(function () {
  // Long lists of semigroups come as bit sets "n:o:hex", one per order n and orientation o (1 for the
  // transposes), bit k-1 for [n, k]; they are drawn when opened.
  document.querySelectorAll("details[data-sets]").forEach(function (details) {
    details.addEventListener("toggle", function () {
      var box = details.querySelector(".links");
      if (!details.open || box.childElementCount) return;
      var root = details.getAttribute("data-root") || "", html = [];
      details.getAttribute("data-sets").split(" ").forEach(function (part) {
        var f = part.split(":"), n = parseInt(f[0], 10), op = f[1] === "1", hex = f[2];
        for (var i = 0; i < hex.length; i++) {
          var digit = parseInt(hex.charAt(hex.length - 1 - i), 16);
          for (var b = 0; b < 4; b++) {
            if (digit & (1 << b)) {
              var k = 4 * i + b + 1;
              html.push("<a href=\"" + root + "s/" + sbSlug(n, k) + ".html\">[" + n + ", " + k + "]" +
                        (op ? "ᵒᵖ" : "") + "</a>");
            }
          }
        }
      });
      box.innerHTML = html.join(" ");
    });
  });

  // Tables with class "sortable": click a column header to sort by it.
  document.querySelectorAll("table.sortable").forEach(function (table) {
    table.querySelectorAll("th").forEach(function (th, column) {
      th.classList.add("sort");
      th.setAttribute("tabindex", "0");
      function sort() {
        var body = table.tBodies[0], rows = Array.prototype.slice.call(body.rows);
        var dir = th.getAttribute("data-dir") === "1" ? -1 : 1;
        table.querySelectorAll("th").forEach(function (x) { x.removeAttribute("data-dir"); });
        th.setAttribute("data-dir", dir === 1 ? "1" : "-1");
        function key(row) {
          var text = row.cells[column].textContent.replace(/[,\s?]/g, "");
          var m = text.match(/^V\[(\d),(\d+)\](ᵒᵖ)?$/);
          if (m) return parseInt(m[1], 10) * 1e6 + parseInt(m[2], 10) * 2 + (m[3] ? 1 : 0);
          m = text.match(/^(\d+)$/);
          return m ? parseInt(m[1], 10) : text;
        }
        rows.sort(function (a, b) {
          var x = key(a), y = key(b);
          if (typeof x !== typeof y) return (typeof x === "number" ? -1 : 1) * dir;
          return (x < y ? -1 : x > y ? 1 : 0) * dir;
        });
        rows.forEach(function (row) { body.appendChild(row); });
      }
      th.addEventListener("click", sort);
      th.addEventListener("keydown", function (e) { if (e.key === "Enter") sort(); });
    });
  });

  // On phones, wide tables show their main columns; a button shows them all.
  document.querySelectorAll(".colsbtn").forEach(function (button) {
    button.addEventListener("click", function () {
      var target = document.getElementById(button.getAttribute("data-target"));
      var on = !target.classList.contains("allcols");
      target.classList.toggle("allcols", on);
      button.setAttribute("aria-pressed", String(on));
      button.textContent = on ? "Fewer columns" : "All columns";
    });
  });
})();
