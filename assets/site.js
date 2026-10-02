// SemiBase census: the search box of every page, lists drawn from bit sets, sortable tables,
// the column switch of wide tables on phones, and a random semigroup.
// build.py fills in the names of the 505 varieties.
var SB_VARIETIES = /*VARIETIES*/[];
var SB_NAMES = { "l": 3843, "b21": 8564, "b2^1": 8564, "a2g": 8878, "a2^g": 8878, "a21": 13747, "a2^1": 13747, "c8": 3842 };

// Accepts "3842", "[6, 3842]", "S6_3842", "V[7390]", or one of the names L, B21, A2g, A21, C8.
function sbGo(form) {
  var root = form.getAttribute("data-root") || "";
  var raw = (form.q.value || "").trim();
  var key = raw.toLowerCase().replace(/[\s_₂¹ᵍ₈]/g, function (c) {
    return { "₂": "2", "¹": "1", "ᵍ": "g", "₈": "8" }[c] || "";
  });
  var go = function (url) { window.location.href = root + url; return false; };
  if (SB_NAMES[key]) return go("s/" + SB_NAMES[key] + ".html");
  var v = /^v\[?(\d+)\]?$/.exec(key);
  if (v) {
    var t = parseInt(v[1], 10);
    if (SB_VARIETIES.indexOf(t) >= 0) return go("v/" + t + ".html");
    if (t >= 1 && t <= 15973) return go("s/" + t + ".html#variety");
  }
  var numbers = raw.match(/\d+/g);
  if (numbers) {
    var n = parseInt(numbers[numbers.length - 1], 10);
    if (n >= 1 && n <= 15973) return go("s/" + n + ".html");
  }
  return go("browse.html");
}

// A random semigroup, for the curious.
function sbRandom(root) {
  window.location.href = (root || "") + "s/" + (1 + Math.floor(Math.random() * 15973)) + ".html";
  return false;
}

(function () {
  // Long lists of semigroups come as a hexadecimal bit set, bit k-1 for [6, k], drawn when opened.
  document.querySelectorAll("details[data-bits]").forEach(function (details) {
    details.addEventListener("toggle", function () {
      var box = details.querySelector(".links");
      if (!details.open || box.childElementCount) return;
      var hex = details.getAttribute("data-bits"), root = details.getAttribute("data-root") || "";
      var html = [];
      for (var i = 0; i < hex.length; i++) {
        var digit = parseInt(hex.charAt(hex.length - 1 - i), 16);
        for (var b = 0; b < 4; b++) {
          if (digit & (1 << b)) {
            var k = 4 * i + b + 1;
            html.push("<a href=\"" + root + "s/" + k + ".html\">[6, " + k + "]</a>");
          }
        }
      }
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
          var text = row.cells[column].textContent.replace(/[,\s]/g, "");
          var m = text.match(/^V\[(\d+)\]$/) || text.match(/^(\d+)$/);
          return m ? parseInt(m[1], 10) : text;
        }
        rows.sort(function (a, b) {
          var x = key(a), y = key(b);
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
