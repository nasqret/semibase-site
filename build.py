#!/usr/bin/env python3
"""Build the SemiBase census: a static website about the semigroups of order six.

One page per semigroup (site/s/<k>.html) with its Cayley table, properties,
shortest known identity basis or the proof that none is finite, the Lean proof,
its variety and related semigroups; one page per variety (site/v/<k>.html); one
page per certified basis (site/b/<id>.html); and overview pages. The site is
plain HTML with a little JavaScript for search and filtering, and works when
opened from disk.

Inputs, from the semibase-order6 repository:
  research/order6/catalogue.json GAP Smallsemi 0.7.2: the 15,973 classes of order six
  provenance/final-census-map.json  the endpoint theorem of each class
and from the bases-min seal of M. Janota (data/):
  sealed-bases-v1.json           the certified basis of every finitely based class, read
                                 back from the Lean theorems by the bases-min seal
  reduced-forms-v1.json          each certified basis with the identities that follow from
                                 the others removed (Vampire)
  order-v2.json                  the 505 varieties and their inclusions (Vampire)
  census-rows-v1.json            for each basis, the classes of order six in which it holds
  graph-layout.json              the Graphviz layout of the graph of varieties (a cache)
The repository is a checkout of semibase-order6 (SEMIBASE_REPO, default
../semibase-order6); its Lean sources give the line of every theorem and the
code each proof needs, and its commit is the one the Lean links point to.

Usage: python3 build.py, then open site/index.html.
"""
import datetime
import hashlib
import html
import itertools
import json
import math
import os
import re
import shutil
import subprocess
import sys
from collections import Counter, defaultdict

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
OUT = os.path.join(HERE, "site")
REPO = os.path.abspath(os.environ.get("SEMIBASE_REPO", os.path.join(HERE, "..", "semibase-order6")))
REPO_URL = "https://github.com/nasqret/semibase-order6"
PAPER = "Proving at Scale for Universal Algebra, MATH-AI workshop, NeurIPS 2026"
N = 15973
CAS_PREFIX = "SemigroupBasis.Generated.Order6CASExplicitSourceUpstream."

NONFINITE = {
    3843: ("L", "Lee's semigroup L"),
    8564: ("B₂¹", "the Brandt monoid B₂¹"),
    8878: ("A₂ᵍ", "the semigroup A₂ᵍ, obtained from A₂ by adjoining an element g"),
    13747: ("A₂¹", "the monoid A₂¹, obtained from A₂ by adjoining an identity"),
}
NONFINITE_DETAIL = {
    3843: ("x y₁²⋯yₙ² x ≈ x yₙ²⋯y₁² x",
           "In a word equal in L to the left side the squares stay blocks, in the forward or in the reverse "
           "order, and no derivation step with an identity in fewer variables passes from one order to the other.",
           "W. T. Zhang and Y. F. Luo (2011)"),
    8564: ("x y₁⋯yₙ x yₙ⋯y₁ ≈ x yₙ⋯y₁ x y₁⋯yₙ",
           "A pattern in the occurrences of the letters survives every derivation step with an identity in fewer "
           "variables; the argument uses that xytyx and xtyxy are isoterms, equal in B₂¹ only to themselves.",
           "P. Perkins (1969), in the reconstruction of M. V. Sapir (1988)"),
    8878: ("(x₁²⋯xₙ²)² ≈ (x₁²⋯xₙ²)³",
           "The identities of A₂ᵍ are read off a directed graph of the word together with a parity; the parity "
           "with which a word winds around the cycle x₁ → ⋯ → xₙ → x₁ survives every derivation step with an "
           "identity in fewer variables.",
           "a winding-parity argument on cycle words; that A₂ᵍ has no finite basis is in Lee, Li and Zhang (2012)"),
    13747: ("X y X′ y X ≈ X y X′ y X y X′ y X,  with X = x₁⋯xₙ and X′ its reverse",
            "No derivation step with an identity in fewer variables changes the left side at all.",
            "A. N. Trahtman (1987); M. V. Sapir (1988)"),
}
NAMED = {3842: ("C₈", "the semigroup C₈ of Section 19 of Lee and Zhang (2015)")}

# Proof kinds, by the module of the endpoint theorem; the first matching prefix wins.
# The names follow the glossary "Reading the names" of the repository README.
TRANSFER = ("A semigroup S with a certified basis lies in the variety of this one, {how}, and this "
            "semigroup satisfies the basis of S. Then every identity of this semigroup holds in S and "
            "follows from the basis, so the basis of S is a basis here too.")
KINDS = [
    (("Order6FinalL5TransferV3.", CAS_PREFIX), "transfer from order ≤ 5",
     TRANSFER.format(how="as a subsemigroup; S has order at most five") +
     " This is the final sweep of such transfers."),
    (("research.",), "transfer from order ≤ 5",
     TRANSFER.format(how="as a subsemigroup; S has order at most five") +
     " An earlier wave of such transfers."),
    (("SemigroupBasis.Generated.Order6EmbeddingTransfers",), "embedding transfer",
     TRANSFER.format(how="as a subsemigroup")),
    (("SemigroupBasis.Generated.Order6DivisorTransfers",), "divisor transfer",
     TRANSFER.format(how="as a quotient of a subsemigroup")),
    (("SemigroupBasis.Generated.Order6DirectPower",), "direct-power transfer",
     TRANSFER.format(how="as a subsemigroup of a direct power of this one")),
    (("SemigroupBasis.Generated.Order6Factor",), "subdirect product",
     "This semigroup is a subdirect product of two factors, and the proof combines the bases of the factors."),
    (("SemigroupBasis.Generated.Order6GenericInflation", "SemigroupBasis.Generated.Order6ExactInflation"),
     "inflation", "This semigroup is an inflation of a smaller one, and the proof adapts the basis of that one."),
    (("SemigroupBasis.Generated.Order6Nilpotent.",), "nilpotent certificate",
     "This semigroup is nilpotent: all products of a fixed number of elements are equal to the zero. The "
     "generated certificate lists the identities between short words, and the basis consists of them."),
    (("SemigroupBasis.Generated.Order6Final",), "heavy generated transfer",
     "A transfer of the final sweep that needed a much heavier generated proof than the others."),
    (("SemigroupBasis.Generated.",), "other generated proof",
     "A machine-generated proof that builds on semigroups certified earlier: an adapter or wrapper of a "
     "transfer found by the campaign's search."),
    (("SemigroupBasis.CoRoots.Order6Astra.",), "individual proof",
     "A proof written for this semigroup or a few semigroups, outside the generated and the family proofs."),
    (("SemigroupBasis.CoRoots.",), "family proof",
     "One basis is proved once to derive every identity of every semigroup of a family; on each table only the "
     "identities of the basis are checked, by computation."),
    (("SemigroupBasis.Order6ResidualReleaseV3.",), "wrapper",
     "A thin wrapper that restates a proof made earlier in the development."),
    (("SemigroupBasis.Order6.", "SemigroupBasis.Examples."), "individual proof",
     "A proof written for this semigroup or a few semigroups, outside the generated and the family proofs."),
    (("SemigroupBasis.Nonfinite.",), "no finite basis", "A proof that no finite basis exists."),
]
KIND_NAMES = list(dict.fromkeys(name for _, name, _ in KINDS))
# Short forms for the overview table of the About page.
KIND_SUMMARY = {
    "transfer from order ≤ 5": "S has order at most five and is a subsemigroup of this one (the final sweep of these "
                               "transfers, and earlier waves)",
    "embedding transfer": "S is a subsemigroup of this one",
    "divisor transfer": "S is a quotient of a subsemigroup of this one",
    "direct-power transfer": "S is a subsemigroup of a direct power of this one",
    "subdirect product": "this semigroup is a subdirect product of two factors; the proof combines their bases",
    "inflation": "this semigroup is an inflation of a smaller one; the proof adapts the basis of that one",
    "nilpotent certificate": "all products of a fixed number of elements are equal to the zero; a generated "
                             "certificate lists the identities between short words",
    "heavy generated transfer": "transfers of the final sweep that needed much heavier generated proofs",
    "other generated proof": "generated adapters and wrappers of transfers found by the campaign's search",
    "family proof": "one basis, proved once to derive every identity of every semigroup of a family; on each table "
                    "only the identities of the basis are checked",
    "wrapper": "thin wrappers that restate proofs made earlier",
    "individual proof": "proofs written for one semigroup or a few, among them C₈",
    "no finite basis": "the four proofs that no finite basis exists",
}

LETTERS = list("xyztuvwsrpqabcdefghijklmno")
SUP = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")
TODAY = datetime.date.today().isoformat()
DIGITS = "0123456789abcdefghijklmnopqrstuvwxyz"
ASSET_VERSION = {}       # file name in assets/ -> a hash of its content, appended to its address
# Browsers that support it fetch a page of the site when the pointer rests on a link to it.
SPECULATION = '{"prefetch":[{"where":{"selector_matches":"a[href$=\'.html\']"},"eagerness":"moderate"}]}'


def esc(text):
    return html.escape(str(text), quote=True)


def load(name, folder=DATA):
    with open(os.path.join(folder, name), encoding="utf-8") as handle:
        return json.load(handle)


def plural(n, word, words=None):
    return f"{n:,} {word if n == 1 else (words or word + 's')}"


def verb(n, singular, plural_form):
    return singular if n == 1 else plural_form


def log(message):
    print(message, file=sys.stderr, flush=True)


def b36(n, width):
    out = ""
    for _ in range(width):
        n, digit = divmod(n, 36)
        out = DIGITS[digit] + out
    assert n == 0
    return out


def asset(name, root):
    return f"{root}assets/{name}?v={ASSET_VERSION[name]}"


def bits_hex(numbers):
    return format(sum(1 << (k - 1) for k in numbers), "x")


# ===================================================================== data

catalogue = load("research/order6/catalogue.json", REPO)
TABLE, SELF_DUAL = {}, {}
for record in catalogue["semigroups"]:
    TABLE[record["smallsemi_id"][1]] = record["table"]
    SELF_DUAL[record["smallsemi_id"][1]] = record["self_dual"]
assert sorted(TABLE) == list(range(1, N + 1))

BASIS, BASIS_CLASSES, CLASS_BASIS, CLASS_RECORD = {}, {}, {}, {}
for basis in load("sealed-bases-v1.json")["bases"]:
    BASIS[basis["basis_id"]] = basis["identities"]
    BASIS_CLASSES[basis["basis_id"]] = sorted(int(c["semigroup_id"][3:]) for c in basis["classes"])
    for record in basis["classes"]:
        k = int(record["semigroup_id"][3:])
        CLASS_BASIS[k] = basis["basis_id"]
        CLASS_RECORD[k] = record
assert len(CLASS_BASIS) == N - len(NONFINITE) and not set(CLASS_BASIS) & set(NONFINITE)

REDUCED = load("reduced-forms-v1.json")["forms"]
ORDER = load("order-v2.json")
THEORY_BASES = {t["theory"]: t["bases"] for t in ORDER["theories"]}
BASIS_THEORY = {b: t for t, bases in THEORY_BASES.items() for b in bases}
ROWS = load("census-rows-v1.json")["rows"]
CENSUS_MAP = load("provenance/final-census-map.json", REPO)


def members_of(hexstring):
    value = int(hexstring, 16)          # bit k-1 is set when the basis holds in [6, k]
    return [m + 1 for m in range(N) if (value >> m) & 1]


GENS = {t: sorted(k for b in bases for k in BASIS_CLASSES[b]) for t, bases in THEORY_BASES.items()}
VNAME = {t: GENS[t][0] for t in THEORY_BASES}     # a variety is named after its smallest generator
CLASS_THEORY = {k: BASIS_THEORY[b] for k, b in CLASS_BASIS.items()}
MEMBER_HEX, CONTAINS = {}, {}
for t, bases in THEORY_BASES.items():
    assert len({ROWS[b] for b in bases}) == 1, "equivalent bases with different models"
    MEMBER_HEX[t] = ROWS[bases[0]]
    CONTAINS[t] = members_of(ROWS[bases[0]])
    assert set(GENS[t]) <= set(CONTAINS[t])
IN_VARIETIES = Counter(k for t in THEORY_BASES for k in CONTAINS[t])

UP, DOWN = defaultdict(set), defaultdict(set)
for a, b in ORDER["cover_edges"]:       # theory a derives theory b: the variety of a lies in that of b
    UP[a].add(b)
    DOWN[b].add(a)
    assert set(CONTAINS[a]) <= set(CONTAINS[b])


def size(e):
    return len(e["lhs"]) + len(e["rhs"])


def shortest(t):
    """The reduced form with the fewest identities, then the fewest letters, among the variety's bases."""
    def key(b):
        ids = REDUCED[b]["identities"]
        return (len(ids), sum(size(e) for e in ids), b)
    b = min(THEORY_BASES[t], key=key)
    return b, REDUCED[b]


SHORTEST = {t: shortest(t) for t in THEORY_BASES}

# =============================================================== structure


def properties(table):
    S = range(1, 7)

    def m(a, b):
        return table[a - 1][b - 1]

    idem = [a for a in S if m(a, a) == a]
    zero = next((z for z in S if all(m(z, x) == z == m(x, z) for x in S)), None)
    one = next((e for e in S if all(m(e, x) == x == m(x, e) for x in S)), None)
    comm = all(m(a, b) == m(b, a) for a in S for b in S)
    nil = 0
    if zero is not None:
        power, degree = set(S), 1
        while len(power) > 1:
            following = {m(a, b) for a in power for b in S}
            if following == power:
                break
            power, degree = following, degree + 1
        nil = degree if power == {zero} else 0
    regular = all(any(m(m(a, x), a) == a for x in S) for a in S)
    inverse = regular and all(m(e, f) == m(f, e) for e in idem for f in idem)
    group = one is not None and all(any(m(a, x) == one for x in S) for a in S)

    def generated(gens):
        found = set(gens)
        while True:
            new = {m(a, b) for a in found for b in found} - found
            if not new:
                return found
            found |= new

    rank = next(sub for r in range(1, 7) for sub in itertools.combinations(S, r) if len(generated(sub)) == 6)
    ideals = {frozenset({a} | {m(a, x) for x in S} | {m(x, a) for x in S} | {m(m(x, a), y) for x in S for y in S})
              for a in S}
    return {"idem": idem, "zero": zero, "one": one, "comm": comm, "band": len(idem) == 6, "nil": nil,
            "regular": regular, "inverse": inverse, "group": group, "rank": rank, "jclasses": len(ideals),
            "left_zero": all(m(a, b) == a for a in S for b in S),
            "right_zero": all(m(a, b) == b for a in S for b in S)}


log("properties ...")
PROPS = {k: properties(TABLE[k]) for k in range(1, N + 1)}

log("nearby tables ...")
ARRAY = np.array([sum(TABLE[k], []) for k in range(1, N + 1)], dtype=np.uint8)
NEAR = defaultdict(list)      # k -> [(j, [(row, column), ...])], tables that differ in one or two entries
for i in range(N):
    distance = np.count_nonzero(ARRAY != ARRAY[i], axis=1)
    for j in np.nonzero((distance > 0) & (distance <= 2))[0]:
        cells = [(int(c) // 6 + 1, int(c) % 6 + 1) for c in np.nonzero(ARRAY[i] != ARRAY[j])[0]]
        NEAR[i + 1].append((int(j) + 1, cells))

# ================================================================ Lean code

COMMIT = subprocess.run(["git", "-C", REPO, "rev-parse", "HEAD"], capture_output=True, text=True,
                        check=True).stdout.strip()
IMPORT = re.compile(r"^\s*import\s+(.+)$")
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|public)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|opaque)\s+([^\s:({\[]+)")


def module_files():
    files = {}
    for directory, subdirectories, names in os.walk(REPO):
        subdirectories[:] = [d for d in subdirectories if d not in (".lake", ".git", "scripts")]
        for name in names:
            if name.endswith(".lean") and name != "lakefile.lean":
                path = os.path.relpath(os.path.join(directory, name), REPO)
                files[path[:-5].replace(os.sep, ".")] = path
    return files


def header_imports(text):
    found, in_comment = [], False
    for line in text.split("\n"):
        line = line.strip()
        if in_comment:
            in_comment = "-/" not in line
            continue
        if line.startswith("/-"):
            in_comment = "-/" not in line[2:]
            continue
        if not line or line.startswith("--"):
            continue
        match = IMPORT.match(line)
        if not match:
            break
        found += match.group(1).split()
    return found


log("reading the Lean sources ...")
FILES = module_files()
MODULES = sorted(FILES)
INDEX = {m: i for i, m in enumerate(MODULES)}
LINES = np.zeros(len(MODULES), dtype=np.int64)
GRAPH = {}
for m in MODULES:
    with open(os.path.join(REPO, FILES[m]), encoding="utf-8") as handle:
        text = handle.read()
    LINES[INDEX[m]] = text.count("\n")
    GRAPH[m] = [i for i in header_imports(text[:50000]) if i in FILES]
sys.setrecursionlimit(100000)
_closure = {}


def closure_bits(m):
    if m not in _closure:
        bits = 1 << INDEX[m]
        for i in GRAPH[m]:
            bits |= closure_bits(i)
        _closure[m] = bits
    return _closure[m]


NBYTES = (len(MODULES) + 7) // 8
_size = {}


def closure_mask(m):
    return np.unpackbits(np.frombuffer(closure_bits(m).to_bytes(NBYTES, "little"), dtype=np.uint8),
                         bitorder="little")[:len(MODULES)].astype(bool)


def proof_size(m):
    """The files and lines Lean compiles to check module m: m and everything it imports."""
    if m not in _size:
        mask = closure_mask(m)
        _size[m] = (int(mask.sum()), int(LINES[mask].sum()))
    return _size[m]


_decls = {}


def declarations(path):
    """Map the full name of every declaration of a file to its line, following namespaces and sections."""
    if path not in _decls:
        names, stack = {}, []
        with open(os.path.join(REPO, path), encoding="utf-8") as handle:
            for number, line in enumerate(handle, 1):
                words = line.split()
                if not words:
                    continue
                if words[0] == "namespace" and len(words) > 1:
                    stack.append(words[1].split("."))
                elif "section" in words[:2] or words[0] == "mutual":
                    stack.append([])
                elif words[0] == "end":
                    if stack:
                        stack.pop()
                else:
                    match = DECL.match(line)
                    if match:
                        name = match.group(1)
                        full = name[7:] if name.startswith("_root_.") else \
                            ".".join([part for frame in stack for part in frame] + [name])
                        names.setdefault(full, number)
        _decls[path] = names
    return _decls[path]


def lean_line(path, name):
    names = declarations(path)
    if name in names:
        return names[name]
    tail = name.split(".")
    for n in (3, 2):
        found = [line for full, line in names.items() if full.split(".")[-n:] == tail[-n:]]
        if len(found) == 1:
            return found[0]
    return None


def lean_module(module):
    if module.startswith(CAS_PREFIX):        # removed upstream files, see provenance/README.md
        module = "Order6FinalL5TransferV3." + module[len(CAS_PREFIX):]
    return module


def lean_url(path, line=None):
    return f"{REPO_URL}/blob/{COMMIT}/{path}" + (f"#L{line}" if line else "")


def kind_of(module):
    for prefixes, name, text in KINDS:
        if module.startswith(prefixes):
            return name, text
    raise ValueError(module)


def census_ref(k):
    path = f"SemiBase/Census/Shard{(k - 1) // 150 + 1:03d}.lean"
    return path, lean_line(path, f"SemiBase.Census.S6_{k}")


def catalogue_ref(k):
    path = f"SemiBase/Catalogue/Order6/Part{(k - 1) // 150 + 1:03d}.lean"
    return path, lean_line(path, f"SemiBase.Catalogue.Order6.S6_{k}")


log("locating the theorems ...")
ENDPOINT = {}        # k -> (path, line, theorem name, module as recorded)
for k in range(1, N + 1):
    if k in NONFINITE:
        point = CENSUS_MAP["non_finitely_based"][f"S6_{k}"]
        module, name = point["module"], point["name"]
    else:
        module, name = CLASS_RECORD[k]["module"], CLASS_RECORD[k]["theorem"]
    path = FILES[lean_module(module)]
    ENDPOINT[k] = (path, lean_line(path, name), name, module)
MISSING = [k for k, value in ENDPOINT.items() if value[1] is None]
SIZE = {k: proof_size(lean_module(ENDPOINT[k][3])) for k in range(1, N + 1)}
# Code of its own: the lines of the files that the proof of this class uses and the proof of no other class does.
_classes_of_module = Counter(lean_module(ENDPOINT[k][3]) for k in range(1, N + 1))
_masks = {m: closure_mask(m) for m in _classes_of_module}
_uses = sum(mask.astype(np.int64) * count for m, (mask, count) in
            ((m, (_masks[m], c)) for m, c in _classes_of_module.items()))
OWN = {k: int(LINES[_masks[lean_module(ENDPOINT[k][3])] & (_uses == 1)].sum()) for k in range(1, N + 1)}
KIND = {k: "no finite basis" if k in NONFINITE else kind_of(ENDPOINT[k][3])[0] for k in range(1, N + 1)}

# ============================================================== formatting


def fmt_identity(e):
    names = {}
    for v in e["lhs"] + e["rhs"]:
        names.setdefault(v, LETTERS[len(names)] if len(names) < len(LETTERS) else f"x{len(names)}")

    def word(seq):
        out = []
        for letter, run in itertools.groupby(seq):
            n = len(list(run))
            out.append(names[letter] + (str(n).translate(SUP) if n > 1 else ""))
        return "".join(out)

    return f"{word(e['lhs'])} ≈ {word(e['rhs'])}"


def sorted_identities(ids):
    return sorted(ids, key=lambda e: (len(set(e["lhs"] + e["rhs"])), size(e), e["lhs"], e["rhs"]))


def basis_list(ids):
    ids = sorted_identities(ids)
    cls = "basis cols" if len(ids) > 8 else "basis"
    return f'<ol class="{cls}">' + "".join(f"<li>{esc(fmt_identity(e))}</li>" for e in ids) + "</ol>"


def cayley(table, props, highlight=()):
    head = "<tr><th>·</th>" + "".join(f"<th>{b}</th>" for b in range(1, 7)) + "</tr>"
    body = []
    for a in range(1, 7):
        cells = []
        for b in range(1, 7):
            value = table[a - 1][b - 1]
            cls = ["diff"] if (a, b) in highlight else []
            if props["zero"] is not None and value == props["zero"] and not cls:
                cls.append("zero")
            if a == b and value == a:
                cls.append("idem")
            cells.append(f'<td class="{" ".join(cls)}">{value}</td>' if cls else f"<td>{value}</td>")
        body.append(f"<tr><th>{a}</th>{''.join(cells)}</tr>")
    return f'<table class="cayley">{head}{"".join(body)}</table>'


def slink(k, root="../", named=True):
    name = NONFINITE.get(k, NAMED.get(k, (None,)))[0] if named else None
    label = f"[6, {k}]" + (f" {name}" if name else "")
    cls = ' class="nfb"' if k in NONFINITE else ""
    return f'<a href="{root}s/{k}.html"{cls}>{esc(label)}</a>'


def vlink(t, root="../"):
    return f'<a href="{root}v/{VNAME[t]}.html">V[{VNAME[t]}]</a>'


def blink(b, root="../"):
    return f'<a href="{root}b/{b}.html">{plural(len(BASIS[b]), "identity", "identities")}</a>'


def links(items):
    return f'<div class="links">{" ".join(items)}</div>'


def status_badge(form):
    return ('<span class="badge fb">irredundant</span>' if form["status"] == "irredundant"
            else '<span class="badge plain">reduced</span>')


STATUS_NOTE = {
    "irredundant": "Irredundant: none of these identities follows from the others; for each, a semigroup "
                   "satisfies the others but not it.",
    "candidate_reduced": "Reduced as far as the search went: some identity may still follow from the others.",
}


def page(title, body, root, description="", scripts=()):
    nav = f'<a class="home" href="{root}index.html">Home</a>' + "".join(
        f'<a href="{root}{href}">{label}</a>' for href, label in (
            ("browse.html", "Browse"), ("varieties.html", "Varieties"), ("nonfinite.html", "No finite basis"),
            ("about.html", "About")))
    meta = f'\n<meta name="description" content="{esc(description)}">' if description else ""
    extra = "".join(f'<script src="{asset(s, root)}" defer></script>' for s in scripts)
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(title)}</title>{meta}
<link rel="icon" href="{asset('icon.svg', root)}" type="image/svg+xml">
<link rel="stylesheet" href="{asset('style.css', root)}">
<script type="speculationrules">{SPECULATION}</script></head>
<body><header class="top"><div class="wrap"><a class="brand" href="{root}index.html">SemiBase</a><nav>{nav}</nav>
<form onsubmit="return sbGo(this)" data-root="{root}"><input name="q" placeholder="Semigroup: 3842, L, C8" aria-label="Go to a semigroup"></form></div></header>
<main class="wrap">
{body}
</main>
<footer><div class="wrap">SemiBase: the semigroups of order six and their identity bases. Tables from GAP Smallsemi 0.7.2;
proofs checked by Lean 4 in <a href="{REPO_URL}">nasqret/semibase-order6</a> (commit <span class="mono">{COMMIT[:7]}</span>);
reduced bases and inclusions of varieties computed with Vampire by the <span class="mono">bases-min</span> tools of
M. Janota. Built {TODAY}.</div></footer>
<script src="{asset('site.js', root)}"></script>{extra}</body></html>
"""


def write(path, text):
    full = os.path.join(OUT, path)
    os.makedirs(os.path.dirname(full), exist_ok=True)
    with open(full, "w", encoding="utf-8") as handle:
        handle.write(text)


# ================================================================= pages


def kind_phrase(P):
    """A phrase for the structure of the semigroup, and whether it says more than 'semigroup' or 'monoid'."""
    comm = "commutative " if P["comm"] else ""
    if P["group"]:
        return ("the cyclic group of order six" if P["comm"] else "the symmetric group S₃"), True
    if P["left_zero"]:
        return "a left zero semigroup: xy = x for all x and y", True
    if P["right_zero"]:
        return "a right zero semigroup: xy = y for all x and y", True
    if P["band"]:
        return ("a semilattice: a commutative semigroup in which every element is idempotent" if P["comm"]
                else "a band: every element is idempotent"), True
    if P["nil"] == 2:
        return "a null semigroup: every product is equal to the zero", True
    if P["nil"]:
        return f"a {comm}nilpotent semigroup: every product of {P['nil']} elements is equal to the zero", True
    monoid = P["one"] is not None
    if P["inverse"]:
        return f"a {comm}inverse {'monoid' if monoid else 'semigroup'}", True
    if P["regular"]:
        return f"a {comm}regular {'monoid' if monoid else 'semigroup'}", True
    return f"a {comm}{'monoid' if monoid else 'semigroup'}", False


def describe(k):
    P = PROPS[k]
    if k in NONFINITE:
        return f"[6, {k}] is {NONFINITE[k][1]}, one of the four semigroups of order six without a finite identity basis."
    phrase, special = kind_phrase(P)
    facts = []
    if not (P["band"] or P["group"] or P["nil"]):
        facts.append(plural(len(P["idem"]), "idempotent"))
    if P["zero"] is not None and not P["nil"]:
        facts.append(f"a zero, {P['zero']}")
    if P["one"] is not None and not P["group"]:
        facts.append(f"an identity element, {P['one']}")
    listed = ", ".join(facts[:-1]) + (" and " if len(facts) > 1 else "") + (facts[-1] if facts else "")
    if k in NAMED:
        text = f"[6, {k}] is {NAMED[k][1]}: {phrase}" + (f" with {listed}." if listed else ".")
    elif special:
        text = f"[6, {k}] is {phrase}." + (f" It has {listed}." if listed else "")
    else:
        text = f"[6, {k}] is {phrase}" + (f" with {listed}." if listed else ".")
    t = CLASS_THEORY[k]
    n = len(SHORTEST[t][1]["identities"])
    others = len(GENS[t]) - 1
    text += (f" It is finitely based: {plural(n, 'identity', 'identities')} {verb(n, 'defines', 'define')} its "
             f"variety, which " + (f"{plural(others, 'other semigroup')} of order six also "
                                    f"{verb(others, 'generates', 'generate')}." if others else
                                    "no other semigroup of order six generates."))
    return text


def tags(k):
    P = PROPS[k]
    out = []
    if P["group"]:
        out.append("group")
    elif P["one"] is not None:
        out.append("monoid")
    if P["nil"]:
        out.append(f"nilpotent of class {P['nil']}")
    if P["band"]:
        out.append("band")
    if P["comm"]:
        out.append("commutative")
    if P["inverse"] and not P["group"]:
        out.append("inverse")
    elif P["regular"] and not P["group"]:
        out.append("regular")
    out.append("self-dual" if SELF_DUAL[k] else "not self-dual")
    if k not in NONFINITE:
        out.append(KIND[k])
    return '<div class="tags">' + "".join(f"<span>{esc(t)}</span>" for t in out) + "</div>"


def orientation_note(k):
    return {
        "direct": "The theorem is about the semigroup with exactly this table.",
        "both": "The theorem is about the semigroup with exactly this table.",
        "opposite": "The theorem is about the opposite semigroup, with the transposed table; read backwards, "
                    "its basis is the basis of this table shown above.",
        "relabelled": "The theorem is about a renumbering of this table; the census theorem checks the "
                      "explicit permutation of the elements.",
    }[CLASS_RECORD[k]["proof_orientation"]]


def lean_block(k):
    path, line, name, module = ENDPOINT[k]
    files, lines = SIZE[k]
    spath, sline = census_ref(k)
    cpath, cline = catalogue_ref(k)
    rows = []
    if k in NONFINITE:
        shown = f"theorem {name.split('.')[-1]} {CENSUS_MAP['non_finitely_based'][f'S6_{k}']['statement']}"
    else:
        shown = CLASS_RECORD[k]["checked_type"]
        kind, text = kind_of(module)
        rows.append(("Table", esc(orientation_note(k))))
        rows.append(("Method", f"<b>{esc(kind)}</b>. {esc(text)}"))
    own = (f" Of these, {OWN[k]:,} lines are used by the proof of this class and of no other." if OWN[k] else
           " All of it is shared with the proofs of other classes.")
    rows.append(("Size", f"Checking this class alone compiles {files:,} Lean files with {lines:,} lines: the "
                         f"endpoint theorem and everything it imports, the shared library included.{own}"))
    rows.append(("Census", f'<a href="{lean_url(spath, sline)}" class="mono">SemiBase.Census.S6_{k}</a> checks '
                           f'that the theorem is about the table of this class and concludes '
                           f'<span class="mono">Classified</span>; <a href="{lean_url(cpath, cline)}" class="mono">'
                           f'SemiBase.Catalogue.Order6.S6_{k}</a> is the table, with the elements numbered 0 to 5.'))
    dl = "".join(f"<dt>{label}</dt><dd>{value}</dd>" for label, value in rows)
    return f"""<h2>Lean proof</h2>
<p>Endpoint theorem: <a href="{lean_url(path, line)}" class="mono">{esc(name)}</a></p>
<pre class="lean">{esc(shown)}</pre>
<dl class="props">{dl}</dl>"""


def semigroup_page(k):
    P = PROPS[k]
    name = NONFINITE.get(k, NAMED.get(k, (None,)))[0]
    title = f"[6, {k}]" + (f" {name}" if name else "")
    badge = '<span class="badge nfb">no finite basis</span>' if k in NONFINITE else \
        '<span class="badge fb">finitely based</span>'
    pager = ('<div class="pager">' + (f'<a href="{k - 1}.html">← [6, {k - 1}]</a>' if k > 1 else "<span></span>")
             + (f'<a href="{k + 1}.html">[6, {k + 1}] →</a>' if k < N else "") + "</div>")
    body = [pager, f"<h1>{esc(title)} {badge}</h1>", tags(k), f'<p class="lead">{esc(describe(k))}</p>']

    highlight, diff_note = (), ""
    if k in (3842, 3843):
        other = 3843 if k == 3842 else 3842
        highlight = next(cells for j, cells in NEAR[k] if j == other)
        diff_note = f" Shaded: the two entries in which this table differs from that of {slink(other)}."
    rank = P["rank"]
    props = [
        ("Smallsemi", f'<span class="mono">SmallSemigroup(6, {k})</span>'),
        ("Idempotents", esc(", ".join(map(str, P["idem"])))),
        ("Zero", esc(P["zero"] if P["zero"] is not None else "none")),
        ("Identity", esc(P["one"] if P["one"] is not None else "none")),
        ("Nilpotent", esc(f"yes, of class {P['nil']}" if P["nil"] else "no")),
        ("Commutative", "yes" if P["comm"] else "no"),
        ("Regular", ("yes" + (", inverse" if P["inverse"] else "")) if P["regular"] else "no"),
        ("Group", "yes" if P["group"] else "no"),
        ("𝒥-classes", str(P["jclasses"])),
        ("Rank", esc(f"{len(rank)}, generated by {{{', '.join(map(str, rank))}}}")),
        ("Self-dual", "yes: anti-isomorphic to itself" if SELF_DUAL[k] else
         "no: the class also stands for the opposite semigroup, with the transposed table"),
    ]
    dl = "".join(f"<dt>{label}</dt><dd>{value}</dd>" for label, value in props)
    body.append(f"""<div class="two"><div><h2>Cayley table</h2>{cayley(TABLE[k], P, highlight)}
<p class="note">The product of the row element and the column element, numbered as in Smallsemi. Blue: idempotents
on the diagonal{'; grey: the zero' if P['zero'] is not None else ''}.{diff_note}</p></div>
<div><h2>Structure</h2><dl class="props">{dl}</dl></div></div>""")

    if k in NONFINITE:
        family, argument, source = NONFINITE_DETAIL[k]
        body.append(f"""<h2>No finite identity basis</h2>
<div class="box nfb"><p>For every n, the identity</p><p class="formula">{esc(family)}</p>
<p>holds in {esc(name)}. {esc(argument)} A finite set of identities uses boundedly many variables, so it misses
one of these identities and is not a basis.</p>
<p class="note">Argument: {esc(source)}. That L, B₂¹, A₂ᵍ and A₂¹ are the only semigroups of order six without a
finite basis was shown by Lee, Li and Zhang (2012). See <a href="../nonfinite.html">the four nonfinitely based
semigroups</a>.</p></div>""")
    else:
        t = CLASS_THEORY[k]
        form = SHORTEST[t][1]
        b = CLASS_BASIS[k]
        certified = BASIS[b]
        body.append(f"""<h2>Identity basis</h2>
<div class="box"><p><b>Shortest known basis</b>: {plural(len(form['identities']), 'identity', 'identities')} {status_badge(form)}</p>
{basis_list(form['identities'])}
<p class="note">{STATUS_NOTE[form['status']]} Obtained from a basis certified in Lean by removing identities that
follow from the others, with the prover Vampire; the equivalence rests on Vampire's proofs, not on Lean. Shortest
known, not known to be minimal.</p></div>""")
        if len(certified) <= 20:
            body.append(f"<h3>Basis certified in Lean: {plural(len(certified), 'identity', 'identities')}</h3>"
                        + basis_list(certified))
        else:
            body.append(f"<h3>Basis certified in Lean</h3><p>The Lean theorem certifies a longer basis, of "
                        f"{blink(b)}; the shortest known basis above is equivalent to it.</p>")
    body.append(lean_block(k))

    if k in NONFINITE:
        inside = IN_VARIETIES.get(k, 0)
        body.append(f"""<h2 id="variety">Varieties</h2><p>[6, {k}] generates a variety without a finite basis, so not one of the
505 varieties of this census. """ + (f"It lies in {inside} of them, those whose basis it satisfies.</p>" if inside else
            "It lies in none of them: no finitely based semigroup of order six generates a variety that contains "
            "it, as evaluating their bases in this table shows.</p>"))
    else:
        t = CLASS_THEORY[k]
        up = sorted(UP[t], key=VNAME.get)
        down = sorted(DOWN[t], key=VNAME.get)
        gens = GENS[t]
        others = [g for g in gens if g != k]
        others_text = ("no other semigroup of order six generates it" if not others else
                       f"{plural(len(others), 'other semigroup')} of order six "
                       f"{verb(len(others), 'generates', 'generate')} it too")
        body.append(f"""<h2 id="variety">Variety</h2>
<p>[6, {k}] generates the variety {vlink(t)}; {others_text}, and {plural(len(CONTAINS[t]), 'semigroup')} of order
six {verb(len(CONTAINS[t]), 'lies', 'lie')} in it. [6, {k}] lies in {IN_VARIETIES[k]} of the 505 varieties of the
census, those whose basis it satisfies.</p>
<dl class="props"><dt>Directly above</dt><dd>{links([vlink(u) for u in up]) if up else 'none: a maximal variety of the census'}</dd>
<dt>Directly below</dt><dd>{links([vlink(u) for u in down]) if down else 'none: a minimal variety of the census'}</dd></dl>
<p><a href="../varieties.html#graph={VNAME[t]}&amp;around=2">V[{VNAME[t]}] in the inclusion graph</a>, with the varieties
above and below it.</p>""")
        if others:
            more = (f'<p><a href="../v/{VNAME[t]}.html">All {len(others):,} on the variety page</a></p>'
                    if len(others) > 48 else "")
            body.append(f"<h3>Generating the same variety</h3>{links([slink(g) for g in others[:48]])}{more}")

    near = sorted(NEAR.get(k, []), key=lambda item: (len(item[1]), item[0]))
    if near:
        items = []
        for j, cells in near[:30]:
            where = ", ".join(f"({a}, {b})" for a, b in cells)
            if j in NONFINITE:
                extra = ", no finite basis"
            elif k in CLASS_THEORY and CLASS_THEORY[j] == CLASS_THEORY[k]:
                extra = ", the same variety"
            else:
                extra = f", variety {vlink(CLASS_THEORY[j])}"
            items.append(f"<li>{slink(j)}: {plural(len(cells), 'entry', 'entries')} {where}{extra}</li>")
        more = f'<p class="note">And {len(near) - 30} more.</p>' if len(near) > 30 else ""
        body.append(f"""<h2>Nearby tables</h2><p class="note">Semigroups whose Smallsemi table differs from this one
in one or two entries (row, column), as the tables are listed, not up to renumbering.</p>
<ul class="near">{''.join(items)}</ul>{more}""")
    return page(f"[6, {k}]{' ' + name if name else ''} · SemiBase", "\n".join(body), "../",
                f"The semigroup [6, {k}] of order six: Cayley table, identity basis, Lean proof, variety.")


def hasse(t):
    up = sorted(UP[t], key=VNAME.get)
    down = sorted(DOWN[t], key=VNAME.get)
    shown_up, shown_down = up[:8], down[:8]
    W = max(380, 92 * max(len(shown_up), len(shown_down), 1) + 20)

    def place(items, y):
        return [((i + 0.5) * W / len(items), y, u) for i, u in enumerate(items)]

    top, bottom, mid = place(shown_up, 22), place(shown_down, 162), (W / 2, 92)
    out = [f'<div class="hasse-wrap"><svg class="hasse" width="{W:.0f}" height="186" viewBox="0 0 {W:.0f} 186" '
           f'role="img" aria-label="The varieties directly above and below V[{VNAME[t]}]">']
    for x, y, _ in top + bottom:
        out.append(f'<line x1="{x:.0f}" y1="{y:.0f}" x2="{mid[0]:.0f}" y2="{mid[1]:.0f}"/>')

    def node(x, y, u, own=False):
        label = f"V[{VNAME[u]}]"
        w = 8 * len(label) + 16
        shape = (f'<rect x="{x - w / 2:.0f}" y="{y - 12:.0f}" width="{w}" height="24" rx="5"'
                 f'{" class=\"self\"" if own else ""}/><text x="{x:.0f}" y="{y + 4:.0f}">{label}</text>')
        return shape if own else f'<a href="{VNAME[u]}.html">{shape}</a>'

    out += [node(x, y, u) for x, y, u in top + bottom]
    out.append(node(mid[0], mid[1], t, own=True))
    if len(up) > len(shown_up):
        out.append(f'<text x="{W - 4:.0f}" y="50" class="more">+{len(up) - len(shown_up)} more above</text>')
    if len(down) > len(shown_down):
        out.append(f'<text x="{W - 4:.0f}" y="138" class="more">+{len(down) - len(shown_down)} more below</text>')
    out.append("</svg></div>")
    return "".join(out)


def variety_page(t):
    v = VNAME[t]
    form = SHORTEST[t][1]
    gens, members = GENS[t], CONTAINS[t]
    up = sorted(UP[t], key=VNAME.get)
    down = sorted(DOWN[t], key=VNAME.get)
    certified = "".join(f"<li>{blink(b)}, certified in Lean for {plural(len(BASIS_CLASSES[b]), 'semigroup')}</li>"
                        for b in THEORY_BASES[t])
    nonfinite_in = [k for k in NONFINITE if k in members]
    def name_of(u):
        return f"V[{VNAME[u]}]" if u == t else vlink(u)

    # For each undecided pair (a, b), a semigroup of order six refutes that V(b) lies in V(a); whether V(a) lies
    # in V(b) is open.
    open_ = [f"whether {name_of(a)} lies in {name_of(b)}" for a, b in ORDER["undecided"] if t in (a, b)]
    undecided = (f"<dt>Undecided</dt><dd>{'; '.join(open_)}: no proof was found, and no semigroup of order six "
                 f"refutes it.</dd>") if open_ else ""
    if len(gens) > 150:
        generators = (f'<details data-bits="{bits_hex(gens)}" data-root="../"><summary>Show all {len(gens):,}'
                      f'</summary><div class="links"></div></details>')
    else:
        generators = links([slink(g) for g in gens])
    body = f"""<h1>Variety V[{v}]</h1>
<p class="lead">The variety generated by {slink(v)}: all semigroups that satisfy every identity of [6, {v}].
{plural(len(gens), 'semigroup')} of order six {verb(len(gens), 'generates', 'generate')} it, and
{plural(len(members), 'semigroup')} of order six {verb(len(members), 'lies', 'lie')} in it.</p>
<h2>Shortest known basis</h2><div class="box"><p>{plural(len(form['identities']), 'identity', 'identities')} {status_badge(form)}</p>
{basis_list(form['identities'])}<p class="note">{STATUS_NOTE[form['status']]} Obtained from a certified basis by
removing identities that follow from the others (Vampire). Shortest known, not known to be minimal.</p></div>
<h2>Certified bases</h2><ul>{certified}</ul>
{'<p class="note">The certified bases define the same variety: Vampire derives each from the other.</p>' if len(THEORY_BASES[t]) > 1 else ''}
<h2>Among the 505 varieties</h2>{hasse(t)}
<dl class="props"><dt>Directly above</dt><dd>{links([vlink(u) for u in up]) if up else 'none: a maximal variety of the census'}</dd>
<dt>Directly below</dt><dd>{links([vlink(u) for u in down]) if down else 'none: a minimal variety of the census'}</dd>{undecided}</dl>
<p class="note">A variety lies above another when it contains it. An inclusion holds when the basis of the smaller
variety derives that of the larger one, proved by Vampire; it fails when a semigroup of order six lies in the one
and not in the other.</p>
<p><a href="../varieties.html#graph={v}&amp;around=2">Explore V[{v}] in the inclusion graph</a>, with everything above
and below it.</p>
<h2>Generated by {plural(len(gens), 'semigroup')} of order six</h2>{generators}
<h2>Contains {plural(len(members), 'semigroup')} of order six</h2>
<p class="note">The semigroups of order six that satisfy the basis{'; among them the nonfinitely based ' + ', '.join(slink(k) for k in nonfinite_in) if nonfinite_in else ''}.</p>
<details data-bits="{MEMBER_HEX[t]}" data-root="../"><summary>Show all {len(members):,}</summary><div class="links"></div></details>"""
    return page(f"Variety V[{v}] · SemiBase", body, "../",
                f"The variety generated by the semigroup [6, {v}]: basis, inclusions, generators.")


def basis_page(b):
    t = BASIS_THEORY[b]
    users = BASIS_CLASSES[b]
    form = REDUCED[b]
    body = f"""<h1>A certified basis of {plural(len(BASIS[b]), 'identity', 'identities')}</h1>
<p class="lead">This list of identities is a basis, proved in Lean, of {slink(users[0]) if len(users) == 1 else
plural(len(users), 'semigroup') + ' of order six'}, {'which generates' if len(users) == 1 else 'all of which generate'}
the variety {vlink(t)}. Removing the identities that follow from the others leaves
{plural(len(form['identities']), 'identity', 'identities')} (Vampire); the
<a href="../v/{VNAME[t]}.html">variety page</a> shows the shortest known basis.</p>
<p class="note">Identifier <span class="mono">{esc(b)}</span> in the data of the bases-min seal.</p>
<h2>Certified for</h2>{links([slink(k) for k in users])}
<h2>The identities</h2>{basis_list(BASIS[b])}"""
    return page(f"Certified basis {b} · SemiBase", body, "../")


def browse_page():
    kinds = "".join(f'<option value="{i}">{esc(n)}</option>' for i, n in enumerate(KIND_NAMES))
    yn = '<option value="">any</option><option value="yes">yes</option><option value="no">no</option>'
    body = f"""<h1>Browse the semigroups of order six</h1>
<p class="lead">All 15,973 semigroups of order six up to isomorphism and anti-isomorphism, numbered as in Smallsemi.
Filter them, sort by a column, and open one for its table, basis and proof.</p>
<details class="filterbox" id="filterbox" open><summary>Filters<span id="active"></span></summary>
<div class="filters">
<label>Numbers from <input id="f-from" type="number" min="1" max="15973"></label>
<label>to <input id="f-to" type="number" min="1" max="15973"></label>
<label>Finite basis <select id="f-status"><option value="">any</option><option value="fb">yes</option><option value="nfb">no</option></select></label>
<label>Basis size from <input id="f-bmin" type="number" min="1"></label>
<label>to <input id="f-bmax" type="number" min="1"></label>
<label>Variety V[k] <input id="f-variety" type="number" min="1" max="15973" placeholder="k"></label>
<label>Idempotents <select id="f-idem"><option value="">any</option>{''.join(f'<option>{i}</option>' for i in range(1, 7))}</select></label>
<label>Nilpotent <select id="f-nil">{yn}</select></label>
<label>Monoid <select id="f-monoid">{yn}</select></label>
<label>Commutative <select id="f-comm">{yn}</select></label>
<label>Band <select id="f-band">{yn}</select></label>
<label>Regular <select id="f-regular">{yn}</select></label>
<label>Self-dual <select id="f-selfdual">{yn}</select></label>
<label>Proof <select id="f-kind"><option value="">any</option>{kinds}</select></label>
</div></details>
<div class="listbar"><p id="count" class="muted">Loading …</p><div><button type="button" class="btn colsbtn" data-target="browse-table"
aria-pressed="false">All columns</button> <button id="reset" class="btn" type="button">Reset</button></div></div>
<div class="scroll" id="browse-table"><table class="list"><thead><tr><th class="sort" data-key="id">Semigroup</th>
<th class="sort num" data-key="basis" title="identities in the shortest known basis">Basis</th>
<th class="sort" data-key="variety">Variety</th><th class="sort num opt" data-key="idem">Idemp.</th>
<th class="sort num opt" data-key="nil" title="nilpotency class">Nilp.</th><th class="opt">Monoid</th><th class="opt">Comm.</th>
<th class="opt">Band</th><th class="opt">Self-dual</th><th class="sort" data-key="kind">Proof</th>
<th class="sort num opt" data-key="lines" title="lines of Lean the proof of this class compiles">Lean lines</th></tr></thead>
<tbody id="rows"></tbody></table></div>
<p><button id="more" class="more" type="button" hidden>Show more</button></p>
<p class="note">Basis: identities in the shortest known basis. Lean lines: the lines of Lean that checking the class
alone compiles, shared library included. The filters are kept in the address, so a filtered list can be bookmarked.</p>"""
    return page("Browse · SemiBase", body, "", scripts=("data.js", "browse.js"))


def data_js():
    """The table of browse.html, one string per column with one or more base-36 digits per semigroup."""
    varieties = sorted(VNAME[t] for t in THEORY_BASES)
    position = {v: i for i, v in enumerate(varieties)}
    columns = {name: [] for name in ("basis", "variety", "nil", "idem", "flags", "kind", "lines")}
    for k in range(1, N + 1):
        P = PROPS[k]
        nfb = k in NONFINITE
        length = 0 if nfb else len(SHORTEST[CLASS_THEORY[k]][1]["identities"])
        assert length < 36
        columns["basis"].append(DIGITS[length])
        columns["variety"].append("--" if nfb else b36(position[VNAME[CLASS_THEORY[k]]], 2))
        columns["nil"].append(str(P["nil"]))
        columns["idem"].append(str(len(P["idem"])))
        flags = int(P["one"] is not None) | P["comm"] << 1 | P["band"] << 2 | SELF_DUAL[k] << 3 | P["regular"] << 4
        columns["flags"].append(DIGITS[flags])
        columns["kind"].append(DIGITS[KIND_NAMES.index(KIND[k])])
        columns["lines"].append(b36(SIZE[k][1], 4))
    payload = {"n": N, "kinds": KIND_NAMES, "varieties": varieties}
    payload.update({name: "".join(values) for name, values in columns.items()})
    return "window.SEMIBASE = " + json.dumps(payload, separators=(",", ":"), ensure_ascii=False) + ";\n"


GRAPH_CACHE = os.path.join(DATA, "graph-layout.json")


def radius(t):
    return round(3.5 + 1.3 * math.log(len(GENS[t])), 1)


def graph_layout():
    """Place the varieties, larger ones higher, and route the covering edges, with Graphviz dot.

    The result is kept in data/graph-layout.json with a hash of the input to dot, so that a build without
    Graphviz reuses it as long as the varieties and their order have not changed."""
    lines = ["digraph varieties {",
             "graph [rankdir=TB, ranksep=2.4, nodesep=0.25, splines=spline, newrank=true, mclimit=4, remincross=true];",
             'node [shape=circle, fixedsize=true, label=""];',
             "edge [arrowhead=none, headclip=false, tailclip=false];"]
    lines += [f"v{VNAME[t]} [width={2 * radius(t) / 72:.4f}];" for t in sorted(THEORY_BASES, key=VNAME.get)]
    lines += [f"v{VNAME[b]} -> v{VNAME[a]};" for a, b in ORDER["cover_edges"]]
    source = "\n".join(lines + ["}"]) + "\n"
    key = hashlib.sha256(source.encode()).hexdigest()
    if os.path.exists(GRAPH_CACHE):
        with open(GRAPH_CACHE, encoding="utf-8") as handle:
            cached = json.load(handle)
        if cached.get("key") == key:
            return cached
    try:
        output = subprocess.run(["dot", "-Tjson"], input=source, capture_output=True, text=True, check=True).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"Graphviz (dot) is needed to lay out the graph of the varieties: {error}")
    graph = json.loads(output)
    width, height = (float(v) for v in graph["bb"].split(",")[2:])
    names = {obj["_gvid"]: obj["name"][1:] for obj in graph["objects"]}
    nodes = {}
    for obj in graph["objects"]:
        x, y = map(float, obj["pos"].split(","))
        nodes[obj["name"][1:]] = [round(x, 1), round(height - y, 1)]
    edges = {}
    for edge in graph["edges"]:
        points = [tuple(map(float, p.split(","))) for p in edge["pos"].split() if not p.startswith(("e,", "s,"))]
        assert len(points) % 3 == 1
        coords = [f"{round(x)} {round(height - y)}" for x, y in points]
        upper, lower = names[edge["tail"]], names[edge["head"]]
        edges[f"{lower}-{upper}"] = "M" + coords[0] + "C" + " ".join(coords[1:])
    layout = {"key": key, "width": round(width), "height": round(height), "nodes": nodes, "edges": edges}
    with open(GRAPH_CACHE, "w", encoding="utf-8") as handle:
        json.dump(layout, handle, separators=(",", ":"))
    return layout


def graph_data_js():
    """The data of the inclusion graph: the varieties in the order of their names, the covering edges as
    pairs (lower, upper) with their route, the shortest known bases, and the variety of each semigroup."""
    layout = graph_layout()
    order = sorted(THEORY_BASES, key=VNAME.get)
    index = {t: i for i, t in enumerate(order)}
    nodes = [[VNAME[t], *layout["nodes"][str(VNAME[t])], radius(t), len(GENS[t]), len(CONTAINS[t])] for t in order]
    edges = [[index[a], index[b], layout["edges"][f"{VNAME[a]}-{VNAME[b]}"]] for a, b in ORDER["cover_edges"]]
    bases = [[fmt_identity(e) for e in sorted_identities(SHORTEST[t][1]["identities"])] for t in order]
    cls = "".join(b36(index[CLASS_THEORY[k]], 2) if k in CLASS_THEORY else "--" for k in range(1, N + 1))
    payload = {"width": layout["width"], "height": layout["height"], "nodes": nodes, "edges": edges,
               "bases": bases, "cls": cls, "undecided": [[index[a], index[b]] for a, b in ORDER["undecided"]]}
    return "window.SB_GRAPH = " + json.dumps(payload, separators=(",", ":"), ensure_ascii=False) + ";\n"


def varieties_page():
    maximal = sorted((t for t in THEORY_BASES if not UP[t]), key=lambda t: (-len(CONTAINS[t]), VNAME[t]))
    minimal = sorted((t for t in THEORY_BASES if not DOWN[t]), key=VNAME.get)
    rows = []
    for t in sorted(THEORY_BASES, key=lambda t: (-len(GENS[t]), VNAME[t])):
        ids = SHORTEST[t][1]["identities"]
        first = min(ids, key=lambda e: (size(e), e["lhs"], e["rhs"]))
        rows.append(f"<tr><td>{vlink(t, '')}</td><td class=\"num\">{len(ids)}</td>"
                    f"<td class=\"num\">{len(GENS[t]):,}</td><td class=\"num\">{len(CONTAINS[t]):,}</td>"
                    f"<td class=\"num opt\">{len(UP[t])}</td><td class=\"num opt\">{len(DOWN[t])}</td>"
                    f"<td class=\"mono opt\">{esc(fmt_identity(first))}{' …' if len(ids) > 1 else ''}</td></tr>")
    body = f"""<h1>The 505 varieties</h1>
<p class="lead">The 15,969 finitely based semigroups of order six generate 505 distinct varieties. V[k] is the variety
generated by [6, k], with k the smallest number among its generators. Ordered by inclusion, they have
{len(ORDER['cover_edges']):,} covering pairs, {len(maximal)} maximal and {len(minimal)} minimal varieties;
{len(ORDER['undecided'])} inclusions are undecided.</p>
<div class="tabs" role="tablist"><a href="#list" role="tab" aria-selected="true">List</a><a href="#graph" role="tab"
aria-selected="false">Inclusion graph</a></div>
<noscript><p class="note">The inclusion graph needs JavaScript; the list below has the same information.</p></noscript>
<section id="graph-view" hidden>
<div class="graph" id="graph" data-src="{asset('graph-data.js', '')}">
<div class="bar">
<form><input type="search" placeholder="Find V[k] or a semigroup [6, k]" aria-label="Find a variety, or the variety of a semigroup"><button class="btn" type="submit">Find</button></form>
<div class="group" role="group" aria-label="View"><button type="button" class="btn" id="g-all" aria-pressed="true">Whole order</button><button type="button" class="btn" id="g-around" aria-pressed="false" disabled>Around selection</button><select id="g-steps" aria-label="Steps around the selection" disabled><option value="1">1 step</option><option value="2" selected>2 steps</option><option value="3">3 steps</option><option value="0">all</option></select></div>
<div class="group" role="group" aria-label="Zoom"><button type="button" class="btn" id="g-out" aria-label="Zoom out">−</button><button type="button" class="btn" id="g-in" aria-label="Zoom in">+</button><button type="button" class="btn" id="g-fit">Fit</button><button type="button" class="btn" id="g-full" aria-pressed="false">Full screen</button></div>
</div>
<div class="stage"><div class="view"><canvas tabindex="0" role="img" aria-label="The inclusion graph of the 505 varieties. The List tab has the same information as text."></canvas><div class="msg" aria-live="polite"></div><div class="tip" hidden></div></div><div class="info" hidden></div></div>
<div class="legend"><span><i style="background:var(--accent)"></i>selected</span><span><i style="background:var(--good)"></i>above: contains it</span><span><i style="background:var(--warn)"></i>below: lies in it</span><span><i class="dash"></i>undecided</span><span>larger dots: more generators</span></div>
</div>
<p class="note">Each dot is a variety, drawn below the varieties that contain it; a line joins it to each variety
directly above it. Select a variety to see everything above and below it, and choose "Around selection" to lay out
only those, up to a number of steps. The address keeps the selection, so a view can be bookmarked or shared. Layout:
Graphviz.</p>
</section>
<section id="list-view">
<h2>Maximal varieties ({len(maximal)})</h2><p class="note">Contained in no other variety of the census, the largest
first; start here and go down.</p>{links([vlink(t, '') for t in maximal])}
<h2>Minimal varieties ({len(minimal)})</h2>{links([vlink(t, '') for t in minimal])}
<h2>All varieties</h2><p class="note">Sorted by the number of generators; click a column to sort. Basis: identities in
the shortest known basis, of which the shortest is shown. Contains: semigroups of order six in the variety. Above,
below: the covering varieties.</p>
<div class="listbar"><span></span><button type="button" class="btn colsbtn" data-target="varieties-table" aria-pressed="false">All columns</button></div>
<div class="scroll" id="varieties-table"><table class="list sortable"><thead><tr><th>Variety</th><th class="num">Basis</th><th class="num">Generators</th>
<th class="num">Contains</th><th class="num opt">Above</th><th class="num opt">Below</th><th class="opt">Shortest identity</th></tr></thead>
<tbody>{''.join(rows)}</tbody></table></div>
</section>"""
    return page("Varieties · SemiBase", body, "", scripts=("graph.js",))


def nonfinite_page():
    sections = []
    for k in (3843, 8564, 8878, 13747):
        name, words = NONFINITE[k]
        family, argument, source = NONFINITE_DETAIL[k]
        path, line, theorem, _ = ENDPOINT[k]
        sections.append(f"""<h2>{esc(name)} = {slink(k, '', named=False)}</h2><div class="two"><div>{cayley(TABLE[k], PROPS[k])}</div>
<div><p>{esc(words[0].upper() + words[1:])}. For every n,</p><p class="formula">{esc(family)}</p><p>{esc(argument)}</p>
<p class="note">{esc(source[0].upper() + source[1:])}. Lean: <a href="{lean_url(path, line)}" class="mono">{esc(theorem)}</a></p></div></div>""")
    body = f"""<h1>The four semigroups without a finite basis</h1>
<p class="lead">Every semigroup of order six has a finite identity basis except four: L, B₂¹, A₂ᵍ and A₂¹ (Lee, Li and
Zhang 2012). Each Lean proof exhibits infinitely many identities of the semigroup, one for every n, and a property of
words that separates the two sides of the n-th identity and survives every derivation step with an identity in fewer
than n variables. So no finite set of identities derives them all. None of the four lies in any of the 505 varieties
generated by the finitely based semigroups of order six.</p>
{''.join(sections)}"""
    return page("No finite basis · SemiBase", body, "")


def index_page():
    sizes = Counter(len(SHORTEST[CLASS_THEORY[k]][1]["identities"]) for k in CLASS_THEORY)
    peak = max(sizes.values())
    bars = "".join(f'<span class="lab">{s}</span><div><div class="bar" style="width:{100 * c / peak:.1f}%"></div></div>'
                   f'<span class="lab">{c:,}</span>' for s, c in sorted(sizes.items()))
    biggest = max(range(1, N + 1), key=lambda k: OWN[k])
    longest = max(CLASS_THEORY, key=lambda k: (len(BASIS[CLASS_BASIS[k]]), -k))
    longest_short = max(THEORY_BASES, key=lambda t: (len(SHORTEST[t][1]["identities"]), -VNAME[t]))
    widest = max(THEORY_BASES, key=lambda t: (len(GENS[t]), -VNAME[t]))
    body = f"""<h1>Identity bases of the semigroups of order six</h1>
<p class="lead">A census of the 15,973 semigroups of order six, counted up to isomorphism and anti-isomorphism. All of
them except four have a finite identity basis, and every case is proved in Lean: an explicit basis for each of the
15,969 finitely based semigroups, for most of which only the existence of a finite basis was known before, and a
proof for the other four that no finite basis exists.</p>
<form class="big" onsubmit="return sbGo(this)" data-root=""><input name="q" placeholder="Go to a semigroup: 3842, [6, 3842], L, B21, C8" aria-label="Go to a semigroup"></form>
<div class="numbers"><div><b>15,973</b><span>semigroups of order six</span></div>
<div><b>15,969</b><span>finitely based, each with a basis certified in Lean</span></div>
<div><b>4</b><span>without a finite basis, proved in Lean</span></div>
<div><b>536</b><span>distinct certified bases</span></div>
<div><b>505</b><span>distinct varieties</span></div></div>
<h2>Explore</h2>
<ul class="explore">
<li><a href="browse.html">Browse</a> all 15,973 semigroups and filter them by structure, basis and proof.</li>
<li><a href="varieties.html">Varieties</a>: the 505 varieties the semigroups generate, as a list or as an
<a href="varieties.html#graph">interactive graph of their inclusions</a>.</li>
<li><a href="nonfinite.html">No finite basis</a>: L, B₂¹, A₂ᵍ and A₂¹, and why no finite set of identities suffices.</li>
<li><a href="s/1.html" onclick="return sbRandom('')">A random semigroup</a>.</li>
</ul>
<h2>Worth a look</h2>
<ul class="explore">
<li>{slink(3842, '')}, the semigroup C₈ of Lee and Zhang: finitely based, two table entries away from the nonfinitely based L.</li>
<li>{slink(biggest, '')}: the largest proof, {OWN[biggest]:,} lines of Lean that the proof of no other class uses.</li>
<li>{slink(longest, '')}: the longest certified basis, {len(BASIS[CLASS_BASIS[longest]]):,} identities, which reduce to {len(SHORTEST[CLASS_THEORY[longest]][1]['identities'])}.</li>
<li>{vlink(longest_short, '')}: the variety whose shortest known basis is longest, with {len(SHORTEST[longest_short][1]['identities'])} identities.</li>
<li>{vlink(widest, '')}: the variety with the most generators, {len(GENS[widest]):,} semigroups of order six.</li>
</ul>
<h2>How short are the bases?</h2>
<p class="note">The finitely based semigroups by the number of identities in their shortest known basis.</p>
<div class="bars">{bars}</div>
<h2>On each page</h2>
<p>For each semigroup: the Cayley table and its structure; the shortest known basis and the basis certified in Lean;
the Lean theorem, linked to its line, and the size of its proof; the variety it generates, with the varieties directly
above and below and the other semigroups that generate it; and the tables that differ from it in one or two entries.
<a href="about.html">About</a> says what is proved in Lean and what is not.</p>"""
    return page("SemiBase: identity bases of the semigroups of order six", body, "",
                "Every semigroup of order six with its identity basis, Lean proof and variety.")


def about_page():
    counts = Counter(KIND.values())
    kinds = "".join(f"<tr><td>{esc(name)}</td><td class=\"num\">{counts[name]:,}</td><td>{esc(KIND_SUMMARY[name])}</td></tr>"
                    for name in KIND_NAMES if counts[name])
    body = f"""<h1>About the census</h1>
<h2>What is proved in Lean</h2>
<p>For each of the 15,973 semigroups of order six in GAP Smallsemi 0.7.2, a theorem: either a finite list of
identities is a basis, that is, the identities hold and every identity of the semigroup follows from them by
equational logic, or no finite basis exists. One theorem collects them all,
<span class="mono">SemiBase.order6_classification</span>. The Lean kernel checks every proof, and the proofs use no
axioms beyond propositional extensionality, quotient soundness and choice. Sources, build instructions and the checks
of the tables: <a href="{REPO_URL}">nasqret/semibase-order6</a>, archived on Zenodo as
<a href="https://doi.org/10.5281/zenodo.23109225">doi:10.5281/zenodo.23109225</a>.</p>
<h2>What is not proved in Lean</h2>
<ul><li>The shortest known bases come from the certified ones by removing identities that follow from the others, with
the prover Vampire; their equivalence with the certified bases rests on Vampire's proofs. Shortest known means
shortest found, not proved minimal.</li>
<li>The inclusions between the varieties are proved by Vampire, and the non-inclusions by semigroups of order six that
lie in one variety and not in the other. {len(ORDER['undecided'])} inclusions are undecided.</li>
<li>That Smallsemi lists every semigroup of order six once, up to isomorphism and anti-isomorphism, is taken from GAP
and the literature.</li></ul>
<h2>What was known</h2>
<p>That exactly four semigroups of order six are not finitely based was shown by Lee, Li and Zhang (2012), and Lee and
Zhang (2015) treat the semigroups of order six in detail. For most of the finitely based ones, 14,534 of the 14,600
semigroups without an identity element, finite basability follows there from sufficient conditions, which show that a
finite basis exists without writing one down. The census gives an explicit basis for every one of them.</p>
<h2>How the proofs work</h2>
<p>Most proofs are transfers. If a semigroup S with a certified basis lies in the variety of a semigroup T, and T
satisfies the basis of S, then every identity of T holds in S and so follows from the basis: the basis of S is a basis
of T. The transfers differ in how S lies in the variety of T. Each semigroup page names the method of its proof.</p>
<div class="scroll"><table class="list"><thead><tr><th>Proof</th><th class="num">Classes</th><th>Idea</th></tr></thead><tbody>{kinds}</tbody></table></div>
<h2>Conventions</h2>
<p>Elements are numbered 1 to 6 as in Smallsemi (0 to 5 in Lean), and a table gives the product of the row element and
the column element. An identity u ≈ v is written with the variables x, y, z, t, … in order of first occurrence and with
powers for repeated letters, so x²yx stands for xxyx. V[k] is the variety generated by [6, k], with k the smallest
number among its generators. A class that is not self-dual stands for two semigroups, a table and its transpose; a basis
read backwards is a basis of the transpose. The links to Lean point to commit <span class="mono">{COMMIT[:7]}</span>
of the repository.</p>
<h2>Credits</h2>
<p>Created and curated by <a href="https://github.com/nasqret">@nasqret</a>. The Lean proofs were written by
language-model agents in a campaign from June to September 2026, described in <i>{esc(PAPER)}</i>. The reduced bases
and the order of the varieties were computed with Vampire by the <span class="mono">bases-min</span> tools of Mikoláš
Janota. The tables come from GAP Smallsemi by A. Distler and J. D. Mitchell. The source of this website is
<a href="https://github.com/nasqret/semibase-site">nasqret/semibase-site</a>.</p>
<h2>References</h2><ul class="refs">
<li>A. Distler and J. D. Mitchell, Smallsemi, a library of small semigroups, GAP package, version 0.7.2.</li>
<li>E. W. H. Lee, J. R. Li and W. T. Zhang, Minimal non-finitely based semigroups, Semigroup Forum 85 (2012) 577–580.</li>
<li>E. W. H. Lee and W. T. Zhang, Finite basis problem for semigroups of order six, LMS J. Comput. Math. 18 (2015) 1–129.</li>
<li>P. Perkins, Bases for equational theories of semigroups, J. Algebra 11 (1969) 298–314.</li>
<li>M. V. Sapir, Problems of Burnside type and the finite basis property in varieties of semigroups, Math. USSR-Izv. 30 (1988) 295–314.</li>
<li>A. N. Trahtman, Some finite infinitely basable semigroups, Ural. Gos. Univ. Mat. Zap. 14 (1987) 128–131.</li>
<li>M. V. Volkov, The finite basis problem for finite semigroups, Sci. Math. Jpn. 53 (2001) 171–199.</li>
<li>W. T. Zhang and Y. F. Luo, A new example of a minimal nonfinitely based semigroup, Bull. Aust. Math. Soc. 84 (2011) 484–491.</li></ul>
<p class="note">Built {TODAY} from commit <span class="mono">{COMMIT}</span>.</p>"""
    return page("About · SemiBase", body, "")


def main():
    if os.path.exists(OUT):
        shutil.rmtree(OUT)
    os.makedirs(os.path.join(OUT, "assets"))
    log("assets ...")
    for name in ("style.css", "browse.js", "graph.js", "icon.svg"):
        shutil.copy(os.path.join(HERE, "assets", name), os.path.join(OUT, "assets", name))
    with open(os.path.join(HERE, "assets", "site.js"), encoding="utf-8") as handle:
        site_js = handle.read()
    assert "/*VARIETIES*/[]" in site_js
    write("assets/site.js", site_js.replace("/*VARIETIES*/[]", json.dumps(sorted(VNAME.values()), separators=(",", ":"))))
    write("assets/data.js", data_js())
    write("assets/graph-data.js", graph_data_js())
    for name in sorted(os.listdir(os.path.join(OUT, "assets"))):
        with open(os.path.join(OUT, "assets", name), "rb") as handle:
            ASSET_VERSION[name] = hashlib.sha256(handle.read()).hexdigest()[:10]
    log("pages ...")
    for k in range(1, N + 1):
        write(f"s/{k}.html", semigroup_page(k))
    for t in THEORY_BASES:
        write(f"v/{VNAME[t]}.html", variety_page(t))
    for b in BASIS:
        write(f"b/{b}.html", basis_page(b))
    write("index.html", index_page())
    write("browse.html", browse_page())
    write("varieties.html", varieties_page())
    write("nonfinite.html", nonfinite_page())
    write("about.html", about_page())
    missing_census = [k for k in range(1, N + 1) if census_ref(k)[1] is None or catalogue_ref(k)[1] is None]
    print(f"{N} semigroup pages, {len(THEORY_BASES)} variety pages, {len(BASIS)} basis pages")
    print(f"endpoint lines not found: {len(MISSING)} {MISSING[:10]}; census lines not found: {len(missing_census)}")


if __name__ == "__main__":
    main()
