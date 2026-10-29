#!/usr/bin/env python3
"""Build the SemiBase census: a static website about the semigroups of orders one to six and their identity bases.

One page per semigroup (site/s/<k>.html for [6, k], site/s/<n>-<k>.html for [n, k] with n at most five) with its
Cayley table, its structure, its bases or the proof that none is finite, its Lean theorem, the variety it generates
and related semigroups; one page per variety (site/v/<name>.html), counting a variety and its dual separately; one
page per certified basis (site/b/<id>.html); the rule that names the varieties (site/names.html), with the frozen
list of names (site/names-v1.json); and overview pages. The site is plain HTML with a little JavaScript, and works
when opened from disk.

The data comes from census.py (classes, bases, the pool of tables and its rows, the varieties and their order) and
from data/: the bases reduced by Vampire, the bases in few variables found by prep/fewvars.py, the lower bounds of
prep/variable_bounds.py, the names of the database of Araújo et al., and data/variety-names-v1.json, which fixes the
names of the varieties: the build stops if the data ever give a different name. The Lean sources of a checkout of
semibase-order6 (SEMIBASE_REPO, default ../semibase-order6) give the line of every theorem and the code each proof
needs, and its commit is the one the Lean links point to.

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

import census as C
from census import (CLASSES, CLASS_BASIS, CLASS_VAR, CLASS_VAR_OP, COUNT, BASIS, BASIS_CLASSES, LOWER, MODELS,
                    NONFINITE, NV, REDUCED, SELF_DUAL, TABLE, VARIETIES, UP, DOWN, canonical_basis, nvars, oriented,
                    reverse, size, load, log)

HERE = C.HERE
DATA = C.DATA

# The names of the varieties are fixed (names.html): the data must give exactly the names of version 1.
with open(os.path.join(DATA, "variety-names-v1.json"), "rb") as _handle:
    NAMES_BYTES = _handle.read()
NAMES_SHA = hashlib.sha256(NAMES_BYTES).hexdigest()
REGISTRY = json.loads(NAMES_BYTES)
for _key, _value in C.name_registry().items():
    assert REGISTRY[_key] == _value, f"the names differ from data/variety-names-v1.json in {_key!r}; names are fixed"
NAME_INDEX = {e["slug"]: i for i, e in enumerate(C.NAMES)}
OUT = os.path.join(HERE, "site")
REPO = C.REPO
REPO_URL = "https://github.com/nasqret/semibase-order6"
SITE_URL = "https://github.com/nasqret/semibase-site"
DOI = "10.5281/zenodo.23109225"
SGV_URL = "https://www.sgv.dm.fct.unl.pt/"
PAPER = "Proving at Scale for Universal Algebra, MATH-AI workshop, NeurIPS 2026"
N6 = COUNT[6]
NLOW = sum(COUNT[n] for n in range(1, 6))
CAS_PREFIX = "SemigroupBasis.Generated.Order6CASExplicitSourceUpstream."

NONFINITE_NAMES = {
    3843: ("L", "Lee's semigroup L"),
    8564: ("B₂¹", "the Brandt monoid B₂¹, obtained from B₂ by adjoining an identity"),
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
NAMED = {
    (6, 3842): ("C₈", "the semigroup C₈ of Section 19 of Lee and Zhang (2015)"),
    (5, 415): ("B₂", "the Brandt semigroup B₂; adjoining an identity gives B₂¹, which has no finite basis"),
    (5, 868): ("A₂", "the semigroup A₂; adjoining an identity gives A₂¹, which has no finite basis"),
}
for _k, (_short, _long) in NONFINITE_NAMES.items():
    NAMED[(6, _k)] = (_short, _long)
SEARCH_NAMES = {"l": "3843", "b21": "8564", "b2^1": "8564", "a2g": "8878", "a2^g": "8878", "a21": "13747",
                "a2^1": "13747", "c8": "3842", "b2": "5-415", "a2": "5-868"}

# Proof kinds of order six, by the module of the endpoint theorem; the first matching prefix wins.
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
LOWER_KINDS = {
    "transfer": TRANSFER.format(how="as a subsemigroup, a quotient, or in a direct power of this one"),
    "inflation": "This semigroup is an inflation of a smaller one, and the proof adapts the basis of that one.",
    "family proof": "One basis is proved once to derive every identity of every semigroup of a family; on each "
                    "table only the identities of the basis are checked, by computation.",
    "direct proof": "A proof for this semigroup alone, or generated for it, that derives every identity of the "
                    "semigroup from the basis.",
}
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
    "transfer": "S, another semigroup of order at most five, lies in the variety of this one and the basis of S holds "
                "here",
    "direct proof": "a proof for this semigroup alone, or generated for it",
}

LETTERS = list("xyztuvwsrpqabcdefghijklmno")
SUP = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")
DIGITS = "0123456789abcdefghijklmnopqrstuvwxyz"
OP = "ᵒᵖ"
ASSET_VERSION = {}       # file name in assets/ -> a hash of its content, appended to its address
SPECULATION = '{"prefetch":[{"where":{"selector_matches":"a[href$=\'.html\']"},"eagerness":"moderate"}]}'
ORDER_WORD = {1: "one", 2: "two", 3: "three", 4: "four", 5: "five", 6: "six"}


def git_out(*args, cwd=HERE):
    try:
        return subprocess.run(["git", "-C", cwd, *args], capture_output=True, text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return ""


# The build date is the date of the commit of this repository, so that a build of a commit is the same everywhere.
SITE_COMMIT = git_out("rev-parse", "HEAD")
TODAY = git_out("log", "-1", "--format=%cs") or datetime.date.today().isoformat()


def esc(text):
    return html.escape(str(text), quote=True)


def plural(n, word, words=None):
    return f"{n:,} {word if n == 1 else (words or word + 's')}"


def verb(n, singular, plural_form):
    return singular if n == 1 else plural_form


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


# ===================================================================== names and links


def sslug(key):
    n, k = key
    return str(k) if n == 6 else f"{n}-{k}"


def slabel(n, k, o=0):
    return f"[{n}, {k}]" + (OP if o else "")


def slink(key, root="../", o=0, named=True):
    n, k = key
    name = NAMED.get(key, (None,))[0] if named and not o else None
    label = slabel(n, k, o) + (f" {name}" if name else "")
    cls = ' class="nfb"' if n == 6 and k in NONFINITE else ""
    return f'<a href="{root}s/{sslug(key)}.html"{cls}>{esc(label)}</a>'


def sglink(s, root="../"):
    """A link to a semigroup up to isomorphism: a table, or the transpose of a class that is not self-dual."""
    return slink(s[:2], root, o=s[2])


def vlabel(v):
    return VARIETIES[v]["label"]


def vlink(v, root="../"):
    return f'<a href="{root}v/{VARIETIES[v]["slug"]}.html">{esc(vlabel(v))}</a>'


def nlink(k, root="../"):
    """A link to the variety of the nonfinitely based class [6, k], which is not among VARIETIES."""
    return f'<a href="{root}v/{k}.html" class="nfb">V[6, {k}]</a>'


def name_link(e, root="../"):
    """A link to the variety of an entry of census.NAMES."""
    return vlink(e["variety"], root) if e["finite"] else nlink(e["model"][1], root)


def blink(b, root="../"):
    return f'<a href="{root}b/{b}.html">{plural(len(BASIS[b]), "identity", "identities")}</a>'


def links(items):
    return f'<div class="links">{" ".join(items)}</div>'


def sets_attr(semigroups):
    """A list of semigroups as bit sets, one per order and orientation, for site.js to draw when opened."""
    groups = defaultdict(list)
    for n, k, o in semigroups:
        groups[(n, o)].append(k)
    return " ".join(f"{n}:{o}:{bits_hex(ks)}" for (n, o), ks in sorted(groups.items(), key=lambda x: (-x[0][0], x[0][1])))


def semigroup_list(semigroups, root="../", inline=150):
    if len(semigroups) <= inline:
        return links([sglink(s, root) for s in semigroups])
    return (f'<details data-sets="{sets_attr(semigroups)}" data-root="{root}"><summary>Show all {len(semigroups):,}'
            f'</summary><div class="links"></div></details>')


def by_order(semigroups):
    counts = Counter(s[0] for s in semigroups)
    return ", ".join(f"{counts[n]:,} of order {n}" for n in sorted(counts, reverse=True))


# ===================================================================== bases of the varieties

log("bases of the varieties ...")
FEW = load("few-variables-v1.json")["results"] if os.path.exists(os.path.join(DATA, "few-variables-v1.json")) else []
FEW_BY = defaultdict(list)
for result in FEW:
    FEW_BY[result["variety"]].append(result)
BOUNDS = {b["variety"]: b for b in load("variable-bounds-v1.json")["bounds"]}
SGV = {}
for entry in load("sgv-names-v1.json")["names"]:
    SGV[C.MODEL_VAR[C.LABELS.index(entry["generator"])]] = entry


def candidates(v):
    """Every known basis of V_v: the certified ones, their reduced forms, and the results of the search."""
    found = {}

    def add(kind, ids, **info):
        key = canonical_basis(ids)
        if key not in found:
            found[key] = dict(kind=kind, identities=ids, **info)

    for i in VARIETIES[v]["gens"]:
        n, k, o = MODELS[i]
        b = CLASS_BASIS[(n, k)]
        add("certified", oriented(BASIS[b], o), basis=b, orientation=o)
        if b in REDUCED:
            add("reduced", oriented(REDUCED[b]["identities"], o), basis=b, orientation=o,
                status=REDUCED[b]["status"])
    var, dual = VARIETIES[v], VARIETIES[VARIETIES[v]["dual"]]
    for source, flip in ((var, 0), (dual, 1)):
        for result in FEW_BY.get(source["slug"], []):
            if result["kind"] not in ("search", "reduce"):
                continue
            derives = dict(result["derives"])
            derives["orientation"] ^= flip
            add(result["kind"], oriented(result["basis"], flip), derives=derives, method=result.get("method"))
    return list(found.values())


def total(ids):
    return sum(size(e) for e in ids)


CANDIDATES = {v: candidates(v) for v in range(NV)}
FEWEST_IDS = {v: min(CANDIDATES[v], key=lambda c: (len(c["identities"]), total(c["identities"]),
                                                   nvars(c["identities"]))) for v in range(NV)}
FEWEST_VARS = {v: min(CANDIDATES[v], key=lambda c: (nvars(c["identities"]), len(c["identities"]),
                                                    total(c["identities"]))) for v in range(NV)}
# Lower bounds on the number of variables: a table of the pool (prep/variable_bounds.py), or a larger semigroup
# found by Vampire's model builder (prep/fewvars.py, mode refute), whichever bound is higher.
BOUND_INFO = {v: dict(BOUNDS[VARIETIES[v]["slug"]]) for v in range(NV)}
_cm_path = os.path.join(DATA, "countermodels-v1.json")
for entry in (load("countermodels-v1.json")["models"] if os.path.exists(_cm_path) else []):
    v = C.SLUG[entry["variety"]]
    for w, flip in ((v, False), (VARIETIES[v]["dual"], True)):
        model = [list(row) for row in zip(*entry["table"])] if flip else entry["table"]
        violates = reverse(entry["violates"]) if flip else entry["violates"]
        if entry["k"] + 1 > BOUND_INFO[w]["lower_bound"]:
            BOUND_INFO[w] = {"variety": VARIETIES[w]["slug"], "lower_bound": entry["k"] + 1, "k": entry["k"],
                             "model": model, "violates": violates}
LOWER_BOUND = {v: BOUND_INFO[v]["lower_bound"] for v in range(NV)}
OPTIMAL = {v: LOWER_BOUND[v] == nvars(FEWEST_VARS[v]["identities"]) for v in range(NV)}
for v in range(NV):
    assert LOWER_BOUND[v] <= nvars(FEWEST_VARS[v]["identities"]), VARIETIES[v]["slug"]
GENS = {v: C.generators(v) for v in range(NV)}
MEMBERS = {v: C.members(v) for v in range(NV)}
IN_VARIETIES = Counter()
for v in range(NV):
    for s in MEMBERS[v]:
        IN_VARIETIES[s] += 1
# The names the varieties had when the census listed only the representatives of order six.
OLD_NAME = {}
for v in range(NV):
    reps = [MODELS[i][1] for i in VARIETIES[v]["gens"] if MODELS[i][0] == 6 and MODELS[i][2] == 0]
    if reps:
        OLD_NAME[v] = min(reps)
MOVED = {OLD_NAME[v]: v for v in OLD_NAME if VARIETIES[v]["slug"] != str(OLD_NAME[v])}

# =============================================================== structure


def properties(table):
    n = len(table)
    S = range(1, n + 1)

    def m(a, b):
        return table[a - 1][b - 1]

    idem = [a for a in S if m(a, a) == a]
    zero = next((z for z in S if all(m(z, x) == z == m(x, z) for x in S)), None)
    one = next((e for e in S if all(m(e, x) == x == m(x, e) for x in S)), None)
    comm = all(m(a, b) == m(b, a) for a in S for b in S)
    nil = 0
    if zero is not None and n > 1:
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

    rank = next(sub for r in range(1, n + 1) for sub in itertools.combinations(S, r) if len(generated(sub)) == n)
    ideals = {frozenset({a} | {m(a, x) for x in S} | {m(x, a) for x in S} | {m(m(x, a), y) for x in S for y in S})
              for a in S}
    cyclic = group and any(len(generated((a,))) == n for a in S)
    return {"n": n, "idem": idem, "zero": zero, "one": one, "comm": comm, "band": len(idem) == n, "nil": nil,
            "regular": regular, "inverse": inverse, "group": group, "cyclic": cyclic, "rank": rank,
            "jclasses": len(ideals), "left_zero": all(m(a, b) == a for a in S for b in S),
            "right_zero": all(m(a, b) == b for a in S for b in S)}


log("properties ...")
PROPS = {key: properties(TABLE[key]) for key in CLASSES}

log("nearby tables ...")
NEAR = defaultdict(list)      # key -> [(other key, [(row, column), ...])]: tables that differ in one or two entries
for n in C.ORDERS:
    keys = [(n, k) for k in range(1, COUNT[n] + 1)]
    array = np.array([sum(TABLE[key], []) for key in keys], dtype=np.uint8)
    for i in range(len(keys)):
        distance = np.count_nonzero(array != array[i], axis=1)
        for j in np.nonzero((distance > 0) & (distance <= 2))[0]:
            cells = [(int(c) // n + 1, int(c) % n + 1) for c in np.nonzero(array[i] != array[j])[0]]
            NEAR[keys[i]].append((keys[int(j)], cells))

# ================================================================ Lean code

COMMIT = git_out("rev-parse", "HEAD", cwd=REPO)
assert COMMIT, f"no git checkout of semibase-order6 at {REPO}"
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
FILE_SHA = {}
for m in MODULES:
    with open(os.path.join(REPO, FILES[m]), "rb") as handle:
        raw = handle.read()
    FILE_SHA[FILES[m]] = hashlib.sha256(raw).hexdigest()
    text = raw.decode("utf-8")
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


def lower_kind(module):
    tail = module.split(".")[-1]
    if "Inflation" in tail:
        return "inflation"
    if "Transfers" in tail or "Extensions" in tail:
        return "transfer"
    if module.startswith("SemigroupBasis.CoRoots.") or "Family" in tail:
        return "family proof"
    return "direct proof"


def census_ref(k):
    path = f"SemiBase/Census/Shard{(k - 1) // 150 + 1:03d}.lean"
    return path, lean_line(path, f"SemiBase.Census.S6_{k}")


def catalogue_ref(k):
    path = f"SemiBase/Catalogue/Order6/Part{(k - 1) // 150 + 1:03d}.lean"
    return path, lean_line(path, f"SemiBase.Catalogue.Order6.S6_{k}")


log("locating the theorems ...")
CENSUS_MAP = load("provenance/final-census-map.json", REPO)
ENDPOINT = {}        # k -> (path, line, theorem name, module as recorded), order six
for k in range(1, N6 + 1):
    if k in NONFINITE:
        point = CENSUS_MAP["non_finitely_based"][f"S6_{k}"]
        module, name = point["module"], point["name"]
    else:
        module, name = C.RECORD6[k]["module"], C.RECORD6[k]["theorem"]
    path = FILES[lean_module(module)]
    ENDPOINT[k] = (path, lean_line(path, name), name, module)
MISSING = [k for k, value in ENDPOINT.items() if value[1] is None]
LOWER_ENDPOINT = {}  # (n, k) -> dict, orders one to five
for key, record in LOWER.items():
    path = FILES.get(record["module"])
    line = lean_line(path, record["theorem"]) if path else None
    recorded = {f["path"]: f["sha256"] for f in record["source_files"]}
    LOWER_ENDPOINT[key] = {"path": path if line else None, "line": line, "theorem": record["theorem"],
                           "module": record["module"], "type": record["type"], "opposite": record["opposite_theorem"],
                           "same": bool(line) and recorded.get(path) == FILE_SHA.get(path),
                           "kind": lower_kind(record["module"])}
PUBLIC_LOWER = sum(1 for e in LOWER_ENDPOINT.values() if e["path"])
SIZE, KIND, OWN = {}, {}, {}
for k in range(1, N6 + 1):
    SIZE[(6, k)] = proof_size(lean_module(ENDPOINT[k][3]))
    KIND[(6, k)] = "no finite basis" if k in NONFINITE else kind_of(ENDPOINT[k][3])[0]
for key, e in LOWER_ENDPOINT.items():
    SIZE[key] = proof_size(e["module"]) if e["path"] else (0, 0)
    KIND[key] = e["kind"]
# Code of its own: the lines of the files that the proof of this class uses and the proof of no other class does.
_modules = Counter(lean_module(ENDPOINT[k][3]) for k in range(1, N6 + 1))
_modules.update(e["module"] for e in LOWER_ENDPOINT.values() if e["path"])
_masks = {m: closure_mask(m) for m in _modules}
_uses = sum(mask.astype(np.int64) * _modules[m] for m, mask in _masks.items())
for k in range(1, N6 + 1):
    OWN[(6, k)] = int(LINES[_masks[lean_module(ENDPOINT[k][3])] & (_uses == 1)].sum())
for key, e in LOWER_ENDPOINT.items():
    OWN[key] = int(LINES[_masks[e["module"]] & (_uses == 1)].sum()) if e["path"] else 0
KIND_NAMES = list(dict.fromkeys([name for _, name, _ in KINDS] + list(LOWER_KINDS)))
KIND_NAMES = [name for name in KIND_NAMES if name in set(KIND.values())]

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


def vars_text(ids):
    k = nvars(ids)
    return f"{plural(len(ids), 'identity', 'identities')} in {plural(k, 'variable')}"


def cayley(table, props, highlight=()):
    n = len(table)
    head = "<tr><th>·</th>" + "".join(f"<th>{b}</th>" for b in range(1, n + 1)) + "</tr>"
    body = []
    for a in range(1, n + 1):
        cells = []
        for b in range(1, n + 1):
            value = table[a - 1][b - 1]
            cls = ["diff"] if (a, b) in highlight else []
            if props["zero"] is not None and value == props["zero"] and not cls and n > 1:
                cls.append("zero")
            if a == b and value == a:
                cls.append("idem")
            cells.append(f'<td class="{" ".join(cls)}">{value}</td>' if cls else f"<td>{value}</td>")
        body.append(f"<tr><th>{a}</th>{''.join(cells)}</tr>")
    return f'<table class="cayley">{head}{"".join(body)}</table>'


STATUS_NOTE = {
    "irredundant": "Irredundant: none of these identities follows from the others; for each, a semigroup "
                   "satisfies the others but not it.",
    "candidate_reduced": "Reduced as far as the search went: some identity may still follow from the others.",
}


def provenance(c, v):
    """What is known about a basis, and on what it rests."""
    kind = c["kind"]
    if kind == "certified":
        users = BASIS_CLASSES[c["basis"]]
        whose = (f"the Lean theorem of {slink(users[0])} proves" if len(users) == 1 else
                 f"the Lean theorems of {plural(len(users), 'semigroup')} prove")
        if c["orientation"]:
            return (f"Certified in Lean, read backwards: {whose} that the reversed identities are a basis, and "
                    f"reading a basis backwards gives a basis of the transposed table.")
        return f"Certified in Lean: {whose} that these identities are a basis."
    if kind == "reduced":
        note = STATUS_NOTE[c["status"]]
        return (f"{note} Obtained from a basis certified in Lean by removing identities that follow from the others, "
                f"with the prover Vampire; the equivalence rests on Vampire's proofs, not on Lean.")
    if kind == "reduce":
        return ("The certified basis without the identities that follow from the others, by the prover Vampire; "
                "the equivalence rests on Vampire's proofs, not on Lean.")
    if kind == "search":
        d = c["derives"]
        what = "a certified basis" if d["kind"] == "certified" else "a reduced form of a certified basis"
        return (f"Found by a search among the identities of the variety in {plural(nvars(c['identities']), 'variable')}: "
                f"they hold in its generator, and Vampire derives from them {what}, so they are a basis. "
                f"This rests on Vampire's proofs, not on Lean.")
    raise ValueError(kind)


def witness_text(v, root):
    """Who shows the lower bound: a table of the pool, or a semigroup found by Vampire's model builder."""
    bound = BOUND_INFO[v]
    j = bound["k"]
    if bound.get("witness"):
        n, kk, o = C.MODELS[C.LABELS.index(bound["witness"])]
        return (f"{slink((n, kk), root, o=o, named=False)} satisfies every identity of {esc(vlabel(v))} in "
                f"{plural(j, 'variable')}, because its subsemigroups generated by {plural(j, 'element')} lie in "
                f"{esc(vlabel(v))}, but it is not in {esc(vlabel(v))}")
    m = len(bound["model"])
    return (f"the semigroup of order {m} shown below satisfies every identity of {esc(vlabel(v))} in "
            f"{plural(j, 'variable')}, but not {esc(fmt_identity(bound['violates']))}, which holds in "
            f"{esc(vlabel(v))}")


def optimality(v, root="../"):
    """The note on the number of variables of the basis in the fewest variables."""
    k = nvars(FEWEST_VARS[v]["identities"])
    low = LOWER_BOUND[v]
    if OPTIMAL[v]:
        return f"No basis uses fewer variables: {witness_text(v, root)}."
    searched = any(r["kind"] in ("search", "search-failed") for w in (v, VARIETIES[v]["dual"])
                   for r in FEW_BY.get(VARIETIES[w]["slug"], []))
    tail = (" A search with Vampire found neither a basis in fewer variables nor a semigroup that rules one out."
            if searched else "")
    if low >= 2:
        return (f"Every basis uses at least {plural(low, 'variable')}: {witness_text(v, root)}. Whether a basis in "
                f"fewer than {k} variables exists is not known.{tail}")
    return f"Whether a basis in fewer variables exists is not known.{tail}"


def countermodel_block(v):
    """The Cayley table of a semigroup that shows a lower bound, when it is not a table of the census."""
    bound = BOUND_INFO[v]
    if not bound.get("model"):
        return ""
    T = [[x + 1 for x in row] for row in bound["model"]]
    return (f'<details><summary>The semigroup of order {len(T)} that shows the lower bound</summary>'
            f'<div class="scroll">{cayley(T, properties(T))}</div><p class="note">Found by the finite model builder of Vampire and checked by '
            f'evaluation: it is associative, satisfies the rules of a complete rewriting system of the free object of '
            f'{esc(vlabel(v))} on {plural(bound["k"], "generator")}, and so every identity of {esc(vlabel(v))} in '
            f'{plural(bound["k"], "variable")}, but not {esc(fmt_identity(bound["violates"]))}.</p></details>')


def basis_boxes(v, root="../", heading="h2"):
    """The basis in the fewest variables and, when it differs, the basis with the fewest identities."""
    fv, fi = FEWEST_VARS[v], FEWEST_IDS[v]
    out = [f"""<div class="box"><p><b>Fewest variables</b>: {vars_text(fv['identities'])}</p>
{basis_list(fv['identities'])}<p class="note">{optimality(v, root)} {provenance(fv, v)}</p>{countermodel_block(v)}</div>"""]
    if canonical_basis(fi["identities"]) != canonical_basis(fv["identities"]):
        out.append(f"""<div class="box"><p><b>Fewest identities</b>: {vars_text(fi['identities'])}</p>
{basis_list(fi['identities'])}<p class="note">{provenance(fi, v)}</p></div>""")
    return "\n".join(out)


def footer_text():
    return (f"SemiBase: the semigroups of orders one to six and their identity bases. Tables from GAP Smallsemi 0.7.2; "
            f"proofs checked by Lean 4 in <a href=\"{REPO_URL}\">nasqret/semibase-order6</a> (commit "
            f"<span class=\"mono\">{COMMIT[:7]}</span>, <a href=\"https://doi.org/{DOI}\">doi:{DOI}</a>); bases "
            f"reduced and searched with Vampire, partly by the <span class=\"mono\">bases-min</span> tools of "
            f"M. Janota. Built {TODAY}.")


def page(title, body, root, description="", scripts=()):
    nav = f'<a class="home" href="{root}index.html">Home</a>' + "".join(
        f'<a href="{root}{href}">{label}</a>' for href, label in (
            ("browse.html", "Browse"), ("varieties.html", "Varieties"), ("names.html", "Names"),
            ("nonfinite.html", "No finite basis"), ("about.html", "About")))
    meta = f'\n<meta name="description" content="{esc(description)}">' if description else ""
    extra = "".join(f'<script src="{asset(s, root)}" defer></script>' for s in scripts)
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(title)}</title>{meta}
<link rel="icon" href="{asset('icon.svg', root)}" type="image/svg+xml">
<link rel="stylesheet" href="{asset('style.css', root)}">
<script type="speculationrules">{SPECULATION}</script></head>
<body><header class="top"><div class="wrap"><a class="brand" href="{root}index.html">SemiBase</a><nav>{nav}</nav>
<form onsubmit="return sbGo(this)" data-root="{root}"><input name="q" placeholder="Semigroup: 3842, 5-415, L, B2" aria-label="Go to a semigroup"></form></div></header>
<main class="wrap">
{body}
</main>
<footer><div class="wrap">{footer_text()}</div></footer>
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
    n = P["n"]
    comm = "commutative " if P["comm"] else ""
    if n == 1:
        return "the trivial semigroup, with one element", True
    if P["group"]:
        if P["cyclic"]:
            return f"the cyclic group of order {n}", True
        return ("the Klein four-group" if n == 4 else "the symmetric group S₃"), True
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


def describe(key):
    n, k = key
    P = PROPS[key]
    if n == 6 and k in NONFINITE:
        return (f"[6, {k}] is {NONFINITE_NAMES[k][1]}, one of the four semigroups of order six without a finite "
                f"identity basis.")
    phrase, special = kind_phrase(P)
    facts = []
    if not (P["band"] or P["group"] or P["nil"] or n == 1):
        facts.append(plural(len(P["idem"]), "idempotent"))
    if P["zero"] is not None and not P["nil"] and n > 1:
        facts.append(f"a zero, {P['zero']}")
    if P["one"] is not None and not P["group"] and n > 1:
        facts.append(f"an identity element, {P['one']}")
    listed = ", ".join(facts[:-1]) + (" and " if len(facts) > 1 else "") + (facts[-1] if facts else "")
    label = slabel(n, k)
    if key in NAMED:
        text = f"{label} is {NAMED[key][1]}: {phrase}" + (f" with {listed}." if listed else ".")
    elif special:
        text = f"{label} is {phrase}." + (f" It has {listed}." if listed else "")
    else:
        text = f"{label} is {phrase}" + (f" with {listed}." if listed else ".")
    v = CLASS_VAR[key]
    fv = FEWEST_VARS[v]["identities"]
    others = len([g for g in GENS[v] if g[:2] != key])
    text += (f" It is finitely based: {plural(len(fv), 'identity', 'identities')} in "
             f"{plural(nvars(fv), 'variable')} {verb(len(fv), 'defines', 'define')} its variety, which " +
             (f"{plural(others, 'other semigroup')} of order at most six also {verb(others, 'generates', 'generate')}."
              if others else "no other semigroup of order at most six generates."))
    return text


def tags(key):
    n, k = key
    P = PROPS[key]
    out = [f"order {n}"]
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
    out.append("self-dual" if SELF_DUAL[key] else "not self-dual")
    if not (n == 6 and k in NONFINITE):
        out.append(KIND[key])
    return '<div class="tags">' + "".join(f"<span>{esc(t)}</span>" for t in out) + "</div>"


def orientation_note(k):
    return {
        "direct": "The theorem is about the semigroup with exactly this table.",
        "both": "The theorem is about the semigroup with exactly this table.",
        "opposite": "The theorem is about the opposite semigroup, with the transposed table; read backwards, "
                    "its basis is the basis of this table shown above.",
        "relabelled": "The theorem is about a renumbering of this table; the census theorem checks the "
                      "explicit permutation of the elements.",
    }[C.RECORD6[k]["proof_orientation"]]


def size_row(key):
    files, lines = SIZE[key]
    own = (f" Of these, {OWN[key]:,} lines are used by the proof of this class and of no other." if OWN[key] else
           " All of it is shared with the proofs of other classes.")
    return ("Size", f"Checking this class alone compiles {files:,} Lean files with {lines:,} lines: the endpoint "
                    f"theorem and everything it imports, the shared library included.{own}")


def lean_block(key):
    n, k = key
    if n < 6:
        return lower_lean_block(key)
    path, line, name, module = ENDPOINT[k]
    spath, sline = census_ref(k)
    cpath, cline = catalogue_ref(k)
    rows = []
    if k in NONFINITE:
        shown = f"theorem {name.split('.')[-1]} {CENSUS_MAP['non_finitely_based'][f'S6_{k}']['statement']}"
    else:
        shown = C.RECORD6[k]["checked_type"]
        kind, text = kind_of(module)
        rows.append(("Table", esc(orientation_note(k))))
        rows.append(("Method", f"<b>{esc(kind)}</b>. {esc(text)}"))
    rows.append(size_row(key))
    rows.append(("Census", f'<a href="{lean_url(spath, sline)}" class="mono">SemiBase.Census.S6_{k}</a> checks '
                           f'that the theorem is about the table of this class and concludes '
                           f'<span class="mono">Classified</span>; <a href="{lean_url(cpath, cline)}" class="mono">'
                           f'SemiBase.Catalogue.Order6.S6_{k}</a> is the table, with the elements numbered 0 to 5.'))
    dl = "".join(f"<dt>{label}</dt><dd>{value}</dd>" for label, value in rows)
    return f"""<h2>Lean proof</h2>
<p>Endpoint theorem: <a href="{lean_url(path, line)}" class="mono">{esc(name)}</a></p>
<pre class="lean">{esc(shown)}</pre>
<dl class="props">{dl}</dl>"""


def lower_lean_block(key):
    e = LOWER_ENDPOINT[key]
    rows = [("Table", "The theorem is about the semigroup with exactly this table, with the elements numbered from "
                      "0 in Lean."),
            ("Method", f"<b>{esc(e['kind'])}</b>. {esc(LOWER_KINDS[e['kind']])}")]
    if e["path"]:
        theorem = f'<a href="{lean_url(e["path"], e["line"])}" class="mono">{esc(e["theorem"])}</a>'
        rows.append(size_row(key))
        rows.append(("Where", "In the public repository, which builds it as part of the proofs of order six" +
                     ("." if e["same"] else ", in a later revision of the file than the one the audit checked.")))
    else:
        theorem = f'<span class="mono">{esc(e["theorem"])}</span>'
        rows.append(("Where", "In the repository of the campaign that wrote the proofs, which is not public; this "
                              "theorem is not among those that the public repository needs for order six."))
    rows.append(("Transpose", f'<span class="mono">{esc(e["opposite"])}</span>: the basis read backwards is a basis of '
                              f'the opposite semigroup, with the transposed table.'))
    rows.append(("Audit", "The campaign's audit of the orders one to five checked the statement of each of the 1,309 "
                          "theorems, in both orientations, with the Lean kernel; for order five, a second replay "
                          "by the bases-min tools read the bases back from Lean."))
    dl = "".join(f"<dt>{label}</dt><dd>{value}</dd>" for label, value in rows)
    return f"""<h2>Lean proof</h2>
<p>Theorem: {theorem}</p>
<pre class="lean">{esc(e['type'])}</pre>
<dl class="props">{dl}</dl>"""


def variety_summary(key):
    """The varieties of a class and of its transpose, for the semigroup pages."""
    n, k = key
    v, w = CLASS_VAR[key], CLASS_VAR_OP[key]
    label = slabel(n, k)
    inside = IN_VARIETIES[(n, k, 0)]
    if SELF_DUAL[key]:
        transposed = "The class is self-dual, so its transpose generates the same variety."
    elif v == w:
        transposed = (f"The transposed table, the opposite semigroup, generates the same variety: "
                      f"{esc(vlabel(v))} is self-dual.")
    else:
        transposed = f"The transposed table, the opposite semigroup, generates the dual variety {vlink(w)}."
    return (f"<p>{label} generates the variety {vlink(v)}; {plural(len(GENS[v]), 'semigroup')} of order at most six "
            f"{verb(len(GENS[v]), 'generates', 'generate')} it, and {plural(len(MEMBERS[v]), 'semigroup')} of order "
            f"at most six {verb(len(MEMBERS[v]), 'lies', 'lie')} in it. {transposed} {label} lies in {inside} of the "
            f"{NV} varieties, those whose basis it satisfies.</p>")


def semigroup_page(key):
    n, k = key
    P = PROPS[key]
    nfb = n == 6 and k in NONFINITE
    name = NAMED.get(key, (None,))[0]
    title = slabel(n, k) + (f" {name}" if name else "")
    badge = '<span class="badge nfb">no finite basis</span>' if nfb else '<span class="badge fb">finitely based</span>'
    prev_key = (n, k - 1) if k > 1 else ((n - 1, COUNT[n - 1]) if n > 1 else None)
    next_key = (n, k + 1) if k < COUNT[n] else ((n + 1, 1) if n < 6 else None)
    pager = ('<div class="pager">' +
             (f'<a href="{sslug(prev_key)}.html">← {slabel(*prev_key)}</a>' if prev_key else "<span></span>") +
             (f'<a href="{sslug(next_key)}.html">{slabel(*next_key)} →</a>' if next_key else "") + "</div>")
    body = [pager, f"<h1>{esc(title)} {badge}</h1>", tags(key), f'<p class="lead">{esc(describe(key))}</p>']

    highlight, diff_note = (), ""
    if key in ((6, 3842), (6, 3843)):
        other = (6, 3843) if k == 3842 else (6, 3842)
        highlight = next(cells for j, cells in NEAR[key] if j == other)
        diff_note = f" Shaded: the two entries in which this table differs from that of {slink(other)}."
    rank = P["rank"]
    props = [
        ("Smallsemi", f'<span class="mono">SmallSemigroup({n}, {k})</span>'),
        ("Idempotents", esc(", ".join(map(str, P["idem"])))),
        ("Zero", esc(P["zero"] if P["zero"] is not None else "none")),
        ("Identity", esc(P["one"] if P["one"] is not None else "none")),
        ("Nilpotent", esc(f"yes, of class {P['nil']}" if P["nil"] else "no")),
        ("Commutative", "yes" if P["comm"] else "no"),
        ("Regular", ("yes" + (", inverse" if P["inverse"] else "")) if P["regular"] else "no"),
        ("Group", "yes" if P["group"] else "no"),
        ("𝒥-classes", str(P["jclasses"])),
        ("Rank", esc(f"{len(rank)}, generated by {{{', '.join(map(str, rank))}}}")),
        ("Self-dual", "yes: anti-isomorphic to itself" if SELF_DUAL[key] else
         "no: the class also stands for the opposite semigroup, with the transposed table"),
    ]
    dl = "".join(f"<dt>{label}</dt><dd>{value}</dd>" for label, value in props)
    zero_note = "; grey: the zero" if P["zero"] is not None and n > 1 else ""
    body.append(f"""<div class="two"><div><h2>Cayley table</h2>{cayley(TABLE[key], P, highlight)}
<p class="note">The product of the row element and the column element, numbered as in Smallsemi. Blue: idempotents
on the diagonal{zero_note}.{diff_note}</p></div>
<div><h2>Structure</h2><dl class="props">{dl}</dl></div></div>""")

    if nfb:
        family, argument, source = NONFINITE_DETAIL[k]
        body.append(f"""<h2>No finite identity basis</h2>
<div class="box nfb"><p>For every n, the identity</p><p class="formula">{esc(family)}</p>
<p>holds in {esc(name)}. {esc(argument)} A finite set of identities uses boundedly many variables, so it misses
one of these identities and is not a basis.</p>
<p class="note">Argument: {esc(source)}. That L, B₂¹, A₂ᵍ and A₂¹ are the only semigroups of order six without a
finite basis was shown by Lee, Li and Zhang (2012). See <a href="../nonfinite.html">the four nonfinitely based
semigroups</a>.</p></div>""")
    else:
        v = CLASS_VAR[key]
        b = CLASS_BASIS[key]
        certified = BASIS[b]
        body.append(f"<h2>Identity basis</h2>{basis_boxes(v)}")
        shown = {canonical_basis(FEWEST_VARS[v]["identities"]), canonical_basis(FEWEST_IDS[v]["identities"])}
        if canonical_basis(certified) in shown:
            body.append("<h3>Basis certified in Lean</h3><p>The Lean theorem below certifies the basis "
                        + ("above." if len(shown) == 1 else "with the fewest variables above." if
                           canonical_basis(certified) == canonical_basis(FEWEST_VARS[v]["identities"]) else
                           "with the fewest identities above.") + "</p>")
        elif len(certified) <= 20:
            body.append(f"<h3>Basis certified in Lean: {vars_text(certified)}</h3>" + basis_list(certified))
        else:
            body.append(f"<h3>Basis certified in Lean</h3><p>The Lean theorem certifies a longer basis, of "
                        f"{blink(b)} in {plural(nvars(certified), 'variable')}; the bases above are equivalent "
                        f"to it.</p>")
    body.append(lean_block(key))

    if nfb:
        inside = IN_VARIETIES.get((6, k, 0), 0)
        body.append(f"""<h2 id="variety">Variety</h2><p>[6, {k}] generates the variety {nlink(k)}, which has no finite
basis and so is not one of the {NV} finitely based varieties of the census; [6, {k}] is self-dual, and no other
semigroup of order at most six generates it. """ + (f"It lies in {inside} of the {NV}, those whose basis it satisfies.</p>" if inside
            else f"It lies in none of the {NV}: no finitely based semigroup of order at most six generates a variety "
                 "that contains it, as evaluating their bases in this table shows.</p>"))
    else:
        v = CLASS_VAR[key]
        up, down = UP[v], DOWN[v]
        body.append(f"""<h2 id="variety">Variety</h2>{variety_summary(key)}
<dl class="props"><dt>Directly above</dt><dd>{links([vlink(u) for u in up]) if up else 'none: a maximal variety of the census'}</dd>
<dt>Directly below</dt><dd>{links([vlink(u) for u in down]) if down else 'none: a minimal variety of the census'}</dd></dl>
<p><a href="../varieties.html#graph={VARIETIES[v]['slug']}&amp;around=2">{esc(vlabel(v))} in the inclusion graph</a>,
with the varieties above and below it.</p>""")
        others = [g for g in GENS[v] if g[:2] != key or g[2]]
        if others:
            more = (f'<p><a href="../v/{VARIETIES[v]["slug"]}.html">All {len(others):,} on the variety page</a></p>'
                    if len(others) > 48 else "")
            body.append(f"<h3>Generating the same variety</h3>{links([sglink(g) for g in others[:48]])}{more}")

    near = sorted(NEAR.get(key, []), key=lambda item: (len(item[1]), item[0]))
    if near:
        items = []
        for j, cells in near[:30]:
            where = ", ".join(f"({a}, {b})" for a, b in cells)
            if j not in CLASS_VAR:
                extra = ", no finite basis"
            elif key in CLASS_VAR and CLASS_VAR[j] == CLASS_VAR[key]:
                extra = ", the same variety"
            else:
                extra = f", variety {vlink(CLASS_VAR[j])}"
            items.append(f"<li>{slink(j)}: {plural(len(cells), 'entry', 'entries')} {where}{extra}</li>")
        more = f'<p class="note">And {len(near) - 30} more.</p>' if len(near) > 30 else ""
        body.append(f"""<h2>Nearby tables</h2><p class="note">Semigroups of the same order whose Smallsemi table differs
from this one in one or two entries (row, column), as the tables are listed, not up to renumbering.</p>
<ul class="near">{''.join(items)}</ul>{more}""")
    return page(f"{title} · SemiBase", "\n".join(body), "../",
                f"The semigroup {slabel(n, k)} of order {n}: Cayley table, identity basis, Lean proof, variety.")


def hasse(v):
    up, down = UP[v], DOWN[v]
    shown_up, shown_down = up[:8], down[:8]
    W = max(380, 108 * max(len(shown_up), len(shown_down), 1) + 20)

    def place(items, y):
        return [((i + 0.5) * W / len(items), y, u) for i, u in enumerate(items)]

    top, bottom, mid = place(shown_up, 22), place(shown_down, 162), (W / 2, 92)
    out = [f'<div class="hasse-wrap"><svg class="hasse" width="{W:.0f}" height="186" viewBox="0 0 {W:.0f} 186" '
           f'role="img" aria-label="The varieties directly above and below {esc(vlabel(v))}">']
    for x, y, _ in top + bottom:
        out.append(f'<line x1="{x:.0f}" y1="{y:.0f}" x2="{mid[0]:.0f}" y2="{mid[1]:.0f}"/>')

    def node(x, y, u, own=False):
        label = vlabel(u)
        w = 7.4 * len(label) + 16
        shape = (f'<rect x="{x - w / 2:.0f}" y="{y - 12:.0f}" width="{w:.0f}" height="24" rx="5"'
                 f'{" class=\"self\"" if own else ""}/><text x="{x:.0f}" y="{y + 4:.0f}">{esc(label)}</text>')
        return shape if own else f'<a href="{VARIETIES[u]["slug"]}.html">{shape}</a>'

    out += [node(x, y, u) for x, y, u in top + bottom]
    out.append(node(mid[0], mid[1], v, own=True))
    if len(up) > len(shown_up):
        out.append(f'<text x="{W - 4:.0f}" y="50" class="more">+{len(up) - len(shown_up)} more above</text>')
    if len(down) > len(shown_down):
        out.append(f'<text x="{W - 4:.0f}" y="138" class="more">+{len(down) - len(shown_down)} more below</text>')
    out.append("</svg></div>")
    return "".join(out)


def sgv_link(v):
    entry = SGV.get(v)
    if not entry:
        return ""
    return (f'<a href="{SGV_URL}#V{entry["order"]}{entry["number"]}">{entry["name"]}</a> in the database of Araújo, '
            f'Araújo, Cameron, Lee and Raminhos')


def variety_page(v):
    var = VARIETIES[v]
    n, k, o = var["name"]
    gens, members = GENS[v], MEMBERS[v]
    up, down = UP[v], DOWN[v]
    label = vlabel(v)
    generator = slink((n, k), o=o, named=False)
    dual = ("It is self-dual: the opposite of each of its semigroups lies in it too." if var["self_dual"] else
            f"Its dual, the variety of the opposite semigroups, is {vlink(var['dual'])}.")
    primitive = (f"No semigroup of order less than {n} generates it." if n > 1 else "")
    permanent = (f'<p class="note">The name is permanent: {slabel(n, k, o)} is the least generator of the variety in '
                 f'the order that <a href="../names.html">names the varieties</a>.</p>')
    sgv = sgv_link(v)
    sgv_text = f" It is {sgv}." if sgv else ""
    certified = []
    seen = set()
    for i in var["gens"]:
        nn, kk, oo = MODELS[i]
        b = CLASS_BASIS[(nn, kk)]
        if (b, oo) in seen:
            continue
        seen.add((b, oo))
        users = BASIS_CLASSES[b]
        whose = (slink(users[0]) if len(users) == 1 else plural(len(users), "semigroup"))
        certified.append(f"<li>{blink(b)} in {plural(nvars(BASIS[b]), 'variable')}" +
                         (", read backwards" if oo else "") + f", certified in Lean for {whose}" +
                         (", whose transposes generate this variety" if oo else "") + "</li>")
    old = OLD_NAME.get(v)
    renamed = (f'<p class="note">Called V[{old}] in the first release of the census, which named each variety after '
               f'its smallest generator of order six.</p>' if old is not None and str(old) != var["slug"] else "")
    body = f"""<h1>Variety {esc(label)}</h1>
<p class="lead">The variety generated by {generator}{f', the opposite of {slabel(n, k)}, with the transposed table' if o else ''}:
all semigroups that satisfy every identity of {slabel(n, k, o)}. {primitive} {dual}{sgv_text}</p>{permanent}{renamed}
<h2>Identity bases</h2>{basis_boxes(v)}
<h3>Certified in Lean</h3><ul>{''.join(certified)}</ul>
{'<p class="note">The certified bases define the same variety: each holds in the generators of the others, and each is a basis of the variety of its own generator.</p>' if len(certified) > 1 else ''}
<h2>Among the {NV} varieties</h2>{hasse(v)}
<dl class="props"><dt>Directly above</dt><dd>{links([vlink(u) for u in up]) if up else 'none: a maximal variety of the census'}</dd>
<dt>Directly below</dt><dd>{links([vlink(u) for u in down]) if down else 'none: a minimal variety of the census'}</dd></dl>
<p class="note">A variety lies above another when it contains it. {esc(label)} lies in another variety exactly when
{slabel(n, k, o)} satisfies a basis of that variety, and the basis certified in Lean decides it, so every inclusion
among the {NV} varieties is known.</p>
<p><a href="../varieties.html#graph={var['slug']}&amp;around=2">Explore {esc(label)} in the inclusion graph</a>, with
everything above and below it.</p>
<h2>Generated by {plural(len(gens), 'semigroup')}</h2><p class="note">Of order at most six, up to isomorphism:
{by_order(gens)}. A superscript op marks the opposite semigroup of a class, with the transposed table.</p>
{semigroup_list(gens)}
<h2>Contains {plural(len(members), 'semigroup')}</h2>
<p class="note">Of order at most six, up to isomorphism: {by_order(members)}; those that satisfy the basis.</p>
{semigroup_list(members, inline=0)}"""
    return page(f"Variety {label} · SemiBase", body, "../",
                f"The variety {label}: bases in the fewest variables and identities, inclusions, generators.")


def basis_page(b):
    users = BASIS_CLASSES[b]
    v = CLASS_VAR[users[0]]
    n = users[0][0]
    ids = BASIS[b]
    reduced = REDUCED.get(b)
    shorter = (f" Removing the identities that follow from the others leaves "
               f"{plural(len(reduced['identities']), 'identity', 'identities')} (Vampire)." if reduced else "")
    orders = sorted({u[0] for u in users})
    who = slink(users[0]) if len(users) == 1 else plural(len(users), "semigroup") + (
        f" of order {orders[0]}" if len(orders) == 1 else
        " of orders " + ", ".join(map(str, orders[:-1])) + f" and {orders[-1]}")
    body = f"""<h1>A certified basis of {plural(len(ids), 'identity', 'identities')}</h1>
<p class="lead">This list of identities, in {plural(nvars(ids), 'variable')}, is a basis, proved in Lean, of {who},
{'which generates' if len(users) == 1 else 'all of which generate'} the variety {vlink(v)}.{shorter} The
<a href="../v/{VARIETIES[v]['slug']}.html">variety page</a> shows its bases in the fewest variables and with the fewest
identities. Read backwards, the identities are a basis of the transposed tables.</p>
<p class="note">Identifier <span class="mono">{esc(b)}</span>{' in the data of the bases-min seal' if b.startswith('sb-') else ''}.</p>
<h2>Certified for</h2>{links([slink(u) for u in users])}
<h2>The identities</h2>{basis_list(ids)}"""
    return page(f"Certified basis {b} · SemiBase", body, "../")


def redirect_page(target, label):
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><title>{esc(label)} · SemiBase</title>
<meta http-equiv="refresh" content="0; url={target}"><link rel="canonical" href="{target}"></head>
<body><h1>{esc(label)}</h1><p>This variety has a new name: <a href="{target}">{esc(label)}</a>.</p></body></html>
"""


def browse_page():
    kinds = "".join(f'<option value="{i}">{esc(n)}</option>' for i, n in enumerate(KIND_NAMES))
    yn = '<option value="">any</option><option value="yes">yes</option><option value="no">no</option>'
    orders = "".join(f'<option value="{n}">{n}</option>' for n in C.ORDERS)
    body = f"""<h1>Browse the semigroups of orders one to six</h1>
<p class="lead">All {len(CLASSES):,} semigroups of orders one to six up to isomorphism and anti-isomorphism,
numbered as in Smallsemi: {', '.join(f'{COUNT[n]:,} of order {n}' for n in C.ORDERS)}. Filter them, sort by a
column, and open one for its table, bases and proof.</p>
<details class="filterbox" id="filterbox" open><summary>Filters<span id="active"></span></summary>
<div class="filters">
<label>Order <select id="f-order"><option value="">any</option>{orders}</select></label>
<label>Numbers from <input id="f-from" type="number" min="1" max="15973"></label>
<label>to <input id="f-to" type="number" min="1" max="15973"></label>
<label>Finite basis <select id="f-status"><option value="">any</option><option value="fb">yes</option><option value="nfb">no</option></select></label>
<label>Identities from <input id="f-bmin" type="number" min="1"></label>
<label>to <input id="f-bmax" type="number" min="1"></label>
<label>Variables <select id="f-vars"><option value="">any</option>{''.join(f'<option>{i}</option>' for i in range(2, 13))}</select></label>
<label>Variety <input id="f-variety" type="text" placeholder="5-540, 7390-op" size="10"></label>
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
<div class="scroll long" id="browse-table"><table class="list"><thead><tr><th class="sort" data-key="id">Semigroup</th>
<th class="sort num" data-key="basis" title="identities in the basis with the fewest identities">Identities</th>
<th class="sort num" data-key="vars" title="variables of the basis in the fewest variables">Variables</th>
<th class="sort" data-key="variety">Variety</th><th class="sort num opt" data-key="idem">Idemp.</th>
<th class="sort num opt" data-key="nil" title="nilpotency class">Nilp.</th><th class="opt">Monoid</th><th class="opt">Comm.</th>
<th class="opt">Band</th><th class="opt">Self-dual</th><th class="sort" data-key="kind">Proof</th>
<th class="sort num opt" data-key="lines" title="lines of Lean the proof of this class compiles">Lean lines</th></tr></thead>
<tbody id="rows"></tbody></table></div>
<p><button id="more" class="more" type="button" hidden>Show more</button></p>
<p class="note">Identities: the basis of the variety with the fewest identities. Variables: the basis with the fewest
variables, the largest number of distinct variables in one of its identities. Variety: the variety the table
generates. Lean lines: the lines of Lean that checking the class alone compiles, shared library included, for the
theorems in the public repository. The filters are kept in the address, so a filtered list can be bookmarked.</p>"""
    return page("Browse · SemiBase", body, "", scripts=("data.js", "browse.js"))


def data_js():
    """The table of browse.html, one string per column with one or more base-36 digits per semigroup."""
    position = {v: v for v in range(NV)}
    columns = {name: [] for name in ("order", "num", "basis", "vars", "variety", "nil", "idem", "flags", "kind",
                                     "lines")}
    for key in CLASSES:
        n, k = key
        P = PROPS[key]
        fb = key in CLASS_VAR
        v = CLASS_VAR.get(key)
        columns["order"].append(str(n))
        columns["num"].append(b36(k, 3))
        columns["basis"].append(b36(len(FEWEST_IDS[v]["identities"]) if fb else 0, 2))
        columns["vars"].append(DIGITS[nvars(FEWEST_VARS[v]["identities"])] if fb else "0")
        columns["variety"].append(b36(position[v] if fb else NV + NONFINITE.index(k), 2))
        columns["nil"].append(str(P["nil"]))
        columns["idem"].append(str(len(P["idem"])))
        flags = int(P["one"] is not None and n > 1) | P["comm"] << 1 | P["band"] << 2 | SELF_DUAL[key] << 3 | \
            P["regular"] << 4
        columns["flags"].append(DIGITS[flags])
        columns["kind"].append(DIGITS[KIND_NAMES.index(KIND[key])])
        columns["lines"].append(b36(SIZE[key][1], 4))
    payload = {"n": len(CLASSES), "kinds": KIND_NAMES,      # the varieties, then those of the four without a basis
               "slugs": [var["slug"] for var in VARIETIES] + [str(k) for k in NONFINITE],
               "labels": [var["label"] for var in VARIETIES] + [f"V[6, {k}]" for k in NONFINITE]}
    payload.update({name: "".join(values) for name, values in columns.items()})
    return "window.SEMIBASE = " + json.dumps(payload, separators=(",", ":"), ensure_ascii=False) + ";\n"


GRAPH_CACHE = os.path.join(DATA, "graph-layout.json")


def radius(v):
    return round(3.5 + 1.3 * math.log(len(GENS[v])), 1)


def graph_layout():
    """Place the varieties, larger ones higher, and route the covering edges, with Graphviz dot.

    The result is kept in data/graph-layout.json with a hash of the input to dot, so that a build without
    Graphviz reuses it as long as the varieties and their order have not changed."""
    lines = ["digraph varieties {",
             "graph [rankdir=TB, ranksep=2.4, nodesep=0.25, splines=spline, newrank=true, mclimit=4, remincross=true];",
             'node [shape=circle, fixedsize=true, label=""];',
             "edge [arrowhead=none, headclip=false, tailclip=false];"]
    lines += [f'"{VARIETIES[v]["slug"]}" [width={2 * radius(v) / 72:.4f}];' for v in range(NV)]
    lines += [f'"{VARIETIES[b]["slug"]}" -> "{VARIETIES[a]["slug"]}";' for a in range(NV) for b in UP[a]]
    source = "\n".join(lines + ["}"]) + "\n"
    key = hashlib.sha256(source.encode()).hexdigest()
    if os.path.exists(GRAPH_CACHE):
        with open(GRAPH_CACHE, encoding="utf-8") as handle:
            cached = json.load(handle)
        if cached.get("key") == key:
            return cached
    log("laying out the graph with dot ...")
    try:
        output = subprocess.run(["dot", "-Tjson"], input=source, capture_output=True, text=True, check=True).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"Graphviz (dot) is needed to lay out the graph of the varieties: {error}")
    graph = json.loads(output)
    width, height = (float(x) for x in graph["bb"].split(",")[2:])
    names = {obj["_gvid"]: obj["name"] for obj in graph["objects"]}
    nodes = {}
    for obj in graph["objects"]:
        x, y = map(float, obj["pos"].split(","))
        nodes[obj["name"]] = [round(x, 1), round(height - y, 1)]
    edges = {}
    for edge in graph["edges"]:
        points = [tuple(map(float, p.split(","))) for p in edge["pos"].split() if not p.startswith(("e,", "s,"))]
        assert len(points) % 3 == 1
        coords = [f"{round(x)} {round(height - y)}" for x, y in points]
        upper, lower = names[edge["tail"]], names[edge["head"]]
        edges[f"{lower} {upper}"] = "M" + coords[0] + "C" + " ".join(coords[1:])
    layout = {"key": key, "width": round(width), "height": round(height), "nodes": nodes, "edges": edges}
    with open(GRAPH_CACHE, "w", encoding="utf-8") as handle:
        json.dump(layout, handle, separators=(",", ":"))
    return layout


def graph_data_js():
    """The data of the inclusion graph: the varieties in the order of their names, the covering edges as pairs
    (lower, upper) with their route, the bases in the fewest variables, and the variety of each semigroup."""
    layout = graph_layout()
    nodes = [[VARIETIES[v]["slug"], *layout["nodes"][VARIETIES[v]["slug"]], radius(v), len(GENS[v]),
              len(MEMBERS[v]), VARIETIES[v]["label"], VARIETIES[v]["dual"]] for v in range(NV)]
    edges = [[a, b, layout["edges"][f"{VARIETIES[a]['slug']} {VARIETIES[b]['slug']}"]] for a in range(NV) for b in UP[a]]
    bases = [[nvars(FEWEST_VARS[v]["identities"])] + [fmt_identity(e) for e in
                                                      sorted_identities(FEWEST_VARS[v]["identities"])]
             for v in range(NV)]
    cls = "".join(b36(CLASS_VAR[key], 2) if key in CLASS_VAR else "--" for key in CLASSES)
    payload = {"width": layout["width"], "height": layout["height"], "nodes": nodes, "edges": edges,
               "bases": bases, "cls": cls, "orders": [COUNT[n] for n in C.ORDERS],
               "alias": {str(old): VARIETIES[v]["slug"] for old, v in MOVED.items()}}
    return "window.SB_GRAPH = " + json.dumps(payload, separators=(",", ":"), ensure_ascii=False) + ";\n"


def varieties_page():
    maximal = sorted((v for v in range(NV) if not UP[v]), key=lambda v: (-len(MEMBERS[v]), v))
    minimal = [v for v in range(NV) if not DOWN[v]]
    primitive = Counter(VARIETIES[v]["name"][0] for v in range(NV))
    selfdual = sum(1 for var in VARIETIES if var["self_dual"])
    optimal = sum(1 for v in range(NV) if OPTIMAL[v])
    rows = []
    for v in range(NV):                          # the order of the names
        fi, fv = FEWEST_IDS[v]["identities"], FEWEST_VARS[v]["identities"]
        first = min(fi, key=lambda e: (size(e), e["lhs"], e["rhs"]))
        var = VARIETIES[v]
        dual = "self-dual" if var["self_dual"] else vlink(var["dual"], "")
        entry = SGV.get(v)
        rows.append(f"<tr><td>{vlink(v, '')}</td><td class=\"opt\">{dual}</td>"
                    f"<td class=\"num\">{var['name'][0]}</td><td class=\"num\">{len(fi)}</td>"
                    f"<td class=\"num\">{nvars(fv)}{'' if OPTIMAL[v] else '?'}</td>"
                    f"<td class=\"num\">{len(GENS[v]):,}</td><td class=\"num opt\">{len(MEMBERS[v]):,}</td>"
                    f"<td class=\"num opt\">{len(UP[v])}</td><td class=\"num opt\">{len(DOWN[v])}</td>"
                    f"<td class=\"opt\">{entry['name'] if entry else '–'}</td>"
                    f"<td class=\"mono opt\">{esc(fmt_identity(first))}{' …' if len(fi) > 1 else ''}</td></tr>")
    counts = ", ".join(f"{primitive[n]} of order {n}" for n in C.ORDERS)
    body = f"""<h1>The {NV} varieties</h1>
<p class="lead">The finitely based semigroups of orders one to six, each table and its transpose, generate {NV}
distinct varieties, counting a variety and its dual separately: {selfdual} are self-dual and the others form
{(NV - selfdual) // 2} dual pairs. V[n, k] is the variety generated by [n, k], and V[n, k]{OP} its dual, generated by
the transposed table; each is named after its least generator, by the rule that <a href="names.html">Names</a> fixes
once and for all. By the order of that generator: {counts}. Ordered by inclusion, they have
{sum(len(UP[v]) for v in range(NV)):,} covering pairs, {len(maximal)} maximal varieties and {len(minimal)} minimal one,
the trivial variety; every inclusion is decided. The four semigroups without a finite basis generate four more
varieties, {', '.join(nlink(k, '') for k in NONFINITE[:-1])} and {nlink(NONFINITE[-1], '')}, which lie in none of
these; they are not in the list or the graph.</p>
<div class="tabs" role="tablist"><a href="#list" role="tab" aria-selected="true">List</a><a href="#graph" role="tab"
aria-selected="false">Inclusion graph</a></div>
<noscript><p class="note">The inclusion graph needs JavaScript; the list below has the same information.</p></noscript>
<section id="graph-view" hidden>
<div class="graph" id="graph" data-src="{asset('graph-data.js', '')}">
<div class="bar">
<form><input type="search" placeholder="Find V[5, 540], or a semigroup [6, 3842]" aria-label="Find a variety, or the variety of a semigroup"><button class="btn" type="submit">Find</button></form>
<div class="group" role="group" aria-label="View"><button type="button" class="btn" id="g-all" aria-pressed="true">Whole order</button><button type="button" class="btn" id="g-around" aria-pressed="false" disabled>Around selection</button><select id="g-steps" aria-label="Steps around the selection" disabled><option value="1">1 step</option><option value="2" selected>2 steps</option><option value="3">3 steps</option><option value="0">all</option></select></div>
<div class="group" role="group" aria-label="Zoom"><button type="button" class="btn" id="g-out" aria-label="Zoom out">−</button><button type="button" class="btn" id="g-in" aria-label="Zoom in">+</button><button type="button" class="btn" id="g-fit">Fit</button><button type="button" class="btn" id="g-full" aria-pressed="false">Full screen</button></div>
</div>
<div class="stage"><div class="view"><canvas tabindex="0" role="img" aria-label="The inclusion graph of the {NV} varieties. The List tab has the same information as text."></canvas><div class="msg" aria-live="polite"></div><div class="tip" hidden></div></div><div class="info" hidden></div></div>
<div class="legend"><span><i style="background:var(--accent)"></i>selected</span><span><i style="background:var(--good)"></i>above: contains it</span><span><i style="background:var(--warn)"></i>below: lies in it</span><span>larger dots: more generators</span></div>
</div>
<p class="note">Each dot is a variety, drawn below the varieties that contain it; a line joins it to each variety
directly above it. Select a variety to see everything above and below it, and choose "Around selection" to lay out
only those, up to a number of steps. The address keeps the selection, so a view can be bookmarked or shared. Layout:
Graphviz.</p>
</section>
<section id="list-view">
<h2>Maximal varieties ({len(maximal)})</h2><p class="note">Contained in no other variety of the census, the largest
first; start here and go down.</p>{links([vlink(v, '') for v in maximal])}
<h2>All varieties</h2><p class="note">In the order of their names; click a column to sort. Order: the least
order of a generator. Identities: the basis with the fewest identities, whose shortest identity is shown. Variables:
the basis in the fewest variables, with a question mark when a basis in fewer variables is not ruled out ({NV - optimal}
of the {NV}). Generators and Contains: semigroups of orders one to six, up to isomorphism. Database: the name in the
database of Araújo et al. of the {len(SGV)} varieties generated by a semigroup of order at most five.</p>
<div class="listbar"><span></span><button type="button" class="btn colsbtn" data-target="varieties-table" aria-pressed="false">All columns</button></div>
<div class="scroll long" id="varieties-table"><table class="list sortable"><thead><tr><th data-dir="1">Variety</th><th class="opt">Dual</th><th class="num">Order</th>
<th class="num">Identities</th><th class="num">Variables</th><th class="num">Generators</th><th class="num opt">Contains</th>
<th class="num opt">Above</th><th class="num opt">Below</th><th class="opt">Database</th><th class="opt">Shortest identity</th></tr></thead>
<tbody>{''.join(rows)}</tbody></table></div>
</section>"""
    return page("Varieties · SemiBase", body, "", scripts=("graph.js",))


def nonfinite_page():
    sections = []
    for k in (3843, 8564, 8878, 13747):
        name, words = NONFINITE_NAMES[k]
        family, argument, source = NONFINITE_DETAIL[k]
        path, line, theorem, _ = ENDPOINT[k]
        sections.append(f"""<h2>{esc(name)} = {slink((6, k), '', named=False)}</h2><div class="two"><div>{cayley(TABLE[(6, k)], PROPS[(6, k)])}</div>
<div><p>{esc(words[0].upper() + words[1:])}. For every n,</p><p class="formula">{esc(family)}</p><p>{esc(argument)}</p>
<p class="note">{esc(source[0].upper() + source[1:])}. Lean: <a href="{lean_url(path, line)}" class="mono">{esc(theorem)}</a>.
Its variety: {nlink(k, '')}.</p></div></div>""")
    body = f"""<h1>The four semigroups without a finite basis</h1>
<p class="lead">Every semigroup of order at most six has a finite identity basis except four, all of order six: L,
B₂¹, A₂ᵍ and A₂¹ (Lee, Li and Zhang 2012); every semigroup of order at most five is finitely based (Trahtman 1983).
Each Lean proof exhibits infinitely many identities of the semigroup, one for every n, and a property of words that
separates the two sides of the n-th identity and survives every derivation step with an identity in fewer than n
variables. So no finite set of identities derives them all. None of the four, and none of their transposes, lies in
any of the {NV} varieties generated by the finitely based semigroups of orders one to six. Each of the four is
self-dual and generates a variety of its own, {', '.join(nlink(k, '') for k in NONFINITE[:-1])} and
{nlink(NONFINITE[-1], '')}; three identities tell them apart (<a href="names.html#checks">Names</a>).</p>
{''.join(sections)}"""
    return page("No finite basis · SemiBase", body, "")


def separation_table(root="../"):
    """The identities that tell apart the varieties of the four nonfinitely based classes, evaluated."""
    stack = np.stack([np.array(TABLE[(6, k)], dtype=np.int8) - 1 for k in NONFINITE])
    results = np.array([C.satisfied([e], stack) for e in C.NONFINITE_SEPARATION])
    assert all((results[:, a] != results[:, b]).any() for a, b in itertools.combinations(range(len(NONFINITE)), 2))
    head = "".join(f'<th><a href="{root}s/{k}.html">{esc(NONFINITE_NAMES[k][0])}</a></th>' for k in NONFINITE)
    rows = "".join(f'<tr><td class="mono">{esc(fmt_identity(e))}</td>' +
                   "".join(f"<td>{'holds' if h else 'fails'}</td>" for h in held) + "</tr>"
                   for e, held in zip(C.NONFINITE_SEPARATION, results))
    return (f'<div class="scroll"><table class="list"><thead><tr><th>Identity</th>{head}</tr></thead>'
            f"<tbody>{rows}</tbody></table></div>")


def packed_form(T):
    """The least renumbering of a 0-based table (census.canonical_table), two entries a, b per character a·n + b:
    the key under which names.js finds a table."""
    key = C.canonical_table(T)
    n, flat = key[0], list(key[1:])
    flat += [0] * (len(flat) % 2)
    return "".join(DIGITS[flat[i] * n + flat[i + 1]] for i in range(0, len(flat), 2))


def forms_js():
    """For the lookup on names.html: per order, for k = 1, 2, ..., the packed least renumbering of the table of
    [n, k], then the positions in the list of names of the varieties of the table and of its transpose, two base-36
    digits each. A table that is not the renumbering of any of them is a renumbering of a transpose."""
    index = {e["model"]: i for i, e in enumerate(C.NAMES)}

    def at(n, k, o):
        if (n, k) not in CLASS_BASIS:
            return index[(n, k, 0)]
        return index[VARIETIES[(CLASS_VAR_OP if o else CLASS_VAR)[(n, k)]]["name"]]
    forms = [""]
    for n in C.ORDERS:
        forms.append("".join(packed_form(np.array(TABLE[(n, k)], dtype=np.int8) - 1) + b36(at(n, k, 0), 2) +
                             b36(at(n, k, 1), 2) for k in range(1, COUNT[n] + 1)))
    data = {"names": [e["slug"] for e in C.NAMES], "nonfinite": [str(k) for k in NONFINITE], "forms": forms}
    return ("// The tables of orders one to six for the lookup on names.html, written by build.py (forms_js).\n"
            f"window.SB_FORMS = {json.dumps(data, separators=(',', ':'))};\n")


def long_date(iso):
    d = datetime.date.fromisoformat(iso)
    return f"{d.day} {d:%B %Y}"


def names_page():
    by_order = Counter(e["model"][0] for e in C.NAMES)
    total = len(C.NAMES)
    selfdual = sum(1 for e in C.NAMES if e["dual"] == e["model"])
    small = sum(by_order[n] for n in C.ORDERS if n <= 5)
    counts = ", ".join(f"{by_order[n]} of order {ORDER_WORD[n]}" for n in C.ORDERS)
    nfb = ", ".join(f"{nlink(k, '')} of {esc(NONFINITE_NAMES[k][0])}" for k in NONFINITE[:-1])
    nfb += f" and {nlink(NONFINITE[-1], '')} of {esc(NONFINITE_NAMES[NONFINITE[-1]][0])}"
    first = ", ".join(esc(e["label"]) for e in C.NAMES[:7])
    date = long_date(REGISTRY["date"])
    lists = []
    for n in C.ORDERS:
        items = links([name_link(e, "") for e in C.NAMES if e["model"][0] == n])
        if n < 6:
            lists.append(f"<h3>Generator order {ORDER_WORD[n]}: {by_order[n]}</h3>{items}")
        else:
            lists.append(f"<h3>Generator order six: {by_order[n]}</h3><details><summary>Show all "
                         f"{by_order[n]}</summary>{items}</details>")
    # The example of the lookup: [6, 5762] with its elements numbered backwards; it generates V[5, 540].
    T = np.array(TABLE[(6, 5762)]) - 1
    flip = T.shape[0] - 1 - T[::-1, ::-1]
    example = "&#10;".join(" ".join(str(x + 1) for x in row) for row in flip)
    body = f"""<h1>Names of varieties</h1>
<p class="lead">Each variety generated by a semigroup of order at most six has a permanent name, V[n, k] or
V[n, k]{OP}, made of the Smallsemi number of its least generator. This page fixes the rule once and for all, states
what it guarantees, and gives the procedure to find the name of the variety of a finite semigroup.</p>
<p class="note">Version 1, {date}: {total} names, fixed in <a href="names-v1.json">names-v1.json</a>
(SHA-256 <span class="mono">{NAMES_SHA}</span>).</p>
<h2 id="rule">The rule</h2>
<ol class="rule">
<li><b>Semigroups.</b> For each order n up to eight, the GAP package Smallsemi lists the semigroups of order n up to
isomorphism and anti-isomorphism. [n, k] is its semigroup number k, with the Cayley table
<span class="mono">MultiplicationTable(SmallSemigroup(n, k))</span> of Smallsemi 0.7.2, in which row i and column j
hold the product of the elements i and j. [n, k]{OP} is the opposite semigroup, with the transposed table. Every
semigroup of order n is isomorphic to [n, k] or to [n, k]{OP} for exactly one k, and to both when [n, k] is
self-dual.</li>
<li><b>Triples.</b> The triple (n, k, 0) stands for [n, k] and (n, k, 1) for [n, k]{OP}. Triples are compared by n,
then by k, then by the last entry: a smaller order first, then a smaller number, then a table before its
transpose.</li>
<li><b>Names.</b> A variety generated by a semigroup of order at most eight is named after the least triple
(n, k, o) whose semigroup generates it: V[n, k] when o = 0, and V[n, k]{OP} when o = 1.</li>
<li><b>Order of the varieties.</b> Varieties are ordered as the triples that name them: {first}, and so on. The list
of names below, names-v1.json and the <a href="varieties.html">list of varieties</a> follow this order.</li>
</ol>
<p>Spaces do not matter, so V[5,540] and V[5, 540] are the same name, and in plain text V[5, 540]{OP} may be written
V[5,540]^op. The square brackets set these names apart from the names V(n, i) of the database of Araújo, Araújo,
Cameron, Lee and Raminhos: there, too, n is the least order of a generator, but i numbers the varieties of that order
in the sequence of the database. Each variety page gives both.</p>
<h2 id="guarantees">What the rule guarantees</h2>
<ul class="spaced">
<li><b>One name for each variety, and one variety for each name.</b> V[n, k] always denotes the variety generated by
[n, k], and V[n, k]{OP} the variety generated by [n, k]{OP}: a name says what it names and cannot become
ambiguous.</li>
<li><b>Names never change.</b> A name depends only on its variety and on the numbering of Smallsemi: not on bases,
proofs or computations, nor on where SemiBase is hosted. Extending the census to semigroups of order seven or eight
leaves every name as it is, since each new semigroup comes after all those of order at most six; only the varieties
that no smaller semigroup generates get new names, V[7, k] or V[8, k] and their duals.</li>
<li><b>The order in the name is the generator order.</b> In V[n, k] and V[n, k]{OP}, n is the least order of a
semigroup that generates the variety. So the varieties generated by a semigroup of order at most five are exactly the
{small} whose names have n at most five.</li>
<li><b>Duals.</b> The dual of V[n, k], the variety of the opposite semigroups, is V[n, k]{OP}, and the dual of
V[n, k]{OP} is V[n, k]; V[n, k]{OP} is a name exactly when V[n, k] is not self-dual. Indeed S generates a variety
exactly when S{OP} generates its dual, so the triples that generate the two differ only in the last entry, and the
least of them share n and k. For example, the left zero semigroups form {vlink(C.SLUG['2-4'], '')} and the right zero
semigroups {vlink(C.SLUG['2-4-op'], '')}.</li>
<li><b>A semigroup need not name its own variety.</b> V[n, k] is a name only when no smaller triple generates the
same variety: {slink((6, 5762), '')} generates {vlink(C.SLUG['5-540'], '')}, for instance. The page of every
semigroup of order at most six names the varieties of its table and of its transpose.</li>
</ul>
<h2 id="find">Finding the name of the variety of a semigroup</h2>
<p><b>Order at most six.</b> Enter its Cayley table, one row per line: row i and column j hold the product of the
elements i and j, numbered from 1, or from 0 when an entry is 0. A table copied from GAP works as it is.</p>
<form class="lookup" id="lookup" data-forms="{asset('forms.js', '')}">
<textarea name="table" rows="7" spellcheck="false" autocomplete="off" aria-label="Cayley table"></textarea>
<div class="row"><button class="btn" type="submit">Find its variety</button>
<button class="btn" type="button" id="lookup-example" data-table="{example}">Example</button></div></form>
<div class="box" id="lookup-out" aria-live="polite" hidden></div>
<noscript><p class="note">The lookup needs JavaScript; the semigroup pages give the same names.</p></noscript>
<p class="note">The page renumbers the table and its transpose in every way, which identifies the semigroup [n, k] of
Smallsemi and the triple (n, k, o), and reads off the name of its variety. In GAP,
<span class="mono">IdSmallSemigroup(S)</span> gives [n, k]; then S is isomorphic to
<span class="mono">SmallSemigroup(n, k)</span>, and o = 0, or only to its opposite, and o = 1. The page of [n, k] and
names-v1.json give the names of the varieties of both.</p>
<p><b>Larger order.</b> The variety V(S) of a finite semigroup S has a name in version 1 when a semigroup T of order
at most six generates it, that is, when S and T satisfy the same identities. The finitely based varieties of the list
that contain S are those whose basis S satisfies. If V(S) is one of them, it is the least of them under inclusion;
and if they have a least one, W, then V(S) = W exactly when the generator of W satisfies every identity of S. That is
decidable: a semigroup of order m satisfies every identity of S once it satisfies those in m variables, and finitely
many of these, read off the free semigroup of V(S) on m generators (the functions from S<sup>m</sup> to S that words
define), imply all the others. If none of the {NV} is V(S), it can still be one of the four varieties without a finite
basis, V(N) for N one of L, B₂¹, A₂ᵍ and A₂¹: V(S) = V(N) exactly when each of S and N satisfies every identity of the
other, which the same test decides. Otherwise no semigroup of order at most six generates V(S), and version 1 does not
name it.</p>
<h2 id="list">The names of version 1</h2>
<p>{total} names: the {NV} varieties with a finite basis, which the <a href="varieties.html">list of varieties</a>
shows with their bases, and the four without one, {nfb}. By generator order: {counts}. {selfdual} are self-dual and
the other {total - selfdual} form {(total - selfdual) // 2} dual pairs.</p>
<p><a href="names-v1.json">names-v1.json</a> fixes them, in their order: for each name the triple and the table of
its generator, its dual and whether it has a finite basis; the names of the varieties of every semigroup of order at
most six and of its transpose; and the names of the first release that they replace.</p>
{''.join(lists)}
<h2 id="checks">How the names were found and checked</h2>
<p>Every finitely based semigroup of order at most six has a basis certified in Lean, so a semigroup lies in its
variety exactly when it satisfies that basis, and two semigroups generate the same variety exactly when each satisfies
the basis of the other. Evaluating the bases in the {len(C.SEMIGROUPS):,} semigroups of order at most six, counted up
to isomorphism, so that a semigroup and its opposite count twice unless they are isomorphic, gives the variety of each,
and so the least triple of each variety. <span class="mono">check_data.py</span> repeats this by evaluation,
independently of the satisfaction rows from which the site is built: each semigroup satisfies the basis of the generator
of its variety, that generator satisfies the basis of the semigroup, and the {NV} varieties are pairwise distinct.</p>
<p>Each of the four semigroups without a finite basis is self-dual, and the variety it generates has no finite basis,
so it is none of the {NV}. Three identities tell the four apart, so each of them is the only semigroup of order at most
six that generates its variety:</p>
{separation_table('')}
<h2 id="fixed">How the names stay fixed</h2>
<ul class="spaced">
<li>names-v1.json freezes the names of version 1. Every build of this website compares each name with it and stops if
one differs, so every copy of the site, wherever it is hosted, has the same names; the SHA-256 above identifies the
file.</li>
<li>A name is never changed, reused or withdrawn. A later version may only add names, for varieties that no semigroup
of order at most six generates, and keeps every name of version 1.</li>
<li>Should an error ever come to light, the name would keep denoting the variety of the semigroup it names, and the
correction would be recorded here, never made by renaming.</li>
<li>The first release of this site, on 2 October 2026, covered order six only and called each variety V[k] after its
least generator of order six. Those names are withdrawn: their pages lead to the new names, and names-v1.json maps all
{len(REGISTRY['legacy'])} of them.</li>
</ul>
<h2 id="cite">Citing a name</h2>
<p>For example: the variety V[5, 540] of SemiBase (names of varieties, version 1, {date},
https://nasqret.github.io/semibase-site/names.html).</p>"""
    return page("Names of varieties · SemiBase", body, "",
                "The permanent names V[n, k] of the varieties generated by the semigroups of order at most six: "
                "the rule, its guarantees, the list, and a lookup by Cayley table.", scripts=("names.js",))


def nonfinite_variety_page(k):
    name, words = NONFINITE_NAMES[k]
    family, argument, source = NONFINITE_DETAIL[k]
    label = f"V[6, {k}]"
    others = [esc(NONFINITE_NAMES[j][0]) for j in NONFINITE if j != k]
    body = f"""<h1>Variety {label} <span class="badge nfb">no finite basis</span></h1>
<p class="lead">The variety generated by {slink((6, k), named=False)}, {esc(words)}: all semigroups that satisfy every
identity of {esc(name)}. It has no finite basis. It is self-dual, since {esc(name)} is anti-isomorphic to itself, and
no other semigroup of order at most six generates it: the variety of a finitely based semigroup has a finite basis,
and the identities below tell it apart from the varieties of {', '.join(others[:-1])} and {others[-1]}.</p>
<h2>No finite basis</h2>
<div class="box nfb"><p>For every n, the identity</p><p class="formula">{esc(family)}</p><p>holds in {esc(name)}.
{esc(argument)} A finite set of identities uses boundedly many variables, so it misses one of these identities and is
not a basis.</p><p class="note">Argument: {esc(source)}. The Lean theorem is on the page of
{slink((6, k), named=False)}; see also <a href="../nonfinite.html">the four semigroups without a finite basis</a>.</p></div>
<h2>The four varieties without a finite basis</h2>
<p>{', '.join(nlink(j) for j in NONFINITE[:-1])} and {nlink(NONFINITE[-1])} are distinct: each pair differs on one of
these identities.</p>
{separation_table()}
<h2>Among the {NV} finitely based varieties</h2>
<p>{esc(name)} lies in none of them, so neither does this variety. Which of them lie in it is not decided here:
without a finite basis there is no basis to evaluate.</p>
<p class="note">The name is permanent: [6, {k}] is the only generator of order at most six. See
<a href="../names.html">how the varieties are named</a>.</p>"""
    return page(f"Variety {label} · SemiBase", body, "../",
                f"The variety {label}, generated by {name}: no finite basis.")


def index_page():
    sizes = Counter(nvars(FEWEST_VARS[v]["identities"]) for v in range(NV))
    peak = max(sizes.values())
    bars = "".join(f'<span class="lab">{s}</span><div><div class="bar" style="width:{100 * c / peak:.1f}%"></div></div>'
                   f'<span class="lab">{c:,}</span>' for s, c in sorted(sizes.items()))
    biggest = max(CLASSES, key=lambda key: OWN[key])
    longest = max(CLASS_BASIS, key=lambda key: (len(BASIS[CLASS_BASIS[key]]), -key[0], -key[1]))
    longest_short = max(range(NV), key=lambda v: (len(FEWEST_IDS[v]["identities"]), -v))
    widest = max(range(NV), key=lambda v: (len(GENS[v]), -v))
    optimal = sum(1 for v in range(NV) if OPTIMAL[v])
    found = sum(1 for v in range(NV) if FEWEST_VARS[v]["kind"] == "search")
    body = f"""<h1>Identity bases of the semigroups of orders one to six</h1>
<p class="lead">A census of the {len(CLASSES):,} semigroups of orders one to six, counted up to isomorphism and
anti-isomorphism as in GAP Smallsemi: {NLOW:,} of order at most five and {N6:,} of order six. All of them except four
have a finite identity basis, and every case is proved in Lean: an explicit basis for each of the
{len(CLASS_BASIS):,} finitely based semigroups, for most of which only the existence of a finite basis was known
before, and a proof for the other four that no finite basis exists.</p>
<form class="big" onsubmit="return sbGo(this)" data-root=""><input name="q" placeholder="Go to a semigroup: 3842, [5, 415], L, B2, C8" aria-label="Go to a semigroup"></form>
<div class="numbers"><div><b>{len(CLASSES):,}</b><span>semigroups of orders one to six</span></div>
<div><b>{len(CLASS_BASIS):,}</b><span>finitely based, each with a basis certified in Lean</span></div>
<div><b>4</b><span>without a finite basis, all of order six, proved in Lean</span></div>
<div><b>{len(BASIS):,}</b><span>distinct certified bases</span></div>
<div><b>{len(C.NAMES)}</b><span>varieties they generate, counting duals, each with a permanent name</span></div>
<div><b>{optimal}</b><span>of the {NV} finitely based ones with a basis in as few variables as possible</span></div></div>
<h2>Explore</h2>
<ul class="explore">
<li><a href="browse.html">Browse</a> all {len(CLASSES):,} semigroups and filter them by order, structure, basis and proof.</li>
<li><a href="varieties.html">Varieties</a>: the {NV} varieties the finitely based semigroups and their transposes
generate, as a list or as an <a href="varieties.html#graph">interactive graph of their inclusions</a>.</li>
<li><a href="names.html">Names</a>: the rule that names the {len(C.NAMES)} varieties, fixed once and for all, and the
name of the variety of any Cayley table of order at most six.</li>
<li><a href="nonfinite.html">No finite basis</a>: L, B₂¹, A₂ᵍ and A₂¹, and why no finite set of identities suffices.</li>
<li><a href="s/1.html" onclick="return sbRandom('')">A random semigroup</a>.</li>
</ul>
<h2>Worth a look</h2>
<ul class="explore">
<li>{slink((6, 3842), '')}, the semigroup C₈ of Lee and Zhang: finitely based, two table entries away from the nonfinitely based L.</li>
<li>{slink((5, 415), '')} and {slink((5, 868), '')}: finitely based; adjoining an identity to either gives a semigroup of order six without a finite basis.</li>
<li>{vlink(C.SLUG['5-540'], '')}: the variety V(5,140) of the database of Araújo et al., with a basis in three variables where the certified one uses four.</li>
<li>{slink(biggest, '')}: the largest proof, {OWN[biggest]:,} lines of Lean that the proof of no other class uses.</li>
<li>{slink(longest, '')}: the longest certified basis, {len(BASIS[CLASS_BASIS[longest]]):,} identities, which reduce to {len(FEWEST_IDS[CLASS_VAR[longest]]['identities'])}.</li>
<li>{vlink(longest_short, '')}: the variety whose basis with the fewest identities is longest, with {len(FEWEST_IDS[longest_short]['identities'])} identities.</li>
<li>{vlink(widest, '')}: the variety with the most generators, {len(GENS[widest]):,} semigroups of order at most six.</li>
</ul>
<h2>How many variables do the bases need?</h2>
<p class="note">The {NV} finitely based varieties by the number of variables of their basis in the fewest variables: the largest
number of distinct variables in one identity, which decides how long it takes to check whether a semigroup lies in
the variety. For {optimal} varieties no basis in fewer variables exists. {found} of the bases in the fewest variables
were found by a search for this census, beyond the certified bases and their reductions.</p>
<div class="bars">{bars}</div>
<h2>On each page</h2>
<p>For each semigroup: the Cayley table and its structure; the basis of its variety in the fewest variables and the
basis with the fewest identities, and the basis certified in Lean; the Lean theorem and the size of its proof; the
variety it generates and the one its transpose generates, with the varieties directly above and below and the other
semigroups that generate it; and the tables that differ from it in one or two entries.
<a href="about.html">About</a> says what is proved in Lean and what is not.</p>"""
    return page("SemiBase: identity bases of the semigroups of orders one to six", body, "",
                "Every semigroup of order at most six with its identity bases, Lean proof and variety.")


def about_page():
    counts = Counter(KIND[key] for key in CLASSES if key[0] == 6)
    lower_counts = Counter(KIND[key] for key in CLASSES if key[0] < 6)
    kinds = "".join(f"<tr><td>{esc(name)}</td><td class=\"num\">{counts[name]:,}</td>"
                    f"<td class=\"num\">{lower_counts[name]:,}</td><td>{esc(KIND_SUMMARY[name])}</td></tr>"
                    for name in KIND_NAMES)
    optimal = sum(1 for v in range(NV) if OPTIMAL[v])
    found = sum(1 for v in range(NV) if FEWEST_VARS[v]["kind"] == "search")
    selfdual = sum(1 for var in VARIETIES if var["self_dual"])
    same = sum(1 for e in LOWER_ENDPOINT.values() if e["same"])
    models = sum(1 for v in range(NV) if BOUND_INFO[v].get("model"))
    body = f"""<h1>About the census</h1>
<h2>What is proved in Lean</h2>
<p>For each of the {len(CLASSES):,} semigroups of orders one to six in GAP Smallsemi 0.7.2, a theorem: either a finite
list of identities is a basis, that is, the identities hold and every identity of the semigroup follows from them by
equational logic, or no finite basis exists. The Lean kernel checks every proof, and the proofs use no axioms beyond
propositional extensionality, quotient soundness and choice.</p>
<ul><li>Order six: one theorem collects the {N6:,} cases, <span class="mono">SemiBase.order6_classification</span>.
Sources, build instructions and the checks of the tables: <a href="{REPO_URL}">nasqret/semibase-order6</a>, archived on
Zenodo as <a href="https://doi.org/{DOI}">doi:{DOI}</a>.</li>
<li>Orders one to five: a theorem for each of the {NLOW:,} semigroups, from the same campaign, audited in both
orientations with the Lean kernel; for order five a second replay read the bases back from Lean. {PUBLIC_LOWER:,} of
these theorems are in the public repository, which builds them as part of the proofs of order six ({same:,} in the
very revision the audit checked); the semigroup pages link them. The other {NLOW - PUBLIC_LOWER:,} are in the
repository of the campaign, which is not public.</li></ul>
<h2>What is not proved in Lean</h2>
<ul><li>The bases with the fewest identities come from the certified ones by removing identities that follow from the
others, with the prover Vampire, and the bases in the fewest variables partly from a search for this census, also
checked with Vampire (see below). Their equivalence with the certified bases rests on Vampire's proofs.</li>
<li>That Smallsemi lists every semigroup of order at most six once, up to isomorphism and anti-isomorphism, is taken
from GAP and the literature.</li></ul>
<p>The inclusions between the varieties need no prover: a variety V(S) lies in a variety W exactly when S satisfies a
basis of W, and evaluating the certified basis of W in the table of S decides it. So every inclusion among the {NV}
varieties is decided, and two semigroups generate the same variety exactly when each satisfies the basis of the
other.</p>
<h2>Duals and smaller generators</h2>
<p>Smallsemi counts a semigroup and its opposite, with the transposed table, once. Their varieties are dual: an identity
holds in one exactly when it holds read backwards in the other. The census lists both. V[n, k] is the variety generated
by [n, k] and V[n, k]{OP} the variety generated by its transpose, and each variety is named after its generator of least
order, then least number, a table before its transpose. So the {NV} finitely based varieties come in {selfdual}
self-dual ones and {(NV - selfdual) // 2} dual pairs V[n, k] and V[n, k]{OP}, and the name of a variety tells the least
order of a single semigroup that generates it. The lists of generators and of members of a variety include the
transposes, marked {OP}. <a href="names.html">Names</a> fixes these names once and for all, with the four varieties
without a finite basis, and finds the name of the variety of any table of order at most six.</p>
<p>The {len(SGV)} varieties generated by a semigroup of order at most five are exactly the varieties of the database of
Araújo, Araújo, Cameron, Lee and Raminhos, which also counts duals separately; each variety page gives the name it has
there, such as V(5,140). The bases of the database hold in exactly the same tables of order at most six, and their
transposes, as the bases of this census (checked by <span class="mono">prep/prepare_lower.py</span>).</p>
<h2>Bases in few variables</h2>
<p>To decide whether a semigroup of order n satisfies an identity in k variables takes about n<sup>k</sup> evaluations,
so for testing membership in a variety a basis in few variables is better than a basis of few identities. Each variety
page shows a basis in the fewest variables known, counting the largest number of distinct variables in one identity,
and a basis with the fewest identities when it is a different one.</p>
<ul><li>Lower bounds: if a semigroup T lies outside a variety V but satisfies every identity of V in k variables, then
no basis of V uses only k variables. Among the tables of order at most six, T qualifies when every subsemigroup of T
generated by k elements lies in V. Beyond them, the finite model builder of Vampire found {models} larger
semigroups that satisfy the rules of a complete rewriting system of the free object of V on k generators, and so
every identity of V in k variables, without lying in V. The variety pages show the witness of each bound, and
<span class="mono">check_data.py</span> checks every one by evaluation.</li>
<li>Upper bounds: the identities of V in k variables are those of the free object of V on k generators, the functions
that words define on the generator of V. A complete rewriting system of that free object gives finitely many of them;
when Vampire derives a certified basis from some of them, those are a basis, and the redundant ones are removed, again
with Vampire.</li></ul>
<p>For {optimal} of the {NV} varieties the two bounds meet, so the basis shown uses as few variables as possible.
{found} of the bases in the fewest variables were found by the search, among them the basis
x⁴yz ≈ xyz, x³ ≈ y³, xy ≈ yx of V(5,140) in three variables, where the certified basis x³yzt ≈ yzt, xy ≈ yx uses
four.</p>
<h2>What was known</h2>
<p>That every semigroup of order at most five is finitely based was shown by Trahtman (1983), without listing the
bases. That exactly four semigroups of order six are not finitely based was shown by Lee, Li and Zhang (2012), and Lee
and Zhang (2015) treat the semigroups of order six in detail. For most of the finitely based ones, 14,534 of the 14,600
semigroups of order six without an identity element, finite basability follows there from sufficient conditions, which
show that a finite basis exists without writing one down. The census gives an explicit basis for every one of them.
Araújo, Araújo, Cameron, Lee and Raminhos (2023) survey the varieties generated by the semigroups of order at most
five, with bases.</p>
<h2>How the proofs work</h2>
<p>Most proofs are transfers. If a semigroup S with a certified basis lies in the variety of a semigroup T, and T
satisfies the basis of S, then every identity of T holds in S and so follows from the basis: the basis of S is a basis
of T. The transfers differ in how S lies in the variety of T. Each semigroup page names the method of its proof.</p>
<div class="scroll"><table class="list"><thead><tr><th>Proof</th><th class="num">Order 6</th><th class="num">Orders 1–5</th><th>Idea</th></tr></thead><tbody>{kinds}</tbody></table></div>
<h2>Conventions</h2>
<p>Elements are numbered from 1 as in Smallsemi (from 0 in Lean), and a table gives the product of the row element and
the column element. An identity u ≈ v is written with the variables x, y, z, t, … in order of first occurrence and with
powers for repeated letters, so x²yx stands for xxyx. [n, k] is the semigroup number k of order n in Smallsemi. A class
that is not self-dual stands for two semigroups, a table and its transpose; a basis read backwards is a basis of the
transpose, a lemma in Lean (<span class="mono">BasisFor.oppositeReversed</span>). The links to Lean point to commit
<span class="mono">{COMMIT[:7]}</span> of the repository. The variety pages of the first release, named after
generators of order six, lead to the new names.</p>
<h2>Credits</h2>
<p>Created and curated by <a href="https://github.com/nasqret">@nasqret</a>. The Lean proofs were written by
language-model agents in a campaign from June to September 2026, described in <i>{esc(PAPER)}</i>. The reduced bases
of order six were computed with Vampire by the <span class="mono">bases-min</span> tools of Mikoláš Janota, which also
supplied the satisfaction rows over all tables of order at most six. The tables come from GAP Smallsemi by A. Distler
and J. D. Mitchell. Thanks to E. W. H. Lee for comments on the bases and on duality. The source of this website is
<a href="{SITE_URL}">nasqret/semibase-site</a>; the same build is also served at
<a href="https://bnaskrecki.faculty.wmi.amu.edu.pl/semigroups6/">bnaskrecki.faculty.wmi.amu.edu.pl/semigroups6</a>.</p>
<h2>References</h2><ul class="refs">
<li>J. Araújo, J. P. Araújo, P. J. Cameron, E. W. H. Lee and J. Raminhos, A survey on varieties generated by small semigroups and a companion website, J. Algebra 635 (2023) 698–735; database <a href="{SGV_URL}">sgv.dm.fct.unl.pt</a>.</li>
<li>A. Distler and J. D. Mitchell, Smallsemi, a library of small semigroups, GAP package, version 0.7.2.</li>
<li>E. W. H. Lee, J. R. Li and W. T. Zhang, Minimal non-finitely based semigroups, Semigroup Forum 85 (2012) 577–580.</li>
<li>E. W. H. Lee and W. T. Zhang, Finite basis problem for semigroups of order six, LMS J. Comput. Math. 18 (2015) 1–129.</li>
<li>P. Perkins, Bases for equational theories of semigroups, J. Algebra 11 (1969) 298–314.</li>
<li>M. V. Sapir, Problems of Burnside type and the finite basis property in varieties of semigroups, Math. USSR-Izv. 30 (1988) 295–314.</li>
<li>A. N. Trahtman, The finite basis question for semigroups of order less than six, Semigroup Forum 27 (1983) 387–389.</li>
<li>A. N. Trahtman, Some finite infinitely basable semigroups, Ural. Gos. Univ. Mat. Zap. 14 (1987) 128–131.</li>
<li>M. V. Volkov, The finite basis problem for finite semigroups, Sci. Math. Jpn. 53 (2001) 171–199.</li>
<li>W. T. Zhang and Y. F. Luo, A new example of a minimal nonfinitely based semigroup, Bull. Aust. Math. Soc. 84 (2011) 484–491.</li></ul>
<p class="note">Built {TODAY} from commit <span class="mono">{SITE_COMMIT[:12] or 'unknown'}</span> of the website and commit
<span class="mono">{COMMIT}</span> of the Lean repository.</p>"""
    return page("About · SemiBase", body, "")


def build_record():
    """A record of the build: the commits it was built from and a hash of every file, to compare two copies."""
    entries = []
    for directory, _, names in os.walk(OUT):
        for name in names:
            path = os.path.relpath(os.path.join(directory, name), OUT)
            if path == "build.json":
                continue
            with open(os.path.join(OUT, path), "rb") as handle:
                entries.append(f"{hashlib.sha256(handle.read()).hexdigest()}  {path}")
    entries.sort(key=lambda line: line[66:])
    content = hashlib.sha256("\n".join(entries).encode()).hexdigest()
    return {"site_commit": SITE_COMMIT, "lean_commit": COMMIT, "built": TODAY, "files": len(entries),
            "content_sha256": content}


def main():
    if os.path.exists(OUT):
        shutil.rmtree(OUT)
    os.makedirs(os.path.join(OUT, "assets"))
    log("assets ...")
    for name in ("style.css", "browse.js", "graph.js", "names.js", "icon.svg"):
        shutil.copy(os.path.join(HERE, "assets", name), os.path.join(OUT, "assets", name))
    with open(os.path.join(HERE, "assets", "site.js"), encoding="utf-8") as handle:
        site_js = handle.read()
    assert "/*VARIETIES*/[]" in site_js and "/*NAMES*/{}" in site_js
    site_js = site_js.replace("/*VARIETIES*/[]", json.dumps([e["slug"] for e in C.NAMES], separators=(",", ":")))
    site_js = site_js.replace("/*NAMES*/{}", json.dumps(SEARCH_NAMES, separators=(",", ":")))
    site_js = site_js.replace("/*COUNTS*/[]", json.dumps([COUNT[n] for n in C.ORDERS]))
    write("assets/site.js", site_js)
    write("assets/data.js", data_js())
    write("assets/graph-data.js", graph_data_js())
    write("assets/forms.js", forms_js())
    for name in sorted(os.listdir(os.path.join(OUT, "assets"))):
        with open(os.path.join(OUT, "assets", name), "rb") as handle:
            ASSET_VERSION[name] = hashlib.sha256(handle.read()).hexdigest()[:10]
    log("pages ...")
    for key in CLASSES:
        write(f"s/{sslug(key)}.html", semigroup_page(key))
    for v in range(NV):
        write(f"v/{VARIETIES[v]['slug']}.html", variety_page(v))
    for old, v in MOVED.items():
        assert not os.path.exists(os.path.join(OUT, "v", f"{old}.html")), old
        write(f"v/{old}.html", redirect_page(f"{VARIETIES[v]['slug']}.html", vlabel(v)))
    for k in NONFINITE:
        assert not os.path.exists(os.path.join(OUT, "v", f"{k}.html")), k
        write(f"v/{k}.html", nonfinite_variety_page(k))
    for b in BASIS:
        write(f"b/{b}.html", basis_page(b))
    write("index.html", index_page())
    write("browse.html", browse_page())
    write("varieties.html", varieties_page())
    write("nonfinite.html", nonfinite_page())
    write("about.html", about_page())
    write("names.html", names_page())
    with open(os.path.join(OUT, "names-v1.json"), "wb") as handle:
        handle.write(NAMES_BYTES)
    record = build_record()
    write("build.json", json.dumps(record, indent=1) + "\n")
    missing_census = [k for k in range(1, N6 + 1) if census_ref(k)[1] is None or catalogue_ref(k)[1] is None]
    print(f"{len(CLASSES)} semigroup pages, {NV} + {len(NONFINITE)} variety pages ({len(MOVED)} old names redirected), "
          f"{len(BASIS)} basis pages; {PUBLIC_LOWER} of {NLOW} theorems of order at most five public")
    print(f"endpoint lines not found: {len(MISSING)} {MISSING[:10]}; census lines not found: {len(missing_census)}")
    print(f"build {record['content_sha256'][:16]} over {record['files']} files")


if __name__ == "__main__":
    main()
