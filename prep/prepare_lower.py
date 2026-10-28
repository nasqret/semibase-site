#!/usr/bin/env python3
"""Prepare the data of the orders one to five for the census site, from inputs that the site build does not read.

    python3 prep/prepare_lower.py --bases-min BASES_MIN --campaign CAMPAIGN [--sgv SGV_HTML]

BASES_MIN is a checkout of the bases-min tools of M. Janota. It supplies the GAP Smallsemi tables of orders one to
six (gap/), the Lean-sealed bases of order five (data/order5-seal-20260829/), and the satisfaction rows of the
order-five and order-six bases over the pool of all tables of orders one to six and their transposes
(data/order6-lower-order-20261001/).

CAMPAIGN holds the records of the SemiBase campaign for the orders one to five, from its repository:
research/formalization/l5_source_theorem_registry.json (the Lean theorem of each class, audited),
research/formalization/bindings/ (the identities of each certified basis), research/data/bases.json and
research/data/catalogue.json (the tables Lean was given).

SGV_HTML is the page https://www.sgv.dm.fct.unl.pt/ of the database of Araújo, Araújo, Cameron, Lee and Raminhos,
saved as HTML. Only the names V(n,i) of its varieties and their generators are kept, to cross-reference them.

Writes, in data/:
  lower-classes-v1.json      every class of order one to five: table, self-duality, certified basis, Lean theorem
  rows-lower-bases-v1.json   the satisfaction rows of the order one to four bases over the pool of bases-min
  sgv-names-v1.json          the names V(n,i) of the database, each with the pool table of its generator
and copies the two row files of bases-min (orders five and six) next to them.
"""
import argparse
import glob
import hashlib
import html as htmllib
import itertools
import json
import os
import re
import shutil
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "data")


def load(path):
    with open(path, encoding="utf-8") as handle:
        return json.load(handle)


def dump(obj, name):
    path = os.path.join(DATA, name)
    with open(path, "w", encoding="utf-8") as handle:
        json.dump(obj, handle, separators=(",", ":"), ensure_ascii=False)
        handle.write("\n")
    print(f"wrote {name}: {os.path.getsize(path):,} bytes")


# ------------------------------------------------------------------ identities


def parse_identity(text):
    """'xxy = yx' -> {'lhs': [0, 0, 1], 'rhs': [1, 0]}, variables numbered by first occurrence."""
    left, right = (side.strip() for side in text.split("="))
    names = {}
    for ch in left + right:
        if not ch.isalpha():
            raise ValueError(text)
        names.setdefault(ch, len(names))
    return {"lhs": [names[c] for c in left], "rhs": [names[c] for c in right]}


def canonical_identity(e):
    """The same identity up to renaming the variables and swapping the sides."""
    def renamed(a, b):
        names = {}
        for v in a + b:
            names.setdefault(v, len(names))
        return tuple(names[v] for v in a), tuple(names[v] for v in b)
    return min(renamed(e["lhs"], e["rhs"]), renamed(e["rhs"], e["lhs"]))


def canonical_basis(ids):
    return tuple(sorted(canonical_identity(e) for e in ids))


def reverse_identity(e):
    return {"lhs": e["lhs"][::-1], "rhs": e["rhs"][::-1]}


# ------------------------------------------------------------------ evaluation


def satisfied(identities, tables):
    """For a stack of tables of one order (M, n, n), 0-based, which satisfy every identity."""
    M, n, _ = tables.shape
    alive = np.ones(M, dtype=bool)
    rows_all = np.arange(M)
    for e in sorted(identities, key=lambda e: (len(set(e["lhs"] + e["rhs"])), len(e["lhs"]) + len(e["rhs"]))):
        idx = rows_all[alive]
        if not len(idx):
            break
        variables = sorted(set(e["lhs"] + e["rhs"]))
        pos = {v: i for i, v in enumerate(variables)}
        A = np.indices((n,) * len(variables), dtype=np.int8).reshape(len(variables), -1)
        chunk = max(1, int(2e7 // A.shape[1]))
        good = np.ones(len(idx), dtype=bool)
        for start in range(0, len(idx), chunk):
            part = idx[start:start + chunk]
            T = tables[part]
            r = np.arange(len(part))[:, None]

            def value(word):
                out = np.broadcast_to(A[pos[word[0]]], (len(part), A.shape[1])).copy()
                for letter in word[1:]:
                    out = T[r, out, A[pos[letter]][None, :]]
                return out
            good[start:start + chunk] = (value(e["lhs"]) == value(e["rhs"])).all(axis=1)
        alive[idx[~good]] = False
    return alive


# ------------------------------------------------------------------ isomorphism


_perms = {}


def canonical_table(table):
    """The lexicographically least relabelling of a 0-based table: equal exactly for isomorphic semigroups."""
    T = np.asarray(table, dtype=np.int8)
    n = T.shape[0]
    if n not in _perms:
        P = np.array(list(itertools.permutations(range(n))), dtype=np.int8)
        Q = np.argsort(P, axis=1).astype(np.int8)        # Q[p][P[p][i]] = i
        _perms[n] = (P, Q)
    P, Q = _perms[n]
    # relabelled[p][i][j] = Q[p][ T[P[p][i]][P[p][j]] ]
    relabelled = np.take_along_axis(Q[:, None, :].repeat(n, 1),
                                    T[P[:, :, None], P[:, None, :]].astype(np.int64), axis=2)
    flat = relabelled.reshape(len(P), -1)
    best = flat[np.lexsort(flat.T[::-1])[0]]
    return bytes([n]) + best.tobytes()


# ------------------------------------------------------------------ main


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--bases-min", required=True)
    parser.add_argument("--campaign", required=True)
    parser.add_argument("--sgv")
    parser.add_argument("--lean", default=os.path.join(HERE, "..", "..", "semibase-order6"),
                        help="a checkout of semibase-order6, for the order-six tables")
    args = parser.parse_args()
    bm, cp = args.bases_min, args.campaign

    # Tables: the GAP export of bases-min, checked against the tables Lean was given.
    gap = {}
    for path in sorted(glob.glob(os.path.join(bm, "gap", "s[1-6]_*.json"))):
        n = int(os.path.basename(path)[1])
        for record in load(path):
            gap[(n, record["index"])] = record["table"]
    counts = {n: sum(1 for key in gap if key[0] == n) for n in range(1, 7)}
    assert counts == {1: 1, 2: 4, 3: 18, 4: 126, 5: 1160, 6: 15973}, counts
    campaign_catalogue = load(os.path.join(cp, "research", "data", "catalogue.json"))["semigroups"]
    assert len(campaign_catalogue) == 1309
    SELF_DUAL = {}
    for record in campaign_catalogue:
        key = tuple(record["smallsemi_id"])
        assert gap[key] == record["table"], key
        SELF_DUAL[key] = record["self_dual"]
    order6 = load(os.path.join(args.lean, "research", "order6", "catalogue.json"))["semigroups"]
    for record in order6:
        assert gap[(6, record["smallsemi_id"][1])] == record["table"]
    print("tables: GAP export = campaign catalogue (orders 1-5) = semibase-order6 catalogue (order 6)")

    # Self-duality, recomputed: a class is self-dual when its table is isomorphic to its transpose.
    for key, flag in SELF_DUAL.items():
        T = np.array(gap[key]) - 1
        assert (canonical_table(T) == canonical_table(T.T)) == flag, key

    # The certified bases of order five, read back from Lean by the bases-min seal.
    seal5 = load(os.path.join(bm, "data", "order5-seal-20260829", "sealed-bases-v1.json"))
    seal_basis, seal_record = {}, {}
    for basis in seal5["bases"]:
        for c in basis["classes"]:
            assert c["proof_orientation"] in ("direct", "both")      # both: a symmetric table
            seal_basis[(5, int(c["semigroup_id"].split("_")[1]))] = (basis["basis_id"], basis["identities"])
            seal_record[(5, int(c["semigroup_id"].split("_")[1]))] = c
    assert len(seal_basis) == 1160

    # The campaign records: the audited Lean theorem of each class, and the identities of its basis.
    registry = {r["semigroup_id"]: r for r in
                load(os.path.join(cp, "research", "formalization", "l5_source_theorem_registry.json"))["records"]}
    assert len(registry) == 1309
    bases_json = {b["semigroup_id"]: b for b in load(os.path.join(cp, "research", "data", "bases.json"))["bases"]}
    classes, agree = [], 0
    for key in sorted(gap):
        n, k = key
        if n == 6:
            continue
        sid = f"S{n}_{k}"
        binding = load(os.path.join(cp, "research", "formalization", "bindings", f"{sid}.json"))
        texts = binding.get("representative_identities") or bases_json[sid]["identities"]
        ids = [parse_identity(t) for t in texts]
        if n == 5:
            basis_id, sealed = seal_basis[key]
            assert canonical_basis(sealed) == canonical_basis(ids), sid   # the records say what Lean says
            agree += 1
            ids = [{"lhs": e["lhs"], "rhs": e["rhs"]} for e in sealed]
        else:
            basis_id = "lb-" + hashlib.sha256(repr(canonical_basis(ids)).encode()).hexdigest()[:16]
        r = registry[sid]
        record = {
            "order": n, "index": k, "table": gap[key], "self_dual": SELF_DUAL[key], "basis_id": basis_id,
            "identities": ids, "theorem": r["representative_theorem"], "module": r["lean_module"],
            "type": r["representative_type"], "opposite_theorem": r["opposite_theorem"],
            "source_files": [{"path": f["path"], "sha256": f["sha256"]} for f in r["source_files"]]}
        if n == 5:     # the endpoint that the bases-min seal replayed, when it differs from the registry's
            c = seal_record[key]
            if (c["theorem"], c["module"]) != (record["theorem"], record["module"]):
                record["sealed_endpoint"] = {"theorem": c["theorem"], "module": c["module"], "source": c["source"],
                                             "type": c["checked_type"]}
        classes.append(record)
    print(f"bases: {agree} order-five records agree with the bases read back from Lean")

    # Every class satisfies its basis, in the orientation of its table.
    for c in classes:
        T = np.array(c["table"], dtype=np.int8)[None] - 1
        assert satisfied(c["identities"], T)[0], (c["order"], c["index"])
        if not c["self_dual"]:
            assert satisfied([reverse_identity(e) for e in c["identities"]], T.transpose(0, 2, 1).copy())[0]
    print("evaluation: every class of order 1-5 satisfies its certified basis")

    # The pool of bases-min: all tables of orders one to six and their transposes, a symmetric table once.
    rows5 = load(os.path.join(bm, "data", "order6-lower-order-20261001", "rows-order5-bases.json"))
    rows6 = load(os.path.join(bm, "data", "order6-lower-order-20261001", "rows-order6-bases.json"))
    labels = rows5["pool_labels"]
    assert labels == rows6["pool_labels"]

    def model(label):
        number = int(label.split(":")[1])
        if number < 1000000:
            return (6, number % 100000, number // 100000)
        n, rest = divmod(number, 1000000)
        return (n, rest % 500000, rest // 500000)
    MODELS = [model(label) for label in labels]
    tables = []
    for n, k, o in MODELS:
        T = np.array(gap[(n, k)], dtype=np.int8) - 1
        tables.append(T.T.copy() if o else T)
    for (n, k, o), T in zip(MODELS, tables):
        if o == 0:
            assert ((n, k, 1) in set(MODELS)) == (not np.array_equal(T, T.T)), (n, k)
    print(f"pool: {len(MODELS):,} tables")

    # The bit order of the rows of bases-min: bit m of the hexadecimal number is pool table m.
    def bits(hexstring):
        value = int(hexstring, 16)
        return np.array([(value >> m) & 1 for m in range(len(MODELS))], dtype=bool)
    index = {m: i for i, m in enumerate(MODELS)}
    for basis in seal5["bases"][:20]:
        row = bits(rows5["rows"][basis["basis_id"]])
        for c in basis["classes"]:
            assert row[index[(5, int(c["semigroup_id"].split("_")[1]), 0)]]

    # Spot check of the rows of bases-min by evaluation.
    by_order = {}
    for i, (n, k, o) in enumerate(MODELS):
        by_order.setdefault(n, []).append(i)
    stacks = {n: np.stack([tables[i] for i in members]) for n, members in by_order.items()}
    rng = np.random.default_rng(20261028)
    seal6 = {b["basis_id"]: b["identities"] for b in load(os.path.join(HERE, "..", "data", "sealed-bases-v1.json"))["bases"]}
    checked = 0
    for source, store in ((rows5["rows"], {b["basis_id"]: b["identities"] for b in seal5["bases"]}), (rows6["rows"], seal6)):
        for basis_id in rng.choice(sorted(store), size=25, replace=False):
            ids = store[basis_id]
            if max(len(set(e["lhs"] + e["rhs"])) for e in ids) > 5 or len(ids) > 60:
                continue
            row = bits(source[basis_id])
            for n in (1, 2, 3, 4, 5):
                members = by_order[n]
                assert np.array_equal(satisfied(ids, stacks[n]), row[members]), (basis_id, n)
            checked += 1
    print(f"rows: {checked} bases-min rows of bases in at most five variables agree with evaluation on orders 1-5")

    # Rows of the bases of orders one to four over the whole pool.
    lower = {}
    for c in classes:
        if c["order"] <= 4:
            lower.setdefault(c["basis_id"], c["identities"])
    rows_lower = {}
    for basis_id, ids in sorted(lower.items()):
        row = np.zeros(len(MODELS), dtype=bool)
        for n, members in by_order.items():
            row[members] = satisfied(ids, stacks[n])
        rows_lower[basis_id] = format(sum(1 << int(m) for m in np.nonzero(row)[0]), "x")
        print(f"  row of {basis_id}: {int(row.sum()):,} tables", file=sys.stderr)
    dump({"record_type": "pool_satisfaction_rows", "pool_labels": labels, "rows": rows_lower,
          "note": "bit m is set when the basis holds in pool table m; computed by prep/prepare_lower.py"},
         "rows-lower-bases-v1.json")
    for name in ("rows-order5-bases.json", "rows-order6-bases.json"):
        shutil.copy(os.path.join(bm, "data", "order6-lower-order-20261001", name), os.path.join(DATA, name))
        print(f"copied {name}")

    dump({"record_type": "semibase_lower_classes", "orders": [1, 2, 3, 4, 5],
          "sources": {"tables": "GAP Smallsemi 0.7.2 via bases-min gap/; equal to the tables the Lean proofs use",
                      "order5_bases": "bases-min data/order5-seal-20260829/sealed-bases-v1.json (read back from Lean)",
                      "lower_bases": "SemiBase campaign, research/formalization/bindings (gate L5)",
                      "theorems": "SemiBase campaign, research/formalization/l5_source_theorem_registry.json"},
          "classes": classes}, "lower-classes-v1.json")

    if args.sgv:
        sgv_names(args.sgv, gap, MODELS, labels)


def sgv_names(path, gap, MODELS, labels):
    """The names V(n,i) of the database, each matched to the pool table of its primitive generator."""
    with open(path, encoding="utf-8", errors="replace") as handle:
        text = handle.read()
    canon = {}
    for i, (n, k, o) in enumerate(MODELS):
        if n <= 5:
            T = np.array(gap[(n, k)], dtype=np.int8) - 1
            canon.setdefault(canonical_table(T.T if o else T), labels[i])
    starts = [m.start() for m in re.finditer(r'<tr id="V\d+">', text)]
    names = []
    for s, e in zip(starts, starts[1:] + [len(text)]):
        chunk = text[s:e]
        n, i = map(int, re.search(r"varid_link\((\d+),(\d+)\)", chunk).groups())
        if n > 5:
            continue
        table = [[int(x) - 1 for x in re.findall(r">(\d+)</td>", row)]
                 for row in re.findall(r"<tr>(.*?)</tr>", re.search(r'<table class="mtable">(.*?)</table>', chunk, re.S).group(1), re.S)]
        label = canon.get(canonical_table(np.array(table, dtype=np.int8)))
        assert label, (n, i)
        names.append({"name": f"V({n},{i})", "order": n, "number": i, "generator": label})
    assert len(names) == 220, len(names)
    check_sgv_bases(text, names, MODELS, labels, gap)
    dump({"record_type": "sgv_variety_names", "source": "https://www.sgv.dm.fct.unl.pt/",
          "reference": "J. Araújo, J. P. Araújo, P. J. Cameron, E. W. H. Lee and J. Raminhos, A survey on varieties "
                       "generated by small semigroups and a companion website, J. Algebra 635 (2023) 698-735",
          "names": names}, "sgv-names-v1.json")


def parse_sgv_identity(text):
    """'x<sup>4</sup>ab &asymp; xab' -> {'lhs': [0, 0, 0, 0, 1, 2], 'rhs': [0, 1, 2]}."""
    def word(t):
        out = []
        for m in re.finditer(r"([a-z])(?:<sup>(\d+)</sup>)?", t.strip()):
            out += [m.group(1)] * int(m.group(2) or 1)
        return out
    left, right = text.split("&asymp;")
    lw, rw = word(left), word(right)
    names = {}
    for ch in lw + rw:
        names.setdefault(ch, len(names))
    return {"lhs": [names[c] for c in lw], "rhs": [names[c] for c in rw]}


def check_sgv_bases(text, names, MODELS, labels, gap):
    """The basis the database gives for each variety holds in exactly the pool tables in which the certified basis of
    its generator holds: the same tables of order at most six and transposes. Prints the result; the bases of the
    database are not kept."""
    rows = {}
    for name in ("rows-order5-bases.json", "rows-order6-bases.json", "rows-lower-bases-v1.json"):
        rows.update(load(os.path.join(DATA, name))["rows"])
    classes = {(c["order"], c["index"]): c for c in load(os.path.join(DATA, "lower-classes-v1.json"))["classes"]}
    index = {m: i for i, m in enumerate(MODELS)}
    op = np.array([index.get((n, k, 1 - o), i) for i, (n, k, o) in enumerate(MODELS)])
    by_order = {}
    for i, (n, k, o) in enumerate(MODELS):
        by_order.setdefault(n, []).append(i)
    stacks = {n: np.stack([(np.array(gap[MODELS[i][:2]], dtype=np.int8) - 1).T.copy() if MODELS[i][2] else
                           np.array(gap[MODELS[i][:2]], dtype=np.int8) - 1 for i in members])
              for n, members in by_order.items()}
    agree = 0
    for entry in names:
        start = text.index(f'<tr id="V{entry["order"]}{entry["number"]}">')
        after = text.index("</table>", start) + len("</table>")      # past the table of the generator
        cell = re.findall(r"<td>(.*?)</td>", text[after:text.index("</tr>", after)], re.S)[0]
        ids = [parse_sgv_identity(part) for part in cell.split("<br>") if part.strip()]
        row = np.zeros(len(MODELS), dtype=bool)
        for n, members in by_order.items():
            row[members] = satisfied(ids, stacks[n])
        n, k, o = MODELS[labels.index(entry["generator"])]
        mine = int(rows[classes[(n, k)]["basis_id"]], 16)
        mine = np.array([(mine >> m) & 1 for m in range(len(MODELS))], dtype=bool)
        if o:
            mine = mine[op]
        agree += bool(np.array_equal(row, mine))
    print(f"database: {agree} of {len(names)} bases hold in exactly the tables of the variety of their generator")
    assert agree == len(names)


if __name__ == "__main__":
    main()
