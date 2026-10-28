#!/usr/bin/env python3
"""Turn the results of prep/fewvars.py into data/few-variables-v1.json.

    python3 prep/collect_fewvars.py TARGETS.json OUT.json [TARGETS2.json OUT2.json ...]

Keeps, for each variety, the basis in the fewest variables that the search found, and the reduced form of a
certified basis when the reduction removed an identity and its final check passed. Each result records the known
basis that Vampire derived from it, with the orientation of that basis, and the attempts of the search.
"""
import json
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import census as C  # noqa: E402

PROVER = "Vampire 5.0.1 (commit 1b13eaf)"


def slug_of(target_id):
    n, k = target_id.removeprefix("r-").split("-")
    return k if n == "6" else f"{n}-{k}"


def orientation(goals, kind, basis_id):
    """Whether the goals are the known basis as recorded (0) or read backwards (1)."""
    known = C.REDUCED[basis_id]["identities"] if kind == "reduced" else C.BASIS[basis_id]
    key = C.canonical_basis(goals)
    if key == C.canonical_basis(known):
        return 0
    assert key == C.canonical_basis([C.reverse(e) for e in known]), basis_id
    return 1


def main():
    """Arguments: target files and result files, in pairs: TARGETS1 OUT1 [TARGETS2 OUT2 ...]."""
    args = sys.argv[1:]
    assert len(args) % 2 == 0, __doc__
    runs = defaultdict(list)            # target id -> [(target, report)], one per pass
    for tpath, opath in zip(args[::2], args[1::2]):
        targets = {t["id"]: t for t in json.load(open(tpath))}
        for r in json.load(open(opath)):
            if r["id"].startswith("f-"):
                continue                 # countermodels: prep/collect_refute.py
            runs[r["id"]].append((targets[r["id"]], r))
    results = []
    for tid, passes in sorted(runs.items()):
        slug = slug_of(tid)
        v = C.SLUG[slug]
        n, k, o = C.VARIETIES[v]["name"]
        assert o == 0 and (n, k) == tuple(int(x) for x in tid.removeprefix("r-").split("-")), tid
        first = passes[0][0]
        kind, basis_id = first["goals_from"]
        derives = {"kind": kind, "basis": basis_id, "orientation": orientation(first["goals"], kind, basis_id)}
        if first.get("reduce_only"):
            r = passes[-1][1]
            if r.get("removed") and r.get("reduced"):
                results.append({"variety": slug, "kind": "reduce", "basis": r["basis"],
                                "vars": C.nvars(r["basis"]), "derives": derives, "prover": PROVER})
            continue
        tried = [{key: a[key] for key in ("k", "free_object", "rules", "length_bound", "result") if key in a}
                 for t, r in passes for a in r.get("tried", [])]
        found = [(r["vars"], len(r["basis"]), t, r) for t, r in passes if "basis" in r]
        entry = {"variety": slug, "kind": "search", "prover": PROVER, "tried": tried,
                 "known_vars": first["max_vars"] + 1, "lower_bound": min(t["min_vars"] for t, r in passes)}
        if found:
            _, _, t, r = min(found, key=lambda x: (x[0], x[1]))
            tk, tb = t["goals_from"]
            entry.update({"basis": r["basis"], "vars": r["vars"],
                          "derives": {"kind": tk, "basis": tb, "orientation": orientation(t["goals"], tk, tb)}})
        else:
            entry.update({"kind": "search-failed", "derives": derives})
        results.append(entry)
    out = os.path.join(C.DATA, "few-variables-v1.json")
    with open(out, "w", encoding="utf-8") as handle:
        json.dump({"record_type": "few_variable_bases", "prover": PROVER,
                   "method": "prep/fewvars.py: the rules of a complete rewriting system of the free object in k "
                             "generators, read as identities; Vampire derives the known basis from them",
                   "results": results}, handle, separators=(",", ":"))
        handle.write("\n")
    found = sum(1 for e in results if e["kind"] == "search")
    print(f"wrote {out}: {found} bases found by the search, "
          f"{sum(1 for e in results if e['kind'] == 'search-failed')} searches without a basis, "
          f"{sum(1 for e in results if e['kind'] == 'reduce')} reduced bases")


if __name__ == "__main__":
    main()
