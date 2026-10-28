#!/usr/bin/env python3
"""Turn the countermodels of prep/fewvars.py (targets with "refute") into data/countermodels-v1.json.

    python3 prep/collect_refute.py REFUTE_OUT.json [MORE.json ...]

A countermodel for a variety V and a number k is a finite semigroup, given as a 0-based table, that satisfies every
identity of V in k variables but violates an identity of V: so no basis of V uses only k variables. fewvars.py
checked each model by evaluation before keeping it, and check_data.py checks it again on every build.
"""
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import census as C  # noqa: E402


def main():
    models = {}
    for path in sys.argv[1:]:
        for r in json.load(open(path)):
            for found in r.get("refuted", []):
                n, k = r["id"].removeprefix("f-").split("-")
                slug = k if n == "6" else f"{n}-{k}"
                assert slug in C.SLUG, slug
                best = models.get(slug)
                if best is None or found["k"] > best["k"] or (found["k"] == best["k"] and
                                                              len(found["table"]) < len(best["table"])):
                    models[slug] = {"variety": slug, "k": found["k"], "table": found["table"],
                                    "violates": found["violates"]}
    out = os.path.join(C.DATA, "countermodels-v1.json")
    with open(out, "w", encoding="utf-8") as handle:
        json.dump({"record_type": "variable_countermodels", "prover": "Vampire 5.0.1 (commit 1b13eaf), -sa fmb",
                   "models": sorted(models.values(), key=lambda m: C.SLUG[m["variety"]])},
                  handle, separators=(",", ":"))
        handle.write("\n")
    print(f"wrote {out}: {len(models)} countermodels")


if __name__ == "__main__":
    main()
