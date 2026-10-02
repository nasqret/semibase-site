#!/usr/bin/env python3
"""Check the data the census site shows against the Cayley tables, by evaluation.

1. Every finitely based class satisfies the shortest known basis shown on its page
   and its certified basis (identities in at most MAX_VARS variables; longer ones in
   nilpotent tables when both sides vanish).
2. For a random sample of pairs (variety, class), the class lies in the variety
   (by census-rows-v1.json) exactly when it satisfies the shortest known basis.
3. The four nonfinitely based classes against the shortest basis of every variety.

The checks are independent of Lean and of Vampire: they only evaluate identities in
the tables. A basis that fails in its table would mean that the data was read with
the wrong orientation.
"""
import json
import os
import random
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.environ.get("SEMIBASE_REPO", os.path.join(HERE, "..", "semibase-order6")))
MAX_VARS = 7
N = 15973


def load(name, folder=os.path.join(HERE, "data")):
    with open(os.path.join(folder, name), encoding="utf-8") as handle:
        return json.load(handle)


TABLES = {r["smallsemi_id"][1]: np.array(r["table"], dtype=np.int64) - 1 for r in load("research/order6/catalogue.json", REPO)["semigroups"]}
_assign = {}


def assignments(k):
    if k not in _assign:
        _assign[k] = np.indices((6,) * k).reshape(k, -1)
    return _assign[k]


def nil_class(T):
    zero = [z for z in range(6) if all(T[z, x] == z == T[x, z] for x in range(6))]
    if not zero:
        return 0
    power, degree = set(range(6)), 1
    while len(power) > 1:
        following = {int(T[a, b]) for a in power for b in range(6)}
        if following == power:
            return 0
        power, degree = following, degree + 1
    return degree if power == {zero[0]} else 0


def holds(T, e, nil):
    """True or False, or None when the identity has too many variables to evaluate."""
    variables = sorted(set(e["lhs"]) | set(e["rhs"]))
    if nil and len(e["lhs"]) >= nil and len(e["rhs"]) >= nil:
        return True
    if len(variables) > MAX_VARS:
        return None
    index = {v: i for i, v in enumerate(variables)}
    A = assignments(len(variables))

    def value(word):
        out = A[index[word[0]]]
        for letter in word[1:]:
            out = T[out, A[index[letter]]]
        return out

    return bool(np.array_equal(value(e["lhs"]), value(e["rhs"])))


def satisfies(k, identities):
    T = TABLES[k]
    nil = nil_class(T)
    results = [holds(T, e, nil) for e in identities]
    if False in results:
        return False
    return None if None in results else True


def main():
    sealed = load("sealed-bases-v1.json")["bases"]
    reduced = load("reduced-forms-v1.json")["forms"]
    order = load("order-v2.json")
    rows = load("census-rows-v1.json")["rows"]
    theory_of = {b: t["theory"] for t in order["theories"] for b in t["bases"]}
    shortest = {}
    for t in order["theories"]:
        b = min(t["bases"], key=lambda b: (len(reduced[b]["identities"]),
                                           sum(len(e["lhs"]) + len(e["rhs"]) for e in reduced[b]["identities"]), b))
        shortest[t["theory"]] = reduced[b]["identities"]
    failures, unchecked = [], 0

    # 1. each class satisfies its shortest basis and its certified basis
    count = 0
    for basis in sealed:
        t = theory_of[basis["basis_id"]]
        for record in basis["classes"]:
            k = int(record["semigroup_id"][3:])
            for label, identities in (("shortest", shortest[t]), ("certified", basis["identities"])):
                result = satisfies(k, identities)
                if result is False:
                    failures.append((k, label, record["proof_orientation"]))
                elif result is None:
                    unchecked += 1
            count += 1
    print(f"1. {count} classes: {len(failures)} fail their basis, {unchecked} checks left partial "
          f"(identities in more than {MAX_VARS} variables)")
    for failure in failures[:20]:
        print("   FAIL", failure)

    # 2. census rows against evaluation, on a sample
    random.seed(20261002)
    theories = sorted(shortest)
    disagree, partial = [], 0
    samples = 20000
    for _ in range(samples):
        t = random.choice(theories)
        k = random.randint(1, N)
        b = next(b for b in order["theories"][t]["bases"])
        listed = bool((int(rows[b], 16) >> (k - 1)) & 1)
        result = satisfies(k, shortest[t])
        if result is None:
            partial += 1
        elif result != listed:
            disagree.append((t, k, listed, result))
    print(f"2. {samples} sampled pairs (variety, class): {len(disagree)} disagree with the census rows, "
          f"{partial} undecided by evaluation")
    for d in disagree[:20]:
        print("   DISAGREE", d)

    # 3. the four nonfinitely based classes
    for k in (3843, 8564, 8878, 13747):
        inside = [t for t in theories if satisfies(k, shortest[t]) is not False]
        listed = [t for t in theories if (int(rows[order["theories"][t]["bases"][0]], 16) >> (k - 1)) & 1]
        print(f"3. [6, {k}] satisfies the basis of {len(inside)} varieties; the census rows list {len(listed)}")
        if sorted(inside) != sorted(listed):
            failures.append((k, "nonfinite rows"))

    if failures or disagree:
        sys.exit(1)


if __name__ == "__main__":
    main()
