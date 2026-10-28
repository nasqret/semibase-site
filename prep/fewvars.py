#!/usr/bin/env python3
"""Search for identity bases in few variables, and check them with Vampire.

    python3 fewvars.py TARGETS.json OUT.json [--workers N] [--vampire PATH]

Each target is a variety W given by a generating table S (0-based), a known basis of W (the goals), and a range of
numbers of variables to try. For k variables, the identities of W in k variables are those of the free object F of W
on k generators: the functions S^k -> S that words define. F is found breadth first, every element with its least
word in the shortlex order, and the words that are not least while all their proper factors are give a complete
rewriting system of F. Its rules, read as identities, hold in S and derive every identity of W in k variables.

If Vampire derives every goal from some of these identities, those identities are a basis of W: they hold in W, and
they derive a basis. The search tries the rules up to a length bound, raising the bound until the goals follow or
the bound is exhausted, keeps the rules that the proofs use, removes those that follow from the rest, and checks
the result once more: every goal derived from the final list. A goal that Vampire does not derive in time decides
nothing; the target then keeps its known basis.
"""
import argparse
import itertools
import json
import multiprocessing
import os
import re
import subprocess
import sys
import tempfile
import time

import numpy as np

VAMPIRE = os.path.expanduser("~/bin/vampire-5.0.1")
CAP = 60000            # largest free object computed
VARS = "XYZUVWABCDEFGH"


# ------------------------------------------------------------------ the free object


def free_object(table, k, cap=CAP):
    """Elements of the free object on k generators of the variety of `table`, breadth first.

    Returns (words, rules): the least word of every element, and the rules (word, normal form) of the reduced
    complete rewriting system, or None when the object has more than `cap` elements."""
    T = np.asarray(table, dtype=np.int16)
    n = T.shape[0]
    points = np.indices((n,) * k).reshape(k, -1)            # all assignments of the k variables
    gens = [points[i].astype(np.int16) for i in range(k)]
    seen = {}
    words, funcs = [], []
    for i, g in enumerate(gens):
        key = g.tobytes()
        if key not in seen:
            seen[key] = len(words)
            words.append((i,))
            funcs.append(g)
    head = 0
    candidates = []                                         # (word, element) of the non-tree edges
    generator_element = [seen[g.tobytes()] for g in gens]
    for i in range(k):
        if words[generator_element[i]] != (i,):
            candidates.append(((i,), generator_element[i]))
    while head < len(words):
        u = head
        head += 1
        for i in range(k):
            f = T[funcs[u], gens[i]]
            key = f.tobytes()
            w = words[u] + (i,)
            if key in seen:
                candidates.append((w, seen[key]))
            else:
                if len(words) >= cap:
                    return None
                seen[key] = len(words)
                words.append(w)
                funcs.append(f)
    normal = set(words)
    rules = [(w, words[v]) for w, v in candidates if w[1:] in normal or len(w) == 1]
    return words, rules


def canonical(lhs, rhs):
    """An identity up to renaming its variables and swapping its sides."""
    best = None
    for a, b in ((lhs, rhs), (rhs, lhs)):
        names = {}
        for v in a + b:
            names.setdefault(v, len(names))
        form = (tuple(names[v] for v in a), tuple(names[v] for v in b))
        if best is None or form < best:
            best = form
    return best


def identities_of(rules):
    out = {}
    for lhs, rhs in rules:
        out.setdefault(canonical(lhs, rhs), None)
    return sorted(out, key=lambda e: (len(e[0]) + len(e[1]), e))


# ------------------------------------------------------------------ Vampire


def term(word):
    out = VARS[word[0]]
    for v in word[1:]:
        out = f"m({out},{VARS[v]})"
    return out


def formula(e):
    lhs, rhs = e
    variables = sorted(set(lhs) | set(rhs))
    return f"![{','.join(VARS[v] for v in variables)}]: {term(lhs)} = {term(rhs)}"


def problem(axioms, goal):
    lines = ["fof(assoc, axiom, ![X,Y,Z]: m(m(X,Y),Z) = m(X,m(Y,Z)))."]
    lines += [f"fof(a{i}, axiom, {formula(e)})." for i, e in enumerate(axioms)]
    lines.append(f"fof(goal, conjecture, {formula(goal)}).")
    return "\n".join(lines) + "\n"


def prove(axioms, goal, seconds):
    """(proved, indices of the axioms the proof uses)."""
    with tempfile.NamedTemporaryFile("w", suffix=".p", delete=False) as handle:
        handle.write(problem(axioms, goal))
        path = handle.name
    try:
        out = subprocess.run([VAMPIRE, "--mode", "casc", "-t", str(seconds), "--proof", "tptp",
                              "--output_axiom_names", "on", path],
                             capture_output=True, text=True, timeout=seconds * 3 + 30).stdout
    except subprocess.TimeoutExpired:
        return False, set()
    finally:
        os.unlink(path)
    if "SZS status Theorem" not in out:
        return False, set()
    used = {int(m) for m in re.findall(r"\bfile\('[^']*',a(\d+)\)", out)}
    return True, used


# ------------------------------------------------------------------ one target


def as_pair(e):
    return (tuple(e["lhs"]), tuple(e["rhs"]))


def reduce_only(target, goals):
    """Remove from a known basis the identities that follow from the others, and check the result."""
    basis = sorted(goals, key=lambda e: (-(len(e[0]) + len(e[1])), e))
    for e in list(basis):
        rest = [x for x in basis if x != e]
        if rest and prove(rest, e, 10)[0]:
            basis = rest
    removed = [g for g in goals if g not in basis]
    checks = [prove(basis, g, 60)[0] for g in removed]
    basis.sort(key=lambda e: (len(set(e[0] + e[1])), len(e[0]) + len(e[1]), e))
    return {"id": target["id"], "reduced": all(checks), "removed": len(removed),
            "basis": [{"lhs": list(a), "rhs": list(b)} for a, b in basis]}


def countermodel(rules, goal, seconds):
    """A finite semigroup that satisfies the rules but not the goal, found by Vampire's model builder, as a
    0-based table; or None."""
    with tempfile.NamedTemporaryFile("w", suffix=".p", delete=False) as handle:
        handle.write(problem(rules, goal))
        path = handle.name
    try:
        out = subprocess.run([VAMPIRE, "-sa", "fmb", "-t", str(seconds), path], capture_output=True,
                             text=True, timeout=seconds * 3 + 30).stdout
    except subprocess.TimeoutExpired:
        return None
    finally:
        os.unlink(path)
    if "SZS status CounterSatisfiable" not in out:
        return None
    pairs = re.findall(r"m\('?fmb_\$i_(\d+)'?,'?fmb_\$i_(\d+)'?\) = '?fmb_\$i_(\d+)'?", out)
    if not pairs:
        return None
    n = max(int(x) for p in pairs for x in p)
    table = [[None] * n for _ in range(n)]
    for a, b, c in pairs:
        table[int(a) - 1][int(b) - 1] = int(c) - 1
    if any(x is None for row in table for x in row):
        return None
    return table


def holds(table, e):
    variables = sorted(set(e[0]) | set(e[1]))
    n = len(table)
    for values in itertools.product(range(n), repeat=len(variables)):
        val = dict(zip(variables, values))

        def ev(word):
            out = val[word[0]]
            for v in word[1:]:
                out = table[out][val[v]]
            return out
        if ev(e[0]) != ev(e[1]):
            return False
    return True


def refute(target):
    """For each number of variables k below the known basis, a semigroup outside the variety that satisfies every
    identity of the variety in k variables: then no basis uses only k variables."""
    started = time.time()
    goals = [as_pair(e) for e in target["goals"]]
    report = {"id": target["id"], "refuted": []}
    for k in range(target["max_vars"], target["min_vars"] - 1, -1):    # the largest k first: the strongest bound
        free = free_object(target["table"], k)
        if free is None:
            continue
        rules = identities_of(free[1])
        found = None
        for g in goals:
            if len(set(g[0] + g[1])) <= k:
                continue
            table = countermodel(rules, g, target.get("seconds", 60))
            if table is None:
                continue
            n = len(table)
            assoc = all(table[table[a][b]][c] == table[a][table[b][c]] for a in range(n) for b in range(n)
                        for c in range(n))
            if assoc and all(holds(table, e) for e in rules) and not holds(table, g):
                found = {"k": k, "table": table, "violates": {"lhs": list(g[0]), "rhs": list(g[1])}}
                break
        if found:
            report["refuted"].append(found)
            break
    report["seconds"] = round(time.time() - started, 1)
    return report


def search(target):
    started = time.time()
    goals = [as_pair(e) for e in target["goals"]]
    if target.get("refute"):
        return refute(target)
    if target.get("reduce_only"):
        report = reduce_only(target, goals)
        report["seconds"] = round(time.time() - started, 1)
        return report
    report = {"id": target["id"], "tried": []}
    for k in range(target["min_vars"], target["max_vars"] + 1):
        free = free_object(target["table"], k)
        if free is None:
            report["tried"].append({"k": k, "result": f"free object larger than {CAP}"})
            break
        words, rules = free
        ids = identities_of(rules)
        attempt = {"k": k, "free_object": len(words), "rules": len(ids)}
        found = None
        for bound in sorted({len(a) + len(b) for a, b in ids}):
            axioms = [e for e in ids if len(e[0]) + len(e[1]) <= bound]
            if len(axioms) > 4000:
                break
            used, ok = set(), True
            for g in goals:
                proved, u = prove(axioms, g, target.get("seconds", 20))
                if not proved:
                    ok = False
                    break
                used |= u
            if ok:
                found = [axioms[i] for i in sorted(used)]
                attempt["length_bound"] = bound
                break
        if found is None:
            attempt["result"] = "goals not derived"
            report["tried"].append(attempt)
            continue
        # drop the identities that follow from the others, the longest first
        basis = sorted(found, key=lambda e: (-(len(e[0]) + len(e[1])), e))
        for e in list(basis):
            rest = [x for x in basis if x != e]
            if rest and prove(rest, e, 10)[0]:
                basis = rest
        basis.sort(key=lambda e: (len(set(e[0] + e[1])), len(e[0]) + len(e[1]), e))
        checks = [prove(basis, g, 60)[0] for g in goals]
        attempt["result"] = "basis" if all(checks) else "final check failed"
        attempt["basis"] = [{"lhs": list(a), "rhs": list(b)} for a, b in basis]
        report["tried"].append(attempt)
        if all(checks):
            report["basis"] = attempt["basis"]
            report["vars"] = max(len(set(a + b)) for a, b in basis)
            break
    report["seconds"] = round(time.time() - started, 1)
    return report


def main():
    global VAMPIRE
    parser = argparse.ArgumentParser()
    parser.add_argument("targets")
    parser.add_argument("out")
    parser.add_argument("--workers", type=int, default=os.cpu_count())
    parser.add_argument("--vampire", default=VAMPIRE)
    args = parser.parse_args()
    VAMPIRE = args.vampire
    with open(args.targets) as handle:
        targets = json.load(handle)
    done = {}
    if os.path.exists(args.out):
        with open(args.out) as handle:
            done = {r["id"]: r for r in json.load(handle)}
    todo = [t for t in targets if t["id"] not in done]
    print(f"{len(todo)} targets, {args.workers} workers", flush=True)
    with multiprocessing.Pool(args.workers) as pool:
        for report in pool.imap_unordered(search, todo):
            done[report["id"]] = report
            with open(args.out + ".tmp", "w") as handle:
                json.dump(list(done.values()), handle)
            os.replace(args.out + ".tmp", args.out)
            print(report["id"], report.get("vars", "-"), report["seconds"], flush=True)


if __name__ == "__main__":
    main()
