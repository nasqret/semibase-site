# SemiBase census website

A static website about the 15,973 semigroups of order six and their identity
bases, published at **<https://nasqret.github.io/semibase-site/>**: one page per
semigroup, per variety and per certified basis, with search, a filterable list,
an interactive graph of the varieties, and links to the Lean proofs in
[nasqret/semibase-order6](https://github.com/nasqret/semibase-order6), release
1.0.0, archived on Zenodo as
[doi:10.5281/zenodo.23109225](https://doi.org/10.5281/zenodo.23109225).

## What it shows

- `index.html`: the numbers, a search box, notable semigroups and the
  distribution of basis lengths.
- `s/<k>.html`, one per class `[6, k]`: a description, the Cayley table and its
  structure (idempotents, zero, identity, nilpotency, regularity, 𝒥-classes,
  rank, self-duality); the shortest known basis and the basis certified in Lean,
  or, for the four exceptions, the argument that no finite basis exists; the
  endpoint theorem with a link to its line in the repository, the statement Lean
  checked, the method of the proof and the size of the code it needs; the variety
  it generates, the varieties directly above and below, the other semigroups
  that generate it; and the tables that differ from it in one or two entries.
- `v/<k>.html`, one per variety `V[k]`, named after its smallest generator `[6, k]`:
  shortest known basis, certified bases, its neighbourhood in the inclusion order,
  its generators and the semigroups of order six it contains.
- `b/<id>.html`, one per certified basis: all its identities and the classes it
  is certified for.
- `browse.html`: all classes in one table, with filters and sorting kept in the
  address.
- `varieties.html`: the 505 varieties as a sortable list, and as an interactive
  graph of their inclusions. Selecting a variety colours everything above and
  below it; the view around a variety lays out only those, one row per step;
  search finds a variety or the variety of a semigroup; the address keeps the
  selection (`varieties.html#graph=7390&around=2`), so a view can be shared. It
  works with a mouse, a keyboard and touch, and has a full-screen mode.
- `nonfinite.html` and `about.html`.

The site is plain HTML, CSS and a little JavaScript with relative links only, so
it works from disk and from any static web server, in any directory, on phones
as well as on desktops.

## Publishing

Every push to `main` runs `.github/workflows/pages.yml`: it checks out this
repository and the release of semibase-order6 named in `LEAN_REF` (now `v1.0.0`),
builds the site, runs both checks below, and publishes it on GitHub Pages. To
point the site at a later release, change `LEAN_REF`.

## Building

```sh
pip install -r requirements.txt
python3 build.py        # about 15 seconds; writes site/
python3 check_data.py   # about 5 seconds; checks the data against the tables
python3 qa.py           # about 25 seconds; checks every page: links, HTML, wording
```

`build.py` needs Python 3.12 or later with numpy, and a checkout of
semibase-order6 next to this directory (or set `SEMIBASE_REPO`). It reads the
catalogue and the census map from that checkout, and the Lean links point to its
commit, so build from a commit that is on GitHub. The layout of the inclusion
graph comes from Graphviz (`dot`); it is kept in `data/graph-layout.json` with a
hash of its input, so Graphviz is needed only when the varieties or their order
change. Open `site/index.html` to view the result.

The pages load quickly: a semigroup page is about 3 KB compressed, and the
stylesheet and scripts (about 10 KB) are shared and cached. Their addresses
carry a hash of their content, so a new build is never mixed with an old one in
a browser's cache. The data of the list (33 KB compressed) and of the graph
(51 KB) load only on the pages that use them, the graph only when it is opened.
Long lists of semigroups are drawn from a bit set when opened.

Inputs:

| File | Content | Source |
|---|---|---|
| `research/order6/catalogue.json` | the 15,973 tables, GAP Smallsemi 0.7.2 | semibase-order6 |
| `provenance/final-census-map.json` | the endpoint theorem of each class | semibase-order6 |
| `data/sealed-bases-v1.json` | the certified basis of each finitely based class, read back from Lean | bases-min, `data/order6-seal-20260924/` |
| `data/reduced-forms-v1.json` | each certified basis without the identities that follow from the others (Vampire) | bases-min, same folder |
| `data/equivalences-v1.json` | Vampire proofs that the 31 pairs of equivalent bases are equivalent | bases-min, same folder |
| `data/order-v2.json` | the 505 varieties and their inclusions (Vampire) | bases-min, same folder |
| `data/census-rows-v1.json` | for each basis, the classes of order six in which it holds | bases-min, same folder |
| `data/graph-layout.json` | the Graphviz layout of the inclusion graph | made by `build.py` |

`check_data.py` evaluates identities in the tables, independently of Lean and
Vampire: every finitely based class satisfies the shortest known basis and the
certified basis shown on its page; on 20,000 random pairs, a class lies in a
variety by `census-rows-v1.json` exactly when it satisfies the variety's basis;
and none of the four nonfinitely based classes lies in any of the 505 varieties.
`build.py` asserts the consistency of the inputs and reports any theorem whose
line it cannot find.

## What is proved where

The certified bases and the four nonfinite-basis results are theorems checked by
Lean. The shortest known bases and the inclusions between varieties come from
Vampire, and the pages say so. "Shortest known" means the shortest found, not
proved minimal.

## Licence

GPL-3.0-or-later, like semibase-order6 and GAP Smallsemi, from which the tables
are derived; see `LICENSE` and `NOTICE.md`. Created and curated by
[@nasqret](https://github.com/nasqret).
