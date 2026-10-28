# Third-party data

The multiplication tables shown on the pages come from the GAP package
Smallsemi 0.7.2:

- Copyright (C) 2008-2025 Andreas Distler and James D. Mitchell.
- Source: <https://github.com/gap-packages/smallsemi>
- License: GPL-3.0-or-later.

The site reads the tables of order six from `research/order6/catalogue.json` of
[semibase-order6](https://github.com/nasqret/semibase-order6), and those of
orders one to five from `data/lower-classes-v1.json`, both derived from
Smallsemi. Smallsemi itself is not included in this repository.

The certified bases of orders five and six read back from the Lean theorems,
the reduced forms of order six and the satisfaction rows over all tables of
order at most six come from the `bases-min` tools of Mikoláš Janota. The bases
and theorems of orders one to four come from the records of the campaign that
wrote the Lean proofs.

`data/sgv-names-v1.json` keeps, for each variety of the database of J. Araújo,
J. P. Araújo, P. J. Cameron, E. W. H. Lee and J. Raminhos
(<https://www.sgv.dm.fct.unl.pt/>; J. Algebra 635 (2023) 698–735), only its
name V(n,i) and the table of its generator, to cross-reference the varieties;
the bases of the database are not reproduced.
