# A word model for three Schreier multiset recurrences

**Devin O'Keefe, Independent Researcher**

This repository accompanies the paper *A word model for three Schreier
multiset recurrences*. It contains the manuscript, Lean 4 proofs, and exact
computational checks.

The paper counts uncolored multisets with a unique maximum, multiplicity at
most two at smaller labels, and a Schreier inequality with a margin. A common
word encoding proves the three conjectured recurrences for q = 2, 3, 4. The
paper also gives composition correspondences, explicit multiset maps, and
minimal eventual recurrence orders 3, 5, 5.

## Read the paper

- [Paper PDF](https://github.com/devinokeefe/schreier-multiset-recurrences/releases/latest/download/main.pdf)
- [Release downloads](https://github.com/devinokeefe/schreier-multiset-recurrences/releases)
- [LaTeX source](paper/main.tex) and [bibliography](paper/references.bib)
- [Proof and declaration map](docs/claims.md)

The complete release archive, `schreier-release.zip`, includes the paper,
sources, and validation receipt. A GitHub source-code download contains the
tracked source tree; generated files in `dist/` are supplied as release assets.

## Explore the Lean proofs

Start with the common argument:

- [Words.lean](formal/common/SchreierUnified/Words.lean): words, cost, and residue partitions.
- [Multisets.lean](formal/common/SchreierUnified/Multisets.lean): encoding and inverse laws.
- [Certificates.lean](formal/common/SchreierUnified/Certificates.lean): uniqueness and polynomial identities.
- [TerminalCompositions.lean](formal/common/SchreierUnified/TerminalCompositions.lean): the general composition equivalence, including q = 1.
- [GeneratingFunctions.lean](formal/common/SchreierUnified/GeneratingFunctions.lean): actual counting series, uniqueness, and all nine rational identities.
- [Minimality.lean](formal/common/SchreierUnified/Minimality.lean): coefficient extraction and exact eventual recurrence orders over the rationals.

The recurrence endpoints are in [q = 2](formal/cases/q2/lean/SchreierQ2/Counting.lean),
[q = 3](formal/cases/q3/lean/Main.lean), and [q = 4](formal/cases/q4/lean/SchreierQ4/Main.lean).
The [adapters](formal/adapters) compare the case constructions with the common model.

Lean verifies the common encoding, the three recurrence theorems, the residue
partition and coefficient uniqueness, the polynomial identities, and the
specified comparisons between constructions. It also verifies the general
terminal-composition equivalence, the formal-power-series arguments and
coefficient extraction at every index, and the exact eventual recurrence
orders 3, 5, 5 over the rationals. These results use the original multiset
families, via the proved word-count equivalence; no counting bridge or
recurrence is assumed. The retained q = 3 composition proof remains available.

## Reproduce the results

Install Python 3.11 or later, Git, elan, and either Tectonic or a TeX
installation with latexmk, pdfLaTeX and BibTeX. Run from the repository root:

```sh
python scripts/validate.py sources
elan toolchain install leanprover/lean4:v4.34.0-rc2
python scripts/validate.py deps
python scripts/validate.py all
```

The paper uses amsmath, amsthm, amssymb, booktabs, geometry, lmodern, mathtools,
microtype, xurl, hyperref and the amsplain bibliography style. Poppler's
`pdfinfo` and `pdftoppm` are useful for PDF inspection. No Python packages are
required. An explicit Tectonic executable can be supplied with `--tectonic PATH`.

`deps` fetches the pinned mathlib dependencies and their upstream caches.
The validator compiles every common, case, and adapter module in fresh
snapshots, checks all requested transitive axiom reports, and runs the
15 default declaration linters. The only permitted
axioms are `propext`, `Classical.choice` and `Quot.sound`. The upstream cache
is a trusted input, checked for changes but not rebuilt. Finite computation
is a diagnostic and does not replace the mathematical proofs.

The `math`, `lean` and `paper` phases can also run separately. Results and
logs are written under `.build/`; the PDF is in that run's `paper/out/`
directory. Use `--dependencies PATH` to reuse an existing Lake project's
exact pinned dependency checkouts read-only. All four projects use
`autoImplicit=false`; the top-level validator handles their separate modules.

After a successful `all` run, substitute its actual report path below:

```sh
python scripts/release.py --lean-report REPORT --math-report REPORT --paper-report REPORT
```

Separate phase reports are accepted. Math and paper reports must match the
complete current source inventory; an earlier Lean report is accepted only
for identical formal sources and configuration. The generated `dist/` holds
the paper, complete archive, and portable validation receipt. Inspect every
PDF page before publishing. The receipt summarizes execution evidence;
retain the raw logs separately if they are needed for an audit.

GitHub Actions runs the validator and produces downloadable build artifacts.
It does not publish releases. The pinned Lean version is in
[`lean-toolchain`](formal/common/lean-toolchain), and all nine dependency
revisions are in [`lake-manifest.json`](formal/common/lake-manifest.json).

After intentional edits, run `python scripts/update_sources.py`, review the
listed changes, and include the updated `SOURCES.tsv`. Validation never
updates this inventory automatically. `.gitattributes` preserves source bytes
across Windows and Unix checkouts. Keep local output under `.build/` or `dist/`.

## Cite this work

Devin O'Keefe. *A word model for three Schreier multiset recurrences*. Preprint, 2026.

[CITATION.cff](CITATION.cff) supplies citation metadata. For use of the formal
proofs or computational checks, also record the release tag or commit used.

## Licenses and contributions

Copyright 2026 Devin O'Keefe. The code and repository documentation are
licensed under [Apache-2.0](LICENSE). The article source in `paper/` and the
generated article PDF are licensed under [CC BY 4.0](paper/LICENSE).
Dependencies retain their own licenses and are fetched separately.

Corrections are welcome through GitHub issues and pull requests. For build
problems, include the version or commit, operating system, and error output.
