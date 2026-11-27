# Contributing and building

This repository is mainly a finished artifact, the formalization of one paper, but issues and
pull requests are welcome.

## Building locally

Install [elan](https://github.com/leanprover/elan); the toolchain is pinned in `lean-toolchain`.

```bash
lake exe cache get            # prebuilt mathlib
lake build                    # the library
lake build RigidityAudit      # the comparator challenges and solutions
```

The library must build with **no warnings**. Lattice-Probability and
Percolation-Cluster-Homogenization have no prebuilt cache, so the first build compiles them as well
as the library. The only intentional `sorry`s are the statement-level ones, one in each
`RigidityAudit/*/Challenge.lean`; `lake build RigidityAudit` reports them as warnings, and the
comparator checks each against its solution.

## The main results and the axiom audit

The main theorems (Theorems 1.1, 1.2, 1.3 and 6.5) are in
`Rigidity/Proofs/Assembly/Main.lean`; the other numbered results are in the neighbouring files
of `Rigidity/Proofs/Assembly/`.

```bash
lake env lean RigidityAudit/Axioms.lean 2>&1 | tee axioms-audit.log
python3 scripts/check_axioms.py axioms-audit.log
```

`RigidityAudit/Axioms.lean` prints the axiom reports of the numbered results, of the propositions
that state the quoted results, and of further proved results, such as the slab connectivity theorem
`Rigidity.Percolation.uniformCubeSlabConnectivity_of_criticalProbability_lt`. It is not imported by
the root module, because a `#print axioms` command runs again whenever its module is rebuilt.
`scripts/check_axioms.py` fails on an error or a warning in the log, on `sorryAx`, on any axiom
other than `propext`, `Classical.choice` and `Quot.sound`, and on a missing, unexpected or repeated
report. The literature inputs are hypotheses of the theorems that use them, not axioms, so they do
not appear in the reports of the theorems.

## Conventions for Lean files

- No `sorry`, `admit`, `native_decide` or new `axiom` in the library. Avoid `set_option maxHeartbeats`;
  where it is used, it raises the limit to at most 400000 for a single declaration.
- Statements stay faithful to the corrected draft `paper/percolation-harmonic-corrected.tex` and
  are referred to by their number and LaTeX label, never by line number. Where a statement
  departs from the printed paper, the departure is listed in `paper/CORRECTIONS.md`.
- A result cited from the literature is stated as a proposition in `Rigidity/External/` (or in an
  `External/` module of a dependency), with its source in the docstring, and enters a theorem as an
  explicit hypothesis. Do not add an `axiom` for it.
- New declarations go under `Rigidity/`. The dependencies under `.lake/packages/` are read-only.
- Avoid `lake clean`, which removes the builds of the dependencies: the mathlib build from its
  cache and the builds of Lattice-Probability and Percolation-Cluster-Homogenization, which have no
  cache and are rebuilt from source.

## Comparators

`RigidityAudit/` has seven pairs, `Lipschitz/`, `IntegerLinearGrowth/`, `FastDecay/` and
`SlowMixing/`, for Theorems 1.1, 1.2, 1.3 and 6.5, and `SlowMixingUnconditional/`,
`IntegerLinearGrowthUnconditional/` and `FastDecayUnconditional/`, for Theorems 6.5, 1.2 and 1.3
with the regime as their only hypothesis (the vocabulary of each is that of the corresponding pair
without its cited results, and its solution uses that pair's `SolutionBasic.lean`). Each has a mathlib-only `Challenge.lean`, a
`Solution.lean` that proves the same statement from the library, and a `comparator.json` that
permits exactly `propext`, `Classical.choice` and `Quot.sound` and enables the nanoda kernel. Do
not add a declaration to a challenge that the statement does not need, and do not change a
challenge without checking it against the paper's statement.

To run the pairs locally, build `leanprover/comparator`, `lean4export`, `landrun` and `nanoda` at
the revisions listed in `.github/workflows/comparator.yml`, then run `./scripts/run_comparators.sh`
as described in the [`README.md`](README.md). A missing pair, a missing tool or a failed kernel
check is a failure.

## Continuous integration

- **CI** (`.github/workflows/build.yml`) builds the library, rejects any warning and any `sorry`,
  runs the axiom audit and builds the comparator surface. It runs on pushes to `main` that change
  more than documentation, the paper, `formalization.yaml` or `CITATION.cff`.
- **Comparator audit** (`.github/workflows/comparator.yml`) builds the comparator tools at pinned
  revisions and runs the seven pairs with the Lean kernel and the independent nanoda kernel. It runs
  after each successful CI run on `main` (on the commit that CI built) and on manual dispatch.
