# Rigidity of harmonic functions on the supercritical percolation cluster

[![CI](https://github.com/nitromannitol/Percolation-Rigidity/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Percolation-Rigidity/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Percolation-Rigidity/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Percolation-Rigidity/actions/workflows/comparator.yml)

A Lean 4 formalization of the paper

> Ahmed Bou-Rabee, William Cooperman and Paul Dario,
> [*Rigidity of harmonic functions on the supercritical percolation cluster*](https://arxiv.org/abs/2303.04736),
> Transactions of the American Mathematical Society 378(6) (2025), 3823–3896,
> [doi:10.1090/tran/9264](https://doi.org/10.1090/tran/9264).

Every numbered result of the paper is stated in Lean, and every result that the paper proves is
proved, with no `sorry` and only the standard axioms. The results that the paper quotes from other
works and uses in its proofs are proved in Lean as well. The four main theorems therefore hold in
Lean with no assumption beyond the setting of the paper.

## The paper

Open each edge of the lattice `ℤᵈ`, `d ≥ 2`, independently with probability `p`. When `p` is above
the critical value `p_c(d)`, there is exactly one infinite connected cluster `𝒞_∞` of open edges. A
function `u` on the cluster is *harmonic* if at every vertex its value is the average of its values at
the neighbours joined to it by open edges.

On the full lattice the linear functions are harmonic. On the cluster there are harmonic functions
that grow linearly too, the *corrected planes*. The paper shows that, apart from these, harmonic
functions on the cluster are far more rigid than on `ℤᵈ`:

- **Theorem 1.1.** Almost surely, every harmonic function on the cluster that is Lipschitz for the
  graph distance of the cluster is constant. On `ℤᵈ` the linear functions are counterexamples.
- **Theorem 1.2.** Almost surely, every harmonic function on the cluster that takes integer values and
  grows at most linearly is constant.
- **Theorem 1.3.** In dimension two, almost surely, if `−Δu` is integer-valued with finite support
  and `u(x)` decays faster than `1/|x|`, then `u` has finite support.
- **Theorem 6.5.** The abelian sandpile Markov chain on the largest cluster of the box of side `n`
  mixes in time of order `nᵈ log n`.

Precisely, with `Δ` the Laplacian of the cluster, `Δu(x) = Σ_{y ∼ x} (u(y) − u(x))` over the open
edges at `x`:

**Theorem 1.1.** Almost surely, if `u : 𝒞_∞ → ℝ` is harmonic and `|u(x) − u(y)| ≤ C dist_{𝒞_∞}(x, y)`
for all `x, y ∈ 𝒞_∞`, then `u` is constant.

**Theorem 1.2.** Almost surely, if `u : 𝒞_∞ → ℝ` is harmonic, integer-valued and `u(x) = O(|x|)`, then
`u` is constant.

**Theorem 1.3.** Let `d = 2`. Almost surely, for every finitely supported `f : ℤ² → ℤ`, if
`u : 𝒞_∞ → ℝ` satisfies `−Δu = f` and `lim sup_{R→∞} R · sup_{B_R ∖ B_{R/2}} |u| = 0`, then `u` has
finite support.

**Theorem 6.5.** Let `𝒞_*(Q_n)` be the largest open cluster of the box `Q_n = {x : |x|_∞ ≤ n}`, and
`P^t` the law after `t` steps of the abelian sandpile chain on it, a random walk on its sandpile group,
with uniform law `U`. There are `c, C > 0` such that almost surely, for every `ε > 0` and all large
`n`, `‖P^t − U‖₂² ≤ ε` for `t ≥ C nᵈ log n` and `‖P^t − U‖₂² ≥ ε` for `t ≤ c nᵈ log n`.

## The main theorems in Lean

The main theorems are in [`Rigidity/Proofs/Assembly/Unconditional.lean`](Rigidity/Proofs/Assembly/Unconditional.lean).
Their only hypotheses are the setting of the paper: `2 ≤ d` and `p_c(d) < p < 1`, and `d = 2` for
Theorem 1.3.

| Paper | Lean declaration |
| --- | --- |
| Theorem 1.1 | `Rigidity.Assembly.Unconditional.lipschitz` |
| Theorem 1.2 | `Rigidity.Assembly.Unconditional.integer_valued_linear_growth` |
| Theorem 1.3 | `Rigidity.Assembly.Unconditional.fast_decay` |
| Theorem 6.5 | `Rigidity.Assembly.Unconditional.slow_mixing` |
| Proposition 3.2 | `Rigidity.Assembly.Unconditional.notLipschitz` |

How to read the statements: the law of the edges is `LatticeProb.Percolation.latticeBondLaw d p`, with
`p : unitInterval`, and the critical value is `LatticeProb.Percolation.criticalProbability d`. Each
statement holds for almost every configuration `ω`, together with a proof
`h : HasUniqueInfiniteOpenComponent ω`; the cluster is `uniqueInfiniteComponent h` and its Laplacian is
`componentLaplacian`.

## All numbered results

The paper has 48 numbered results. The table lists each with the Lean declaration that proves it.
Five of them are quoted from other works: Proposition 2.3, Theorems 2.4 and 2.5, and Lemmas 2.13 and
2.14. Four of these are proved here. Lemma 2.13, a fact of plane topology, is used by no proof; its
special case for unions of lattice squares is proved.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 | `Rigidity.Assembly.Unconditional.lipschitz` | Lipschitz harmonic functions on `𝒞_∞` are constant. |
| Theorem 1.2 | `Rigidity.Assembly.Unconditional.integer_valued_linear_growth` | Integer-valued harmonic functions of linear growth are constant. |
| Theorem 1.3 | `Rigidity.Assembly.Unconditional.fast_decay` | `d = 2`: integer Laplacian of finite support and decay faster than `\|x\|⁻¹` force finite support. |
| Lemma 2.1 | `Rigidity.finite_flip_full_measure` | A full-measure event still holds, almost surely, after every finite modification of the bonds. |
| Proposition 2.3 | `Rigidity.Percolation.wellConnected_input` | The box `Q_N` is well-connected with probability at least `1 − C exp(−c Nˢ)`. |
| Theorem 2.4 (order zero) | `Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds` | Large-scale regularity of harmonic functions on `𝒞_∞` above a minimal scale. |
| Theorem 2.4 (order one at the origin) | `Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_holds` | The order-one part of the same regularity statement, at the origin. |
| Theorem 2.5 (qualitative) | `Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds` | Harmonic functions of linear growth are corrected planes `a + p·x + χ_p`. |
| Theorem 2.5 (quantitative) | `Rigidity.Assembly.EveryDimension.correctorQuantitativeInput_holds` | Bounds on the corrector. |
| Proposition 2.6 | `Rigidity.Assembly.Unconditional.greenGradientHomogenization` | `∇ₓG(x, y)` is close to `Σᵢ ∇ℓ_{eᵢ}(x) ∂ᵢḠ(x − y)` above a minimal scale. |
| Proposition 2.8 | `Rigidity.Assembly.Unconditional.mixed_green` | Decay of the mixed derivative `∇ₓ∇_y G` above a minimal scale. |
| Lemma 2.13 (unions of lattice squares) | `Rigidity.Assembly.polyominoJordan` | A simply connected bounded planar domain whose boundary points are simple is bounded by a Jordan curve. |
| Lemma 2.14 | `Rigidity.Topology.jordan_curve_theorem_sphere` | The Jordan curve theorem on the sphere `S²`. |
| Lemma 2.16 | `Rigidity.Assembly.Unconditional.jordanCurves` | Arcs from `K` points of a Jordan curve to the north pole leave at least `K` components whose closure contains the pole. |
| Lemma 3.1 | `Rigidity.Assembly.Unconditional.reductionToSlopeE1` | A nonconstant Lipschitz harmonic function forces `ℓ_{e₁}` to be Lipschitz. |
| Proposition 3.2 | `Rigidity.Assembly.Unconditional.notLipschitz` | For every `L`, with positive probability `\|∇ℓ_{e₁}(0)\| > L`. |
| Lemma 3.3 | `Rigidity.Assembly.Unconditional.compareDifferentPlanes` | The change of the corrected planes when finitely many edges are removed. |
| Proposition 4.1 | `Rigidity.OpenGadget.exponential_growth_on_ambient_open_gadget` | A nonconstant integer-valued harmonic function on the gadget of height `n` has `\|u(t) − u(s)\| ≥ C 3ⁿ`. |
| Lemma 4.2 | `Rigidity.Assembly.effectiveResistanceRecurrence` | The gadget resistances satisfy `R₁ = 3`, `R_{n+1} = (3Rₙ + 2)/(Rₙ + 1)`. |
| Lemma 4.3 | `Rigidity.Assembly.reducedRationalRecursion` | `Rₙ = A_{n+1}/Bₙ`. |
| Lemma 4.4 | `Rigidity.Gadget.numDenomRecs` | The recursions of the numerators `Aₙ` and denominators `Bₙ`. |
| Lemma 4.5 | `Rigidity.Gadget.reducedRational` | `A_{n+1}` and `Bₙ` are coprime. |
| Lemma 4.6 | `Rigidity.Gadget.exponentialGrowth` | `A_{n+1} > 3^{n−1}`. |
| Lemma 4.7 | `Rigidity.Assembly.Unconditional.detSlope` | For a nonzero slope `q`, almost surely some edge carries a non-integer increment of `ℓ_q`. |
| Lemma 4.8 | `Rigidity.Assembly.Unconditional.nonConstantOnGadget` | Conditionally on `𝒞_∞ ∩ Q_R = H`, `ℓ_q` is nonconstant on a gadget with probability at least `c R^{−2d+2}`. |
| Lemma 4.9 | `Rigidity.Assembly.Unconditional.ergodicityLipschitz` | A nonconstant integer-valued harmonic function of linear growth yields an integer-valued corrected plane. |
| Proposition 4.10 | `Rigidity.Assembly.Unconditional.rationalMatrix` | No nonconstant integer-valued harmonic function is within `o(\|x\|)` of a harmonic quadratic. |
| Theorem 5.1 | `Rigidity.Assembly.Unconditional.fastDecayDichotomy` | `d = 2`: if `u → 0` and `Δu ∈ ℤ`, then `lim sup \|x\| \|u(x)\| > 0` or `u` vanishes outside a ball. |
| Proposition 5.3 | `Rigidity.Assembly.Unconditional.fastDecayPotential` | The dichotomy of Theorem 5.1 for the potentials `u_f = Σ_y f(y) H(·, y)`. |
| Proposition 5.5 | `Rigidity.Assembly.Unconditional.logGrowth` | If `Σ f ≠ 0`, then `u_f` grows like `log \|x\|`. |
| Lemma 5.6 | `Rigidity.Assembly.Unconditional.meanZeroRepresentation` | If `Σ f = 0`, then `u_f = Σ_e F(e) ∇H(·, e)` for a finitely supported field `F`. |
| Proposition 5.7 | `Rigidity.Assembly.Unconditional.gradientTrichotomy` | For `p ≠ 0` and `Σ f = 0`: `Σ f ℓ_p ≠ 0`, or `u_f − lim u_f` has finite support. |
| Proposition 5.8 | `Rigidity.Assembly.Unconditional.twoScaleExpansion` | Two-scale expansion of `u_f` with error `C \|x\|^{−5/4}`. |
| Proposition 5.11 | `Rigidity.Assembly.Unconditional.levelSetDensity` | Edges where `∇u_f ≠ 0` and `∇ℓ_p ≠ 0` have positive lower density in dyadic balls. |
| Proposition 5.12 | `Rigidity.Assembly.Unconditional.infiniteDisjointPaths` | A component of the level set `L₀` contains at most `\|supp f\| + 2` disjoint infinite paths. |
| Lemma 5.14 | `Rigidity.Assembly.Unconditional.loopsAroundAnnuli` | Above a random scale, `𝒞_∞` has a loop around the origin in every annulus `Q_{2R} ∖ Q_R`. |
| Lemma 5.16 | `Rigidity.Assembly.Unconditional.strongMaxPrinciple` | A maximum principle for bounded functions harmonic on an infinite proper subset. |
| Lemma 5.17 | `Rigidity.Assembly.Unconditional.polesSuperLevelSets` | Every component of a super-level set `{u > a}` meets the support of `f`. |
| Lemma 5.18 | `Rigidity.Assembly.Unconditional.longNonzeroPaths` | Paths of `𝒞_∞` leaving `Q_{R'}` from `Q_R ⊇ supp f` avoid the zero set of `u`. |
| Lemma 5.19 | `Rigidity.Assembly.Unconditional.noThickPaths` | If `supp u` is infinite, no bi-infinite path in `L₀` has a whole side in `L₀`. |
| Proposition 5.20 | `Rigidity.Assembly.Unconditional.boundarySize` | At most `C_f` disjoint paths join a biconnected subset of a level set to infinity. |
| Proposition 5.21 | `Rigidity.Assembly.Unconditional.disjointPathsToInfinity` | `P(E_R(x)) ≥ 1 − C exp(−c Rˢ)`. |
| Lemma 5.23 | `Rigidity.Assembly.Unconditional.renormalizedDomination` | The renormalized process dominates site percolation of parameter `1 − C exp(−c Rˢ)`. |
| Proposition 5.24 | `Rigidity.Assembly.Unconditional.longPathRenormalized` | Long paths cross many good boxes, outside an event of probability `C exp(−cK)`. |
| Lemma 5.25 | `Rigidity.Assembly.Unconditional.goodEventLowerBound` | The good event `G(x, C_χ, K)` has probability at least `c > 0` for all large `K`. |
| Lemma 5.26 | `Rigidity.Assembly.Unconditional.goodEventDensity` | The density of good points in the triangles `T_L` tends to the probability of the good event. |
| Lemma 5.27 | `Rigidity.Assembly.Unconditional.largeGradientSensitive` | Near a good point, some edge has `∇ℓ_{e₁} ≠ 0` and `∇u_f ≠ 0`. |
| Lemma 5.28 | `Rigidity.Assembly.Unconditional.finiteBranches` | For every edge `(x₀, x₁)` of `𝒞_∞` as in the proof of Lemma 5.27, the pruned block-cut tree has at most `C_branches` branches. |
| Proposition 6.4 | `Rigidity.integer_valued_compact_support` | A finitely supported function on `ℤᵈ` with integer Laplacian is integer-valued. |
| Theorem 6.5 | `Rigidity.Assembly.Unconditional.slow_mixing` | The sandpile chain on `𝒞_*(Q_n)` mixes in `L²` in time of order `nᵈ log n`. |

Two further forms are proved: Lemma 4.8 in the joint form that the proof of Lemma 4.7 uses
(`Rigidity.Assembly.Unconditional.nonConstantOnGadgetJoint`), and Lemma 5.25 with the event `G₃` as printed
(`Rigidity.Assembly.Unconditional.goodEventLowerBoundDirectional`; see correction C32).

## Corrections

The Lean statements follow a corrected draft of the arXiv v2 source,
[`paper/percolation-harmonic-corrected.tex`](paper/percolation-harmonic-corrected.tex). It differs
from arXiv v2 by 38 local corrections, C1 to C39 (there is no C27). Each is marked in the source by a
comment `% CORRECTION [Cn]`, and [`paper/CORRECTIONS.md`](paper/CORRECTIONS.md) lists them with their
reasons.

- Twelve corrections change the statement of a numbered result: C4, C7, C9, C11, C12, C13, C14, C17,
  C18, C19, C21 and C29.
- Six change a definition that statements use (C1, C2, C3, C23, C24, C31), and three correct quoted
  results (C34, C38, C39).
- C32 gives an alternative statement of Lemmas 5.25 to 5.27; the printed Lemma 5.25 is proved too.
- The others change proofs only.

The unmodified arXiv v2 source is [`paper/percolation-harmonic.tex`](paper/percolation-harmonic.tex);
both versions are included as PDFs.

The formalization also found an error in a cited work. Lemma 3.5 of Dario (2018) is false as printed
in dimension `d ≥ 3`. The repository proves a corrected form, and the conclusion of Dario's Theorem 1,
which the paper uses, is unchanged. [`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps the results of the
cited works to their Lean declarations and records every place where the Lean proofs depart from the
paper or from its sources.

## Scope

- **Measurability.** Some events quantify over the corrected planes of every configuration and are not
  shown to be measurable. For them, "with positive probability" means that the event contains a
  measurable event of positive probability (Proposition 3.2, Lemmas 5.25 and 5.27), and an upper bound
  on a probability bounds the outer measure.
- **Theorem 6.5.** The chain is the random walk on the sandpile group of a largest open cluster `V` of
  `Q_n`, started from the saturated sandpile, adding at each step a chip at a uniformly chosen site of
  `V`. The statement asserts that almost surely, for all large `n`, some largest open cluster of `Q_n`
  lies in `𝒞_∞`, and the two bounds hold for every such cluster that meets the boundary of `Q_n`.
- **Not formalized.** Lemma 2.13 in general, which no proof uses; the remarks, problems and
  conjectures of the paper; the figures.

## Checking the proofs

- **No `sorry`.** The library has none. Each of the eight comparator challenge files under
  [`RigidityAudit/`](RigidityAudit/) contains one intentional `sorry` at the statement, which the
  matching solution file proves.
- **Standard axioms only.** [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean) prints the axioms
  of every numbered result and of the main intermediate results, 1308 reports in all.
  [`scripts/check_axioms.py`](scripts/check_axioms.py) fails on any axiom other than `propext`,
  `Classical.choice` and `Quot.sound`, and on a missing report.
- **Independent check of the statements.** Each main theorem has a comparator pair: a
  `Challenge.lean` that restates the theorem and every definition it uses, and a `Solution.lean` that
  proves it from the library. Four pairs restate Theorems 1.1, 1.2, 1.3 and 6.5 using mathlib alone,
  and four restate them with the setting of the paper as the only hypothesis.
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the two statements
  agree, that only the standard axioms are used, and replays the proof through an independent
  implementation of the Lean kernel.
- **Continuous integration.** The **CI** workflow builds the library, checks the axiom reports and
  builds the comparator pairs. The **Comparator audit** workflow runs the comparator on the eight pairs
  after each successful CI run on `main`.

`Rigidity/` and `Rigidity.lean` contain 875 Lean files with 196,843 lines, built on mathlib,
Lattice-Probability and Percolation-Cluster-Homogenization.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get                                          # prebuilt mathlib
lake build                                                  # the library
lake env lean RigidityAudit/Axioms.lean 2>&1 | tee axioms-audit.log
python3 scripts/check_axioms.py axioms-audit.log            # the axiom reports
lake build RigidityAudit                                    # the comparator pairs
```

Lattice-Probability and Percolation-Cluster-Homogenization have no prebuilt cache, so the first build
compiles them as well as the library. They are public repositories, pinned in
[`lake-manifest.json`](lake-manifest.json):

- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069`, the commit of the tag
  `percolation-rigidity-2026-11-03`, which is not on `main`;
- Percolation-Cluster-Homogenization: `https://github.com/nitromannitol/Percolation-Cluster-Homogenization`
  at `51e38b875e2fdebe3a4ec08b84595ff060be59ea`.

The main theorems are in `Rigidity/Proofs/Assembly/Unconditional.lean`;
`import Rigidity.Proofs.Assembly.Unconditional` loads them and what they use.

To rebuild the PDFs of the paper, run `pdflatex` three times on `percolation-harmonic.tex` or
`percolation-harmonic-corrected.tex` in [`paper/`](paper/); the bibliography is included as `.bbl`
files, so BibTeX is not needed.

## Running the comparators

Each comparator pair has a configuration `RigidityAudit/<Pair>/comparator.json`, which permits exactly
`propext`, `Classical.choice` and `Quot.sound` and enables the nanoda kernel. Build
`leanprover/comparator`, `lean4export`, `landrun` and `nanoda` at the revisions listed in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml), then run from the repository
root

```bash
COMPARATOR_BIN=<comparator> COMPARATOR_LANDRUN=<landrun> \
COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  ./scripts/run_comparators.sh
```

The four variables default to the paths under `~/tools` where the workflow builds these tools. The
script builds the library and the audit modules, runs the comparator on every pair and fails if a
pair is missing or rejected; its logs are kept under `.lake/comparator-logs/`.

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
Rigidity.lean            the root module
Rigidity/
  Draft/                 the statements of the numbered results, one file per section of the paper
  Frozen/                eight numbered results stated and proved first, with their definitions
  External/              the statements of the results quoted from other works
  Steps/                 one Lean proposition per step of the paper's proofs
  Proofs/                the proofs
    Assembly/            the numbered results; Unconditional.lean holds the main theorems
    Corrector/, Poincare/, Green/, Regularity/, Barlow/, BarlowLattice/
                         the results of Armstrong-Dario, Dario, Dario-Gu and Barlow that the proofs use
  Support/               definitions and lemmas used by the frozen results
RigidityAudit/           the axiom reports and the eight comparator pairs
paper/                   the arXiv v2 source and the corrected draft (LaTeX and PDF), CORRECTIONS.md
CORRESPONDENCE.md        the results of the cited works, their Lean declarations and the departures
scripts/                 check_axioms.py and run_comparators.sh
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and OpenAI (GPT),
under the direction of Ahmed Bou-Rabee. Every proof is checked by the Lean kernel. The corrections
of the paper and the literature inputs were also reviewed against the printed proofs and their
sources with AI models. The models, tooling and review process are disclosed in [`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard.

## Copied code

Some modules are copied from other repositories, with attribution, and not through a Lake
dependency. Each copied file starts with a header naming its source repository, file and commit;
the modules from Lattice-Probability are adapted from the named revision, and the headers of the
five modules adapted from its revision `7512f4fb` state the changes. The modules copied from
formal-math, openai/math, Leonardo Bonanno's repository and Lattice-High-Contrast-Homogenization,
and the Kesten modules adapted from Lattice-Probability, are in
[Percolation-Cluster-Homogenization](https://github.com/nitromannitol/Percolation-Cluster-Homogenization#copied-code).

| Source | Commit | Files in this repository |
| --- | --- | --- |
| [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability/tree/c21955fb1c127db67c43b995f47db4543f88f9fd) (Apache License 2.0) | `c21955fb1c127db67c43b995f47db4543f88f9fd` | the 12 modules under `Rigidity/Proofs/Topology/PlanarJordan/`, which are based on Leonardo Bonanno's lean-formalizations and on R. Kirov's [jordan_pick](https://github.com/rkirov/jordan_pick/tree/b3c9b7cf7358bf81a077d78ad67e6e8247869ddd) (Apache License 2.0) |
| [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability/tree/7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069) (Apache License 2.0) | `7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069` | `Rigidity/Support/PlanarOrderZeroGradient.lean`, `Rigidity/Support/PlanarGreenQuantitativeField.lean`, `Rigidity/Proofs/S3/PlanarCorrectorValid.lean`, `Rigidity/Proofs/S3/PlanarGreenColumn.lean`: theorems of the modules `LatticeOrderZeroApproximation`, `LatticeOrderZeroTranslation`, `LatticeOrderZeroGradient`, `GreenQuantitativeField`, `MeasurableRootedPlane` and `GreenColumnEvent` of `LatticeProb/Prob/Percolation/`, specialized to `d = 2`; `Rigidity/Proofs/Green/LocalNash.lean`: `heat_step_of_faberKrahnOn`, adapted from `heat_step` of `LatticeProb/Graph/OnDiagonal.lean` |

## Authors and citation

The paper is by **Ahmed Bou-Rabee**, **William Cooperman** and **Paul Dario**. The Lean development
is by **Ahmed Bou-Rabee**. To cite the formalization, use [`CITATION.cff`](CITATION.cff). It is built
on [Lean 4](https://lean-lang.org), [Mathlib](https://github.com/leanprover-community/mathlib4) and
the library [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability).

## License

The Lean development is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE). The
copied modules listed in [Copied code](#copied-code) keep the terms of their sources. The paper
sources in [`paper/`](paper/) are included with the permission of the paper's authors and are not
covered by the Apache license.
