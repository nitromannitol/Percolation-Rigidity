# Rigidity of harmonic functions on the supercritical percolation cluster

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee, William Cooperman and Paul Dario,
> [*Rigidity of harmonic functions on the supercritical percolation cluster*](https://arxiv.org/abs/2303.04736),
> Transactions of the American Mathematical Society 378(6) (2025), 3823–3896,
> [doi:10.1090/tran/9264](https://doi.org/10.1090/tran/9264); arXiv:2303.04736.

The statements follow a corrected draft of the arXiv v2 source,
[`paper/percolation-harmonic-corrected.tex`](paper/percolation-harmonic-corrected.tex). Every
change from arXiv v2 is a local correction, marked in the source by a comment `% CORRECTION [Cn]`;
[the table below](#corrections-to-the-published-version) lists them. The unmodified arXiv v2 source is
kept in [`paper/percolation-harmonic.tex`](paper/percolation-harmonic.tex), and both versions are
included as compiled PDFs.

The paper has 48 numbered results. The 43 results that the paper proves are proved in Lean, with no
`sorry` and only the standard axioms, from twelve results of the literature that enter as explicit
hypotheses (see [Assumed literature inputs](#assumed-literature-inputs)). Ten of these twelve
inputs are also proved in Lean: the uniqueness of the infinite cluster, the smoothing bound of
Micciancio and Regev, the crossing estimate of Kesten, the Jordan curve theorem on `S²`
(Lemma 2.14), the well-connectedness of boxes (Proposition 2.3), the concentration of the density
of the infinite cluster, the regularity of order zero (Theorem 2.4 at order zero), the existence
of the Green columns, the qualitative corrector input (Theorem 2.5, qualitative part,
`supercriticalBondCorrectorInput_holds`) and the regularity of order one at the origin (Theorem 2.4
at order one, `armstrongDarioOrderOneOrigin_holds`), both in every dimension. The other two remain
hypotheses: the quantitative corrector input (Theorem 2.5, quantitative part) and the quantitative
estimate of the Green function of Dario and Gu; the dimension-two forms of both are proved, and in
every dimension `d ≥ 3` the quantitative corrector input reduces to Theorem 1 of Dario
(`DarioOptimalCorrectorThree`,
`Rigidity.Assembly.WithProvedCorrector.correctorQuantitativeInput_of_darioThree`) and the Green
estimate to Theorem 1 of Dario and Gu (`DarioGuHeatKernelD d`,
`supercriticalBondGreenQuantitative_of_heatKernel`). Theorem 1.3 in the
form with the twelve inputs takes only these two (`Rigidity.Assembly.WithProvedCorrector.fast_decay`).
Theorems 6.5 and 1.3 are proved with no literature hypothesis
([`ProvedFluxWeakNorm.fast_decay_holds`](Rigidity/Proofs/Assembly/ProvedFluxWeakNorm.lean) for
Theorem 1.3). The Gaussian upper bound of Barlow, which is not one of the twelve inputs but enters
the dimension-two proof of Theorem 1.3 through Theorem 1 of Dario and Gu, is proved in every
dimension (`barlowGaussianUpperBound_holds`; in dimension two `barlowGaussianUpperBoundTwo_holds`),
and in dimension two so are Theorem 3 of Dario and Gu
(`darioGuGradientBoundTwo_holds`) and Proposition 2.13 of Dario and Gu, the weak norm of the centered
flux of the corrector (`darioGuFluxWeakNormTwo_holds`), from which the quantitative estimate of the
Green function in dimension two follows (`supercriticalBondGreenQuantitativeTwo_holds`). The five numbered results that the paper does not prove are
quoted from the literature: Proposition 2.3, Theorems 2.4 and 2.5 (each as two inputs) and
Lemma 2.14 enter among the twelve inputs, and Lemma 2.13, a fact of plane topology, is not one of
them and is used by no Lean proof. Its special case that the proof of Proposition 5.12 applies, to
the interior of a finite union of lattice squares, is proved (`Rigidity.Assembly.polyominoJordan`),
and the general lemma is not formalized. Of the main results, Theorems 1.1, 1.2 and 1.3 are
stated as printed, and Theorem 6.5 as printed with its restriction event made explicit (see
[Standing assumptions and scope](#standing-assumptions-and-scope), item 4); the statements changed by
the corrections are listed in
[Corrections to the published version](#corrections-to-the-published-version).

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4), on the
public library [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability), and on
[Percolation-Cluster-Homogenization](https://github.com/nitromannitol/Percolation-Cluster-Homogenization), the formalization of Armstrong and Dario,
*Elliptic regularity and quantitative homogenization on percolation clusters* (Comm. Pure Appl.
Math. 71 (2018)), with the percolation results it uses. Its declarations keep their names
(`Rigidity.*`); the sections below on Armstrong and Dario, on the density concentration, on slab
connectivity and on well-connected cubes describe results proved there, and their links point to
its files.

[![CI](https://github.com/nitromannitol/Percolation-Rigidity/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Percolation-Rigidity/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Percolation-Rigidity/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Percolation-Rigidity/actions/workflows/comparator.yml)

## What is proved

Each edge of `ℤᵈ`, `d ≥ 2`, is open independently with probability `𝔭 ∈ (𝔭_c(d), 1)`, where
`𝔭_c(d)` is the bond percolation threshold, and `𝒞_∞` is the unique infinite open cluster. A function
`u : 𝒞_∞ → ℝ` is *harmonic* if `Δ_{𝒞_∞} u(x) = Σ_{y ∼ x} (u(y) − u(x)) = 0` for every `x ∈ 𝒞_∞`, the
sum running over the open edges at `x`. In Lean, the law of the configuration is
`LatticeProb.Percolation.latticeBondLaw d p` with `p : unitInterval`, the threshold is
`LatticeProb.Percolation.criticalProbability d`, and each statement holds for almost every
configuration `ω` together with a proof `h : HasUniqueInfiniteOpenComponent ω`; the cluster is
`uniqueInfiniteComponent h` and the Laplacian is `componentLaplacian`.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 | `Rigidity.Assembly.Main.lipschitz` | Lipschitz harmonic functions on the cluster are constant. |
| Theorem 1.2 | `Rigidity.Assembly.Main.integerValuedLinearGrowth` | Integer-valued harmonic functions of linear growth are constant. |
| Theorem 1.3 | `Rigidity.Assembly.Main.fastDecay` | In `d = 2`, a function with integer Laplacian of finite support that decays faster than `\|x\|⁻¹` has finite support. |
| Theorem 6.5 | `Rigidity.Assembly.Main.slowMixing` | The sandpile Markov chain on the largest cluster of a box of radius `n` mixes in time of order `nᵈ log n`. |

**Theorem 1.1.** Almost surely, if `u : 𝒞_∞ → ℝ` is harmonic and Lipschitz for the graph distance of
the cluster, `|u(x) − u(y)| ≤ C dist_{𝒞_∞}(x, y)` for all `x, y ∈ 𝒞_∞`, then `u` is constant.

**Theorem 1.2.** Almost surely, if `u : 𝒞_∞ → ℝ` is harmonic, integer-valued and of at most linear
growth, `u(x) = O(|x|)`, then `u ≡ a` for some `a ∈ ℤ`.

**Theorem 1.3.** Let `d = 2`. Almost surely, for every finitely supported `f : ℤ² → ℤ`, if
`u : 𝒞_∞ → ℝ` satisfies `−Δ_{𝒞_∞} u = f` and `lim sup_{R→∞} R · sup_{B_R ∖ B_{R/2}} |u| = 0`, then
the support of `u` is finite.

**Theorem 6.5.** Let `𝒞_*(Q_n)` be the largest open cluster of the box `Q_n = {x : |x|_∞ ≤ n}`, and
`P^t` the law after `t` steps of the abelian sandpile Markov chain on it, a random walk on its sandpile
group, with uniform law `U`. There are `c, C > 0` such that almost surely, for every `ε > 0` and all
large `n`, `‖P^t − U‖₂² ≤ ε` for all `t ≥ C nᵈ log n` and `‖P^t − U‖₂² ≥ ε` for all
`t ≤ c nᵈ log n`.

Each theorem takes as hypotheses the regime (`2 ≤ d`, `criticalProbability d < p`, `p < 1`; `d = 2`
for Theorem 1.3) and the literature inputs its proof uses, listed in
[Assumed literature inputs](#assumed-literature-inputs). The statements of Theorems 1.1, 1.3 and 6.5
are the definitions `Rigidity.Section3.LipschitzStmt`, `Rigidity.Section5.FastDecayStmt` and
`Rigidity.Section6.SlowMixingStmt`; Theorem 1.2 is also the theorem
`Rigidity.integer_valued_linear_growth`, whose statement is written out in full. The three
literature inputs of Theorem 6.5 are proved, and
[`Rigidity.Assembly.Unconditional.slow_mixing`](Rigidity/Proofs/Assembly/Unconditional.lean) is
Theorem 6.5 with the regime `2 ≤ d`, `criticalProbability d < p`, `p < 1` as its only hypotheses.

### All numbered results

The table lists the 48 numbered results in the order of the paper, with their LaTeX labels. Theorems
and lemmas in `Rigidity.Assembly.Main` are in
[`Rigidity/Proofs/Assembly/Main.lean`](Rigidity/Proofs/Assembly/Main.lean), and the other
`Rigidity.Assembly` theorems in `Rigidity/Proofs/Assembly/Section*.lean`. The eight results proved
first, with their own definitions, are in [`Rigidity/Frozen/`](Rigidity/Frozen/). For a statement
in `Rigidity.Assembly`, the definition `Rigidity.Section<n>.<Name>Stmt` that it concludes is in
[`Rigidity/Draft/`](Rigidity/Draft/). A quoted result is marked *quoted*, with the literature input
that states it, if any, and the theorem that proves this input, if any.

| Paper | Label | Lean declaration | Content |
| --- | --- | --- | --- |
| Theorem 1.1 | `theorem:lipschitz` | `Rigidity.Assembly.Main.lipschitz` | Lipschitz harmonic functions on `𝒞_∞` are constant. |
| Theorem 1.2 | `theorem:integer-valued-linear-growth` | `Rigidity.Assembly.Main.integerValuedLinearGrowth` | Integer-valued harmonic functions of linear growth are constant. |
| Theorem 1.3 | `theorem:fast-decay` | `Rigidity.Assembly.Main.fastDecay` | `d = 2`: integer Laplacian of finite support and decay faster than `\|x\|⁻¹` force finite support. |
| Lemma 2.1 | `lemma:finite-energy` | `Rigidity.finite_flip_full_measure` | A full-measure event still holds, almost surely, after every finite modification of the bonds. |
| Proposition 2.3 | `prop:well-connected` | quoted: `Rigidity.External.WellConnectedInput`; proved: `Rigidity.Percolation.wellConnected_input` | The box `Q_N` is well-connected with probability at least `1 − C exp(−c Nˢ)`. |
| Theorem 2.4 | `theorem:large scale-regularity` | quoted: `LatticeProb.External.ArmstrongDarioOrderZero`, `Rigidity.External.ArmstrongDarioOrderOneOrigin`; proved at order zero in every `d ≥ 2`: `Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds`; at order one at the origin in every `d ≥ 2` from the existence of the corrected planes: `Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_of_supercriticalBondCorrectorInput` | Large-scale regularity of harmonic functions on `𝒞_∞` above a minimal scale. |
| Theorem 2.5 | `theorem:first-order-corrector` | quoted: `LatticeProb.External.SupercriticalBondCorrectorInput`, `Rigidity.External.CorrectorQuantitativeInput`; the qualitative part proved in every `d ≥ 2`: `Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds` | Harmonic functions of linear growth are corrected planes `a + p·x + χ_p`; bounds on the corrector. |
| Proposition 2.6 | `prop:homogenizationellipticgreen` | `Rigidity.Assembly.Main.greenGradientHomogenization` | `∇ₓG(x, y)` is close to `Σᵢ ∇ℓ_{eᵢ}(x) ∂ᵢḠ(x − y)` above a minimal scale. |
| Proposition 2.8 | `prop:green-mixed-derivative` | `Rigidity.mixed_green` | Decay of the mixed derivative `∇ₓ∇_y G` above a minimal scale. |
| Lemma 2.13 | (none) | quoted, not used; the special case used in the proof of Proposition 5.12 (line 2124 of the corrected draft; the interior of a finite union of lattice squares) proved: `Rigidity.Assembly.polyominoJordan` (statement `Rigidity.Section2.PolyominoJordanStmt`); the general lemma is not formalized | A simply connected bounded planar domain whose boundary points are simple is bounded by a Jordan curve. |
| Lemma 2.14 | `lemma:jordan-curve-theorem-on-s2` | quoted: `Rigidity.External.JordanCurveTheoremSphere`; proved: `Rigidity.Topology.jordan_curve_theorem_sphere` | The Jordan curve theorem on the sphere `S²`. |
| Lemma 2.16 | `lemma:jordan-curves-theorem` | `Rigidity.Assembly.jordanCurves` | Arcs from `K` points of a Jordan curve to the north pole leave at least `K` components whose closure contains the pole. |
| Lemma 3.1 | `lemma:reduction-to-slope-e1` | `Rigidity.Assembly.reductionToSlopeE1` | A nonconstant Lipschitz harmonic function forces `ℓ_{e₁}` to be Lipschitz. |
| Proposition 3.2 | `prop:not-lipschitz` | `Rigidity.Assembly.Main.notLipschitz` | For every `L`, with positive probability `\|∇ℓ_{e₁}(0)\| > L`. |
| Lemma 3.3 | `lemma:compare-different-planes` | `Rigidity.Assembly.compareDifferentPlanes` | The change of the corrected planes when finitely many edges are removed. |
| Proposition 4.1 | `prop:exponential-growth-gadget` | `Rigidity.OpenGadget.exponential_growth_on_ambient_open_gadget` | A nonconstant integer-valued harmonic function on the gadget of height `n` has `\|u(t) − u(s)\| ≥ C 3ⁿ`. |
| Lemma 4.2 | `lemma:effective-resistance-recurrence` | `Rigidity.Assembly.effectiveResistanceRecurrence` | The gadget resistances satisfy `R₁ = 3`, `R_{n+1} = (3Rₙ + 2)/(Rₙ + 1)`. |
| Lemma 4.3 | `lemma:reduced-rational-recursion` | `Rigidity.Assembly.reducedRationalRecursion` | `Rₙ = A_{n+1}/Bₙ`. |
| Lemma 4.4 | `lemma:num-denom-recs` | `Rigidity.Gadget.numDenomRecs` | The recursions of the numerators `Aₙ` and denominators `Bₙ`. |
| Lemma 4.5 | `lemma:reduced-rational` | `Rigidity.Gadget.reducedRational` | `A_{n+1}` and `Bₙ` are coprime. |
| Lemma 4.6 | `lemma:exponential-growth` | `Rigidity.Gadget.exponentialGrowth` | `A_{n+1} > 3^{n−1}`. |
| Lemma 4.7 | `lemma:det-slope` | `Rigidity.Assembly.detSlope` | For a nonzero slope `q`, almost surely some edge carries a non-integer increment of `ℓ_q`. |
| Lemma 4.8 | `lemma:non-constant-on-gadget` | `Rigidity.Assembly.Main.nonConstantOnGadget` | Conditionally on `𝒞_∞ ∩ Q_R = H`, `ℓ_q` is nonconstant on a gadget with probability at least `c R^{−2d+2}`. |
| Lemma 4.9 | `lemma:ergodicity-lipschitz` | `Rigidity.Assembly.ergodicityLipschitz` | A nonconstant integer-valued harmonic function of linear growth yields an integer-valued corrected plane. |
| Proposition 4.10 | `prop:rational-matrix` | `Rigidity.Assembly.rationalMatrix` | No nonconstant integer-valued harmonic function is within `o(\|x\|)` of a harmonic quadratic. |
| Theorem 5.1 | `theorem:fast-decay-stronger` | `Rigidity.Assembly.Main.fastDecayDichotomy` | `d = 2`: if `u → 0` and `Δu ∈ ℤ`, then `lim sup \|x\| \|u(x)\| > 0` or `u` vanishes outside a ball. |
| Proposition 5.3 | `prop:fast-decay-stronger` | `Rigidity.Assembly.Main.fastDecayPotential` | The dichotomy of Theorem 5.1 for the potentials `u_f = Σ_y f(y) H(·, y)`. |
| Proposition 5.5 | `prop:not-mean-zero-log-growth` | `Rigidity.Assembly.logGrowth` | If `Σ f ≠ 0`, then `u_f` grows like `log \|x\|`. |
| Lemma 5.6 | `lemma:mean-zero-representation` | `Rigidity.Assembly.meanZeroRepresentation` | If `Σ f = 0`, then `u_f = Σ_e F(e) ∇H(·, e)` for a finitely supported field `F`. |
| Proposition 5.7 | `prop:gradient-trichotomy` | `Rigidity.Assembly.Main.gradientTrichotomy` | For `p ≠ 0` and `Σ f = 0`: `Σ f ℓ_p ≠ 0`, or `u_f − lim u_f` has finite support. |
| Proposition 5.8 | `prop:two-scale-expansion-mean-zero` | `Rigidity.Assembly.Main.twoScaleExpansion` | Two-scale expansion of `u_f` with error `C \|x\|^{−5/4}`. |
| Proposition 5.11 | `prop:level-set-of-harmonic-function` | `Rigidity.Assembly.Main.levelSetDensity` | Edges where `∇u_f ≠ 0` and `∇ℓ_p ≠ 0` have positive lower density in dyadic balls. |
| Proposition 5.12 | `prop:infinite-disjoint-paths-limit` | `Rigidity.Assembly.infiniteDisjointPaths` | A component of the level set `L₀` contains at most `\|supp f\| + 2` disjoint infinite paths. |
| Lemma 5.14 | `lemma:loops-around-annuli` | `Rigidity.Assembly.loopsAroundAnnuli` | Above a random scale, `𝒞_∞` has a loop around the origin in every annulus `Q_{2R} ∖ Q_R`. |
| Lemma 5.16 | `lemma:twod-strong-max-principle` | `Rigidity.Assembly.strongMaxPrinciple` | A maximum principle for bounded functions harmonic on an infinite proper subset. |
| Lemma 5.17 | `lemma:poles-sub-super-level-sets` | `Rigidity.Assembly.polesSuperLevelSets` | Every component of a super-level set `{u > a}` meets the support of `f`. |
| Lemma 5.18 | `lemma:long-nonzero-paths` | `Rigidity.Assembly.longNonzeroPaths` | Paths of `𝒞_∞` leaving `Q_{R'}` from `Q_R ⊇ supp f` avoid the zero set of `u`. |
| Lemma 5.19 | `lemma:no-thick-paths` | `Rigidity.Assembly.noThickPaths` | If `supp u` is infinite, no bi-infinite path in `L₀` has a whole side in `L₀`. |
| Proposition 5.20 | `prop:boundary-size-of-set` | `Rigidity.Assembly.boundarySize` | At most `C_f` disjoint paths join a biconnected subset of a level set to infinity. |
| Proposition 5.21 | `prop:disjoint-paths-to-infinty-exponential` | `Rigidity.Assembly.disjointPathsToInfinity` | `P(E_R(x)) ≥ 1 − C exp(−c Rˢ)`. |
| Lemma 5.23 | `lemma:renormalized-domination` | `Rigidity.Assembly.renormalizedDomination` | The renormalized process dominates site percolation of parameter `1 − C exp(−c Rˢ)`. |
| Proposition 5.24 | `prop:longpathsupercritrenormlatt` | `Rigidity.Assembly.longPathRenormalized` | Long paths cross many good boxes, outside an event of probability `C exp(−cK)`. |
| Lemma 5.25 | `lemma:good-event-lower-bound` | `Rigidity.Assembly.Main.goodEventLowerBound` | The good event `G(x, C_χ, K)` has probability at least `c > 0` for all large `K`. |
| Lemma 5.26 | `lemma:density-bound-good-event` | `Rigidity.Assembly.Main.goodEventDensity` | The density of good points in the triangles `T_L` tends to the probability of the good event. |
| Lemma 5.27 | `lemma:large-gradient-implies-not-in-level-set` | `Rigidity.Assembly.Main.largeGradientSensitive` | Near a good point, some edge has `∇ℓ_{e₁} ≠ 0` and `∇u_f ≠ 0`. |
| Lemma 5.28 | `lemma:finite-branches` | `Rigidity.Assembly.finiteBranches` | For every edge `(x₀, x₁)` of `𝒞_∞` as in the proof of Lemma 5.27, the pruned block-cut tree has at most `C_branches` branches. |
| Proposition 6.4 | `prop:integer-valued-compact-support` | `Rigidity.integer_valued_compact_support` | A finitely supported function on `ℤᵈ` with integer Laplacian is integer-valued. |
| Theorem 6.5 | `theorem:slow-mixing-percolation` | `Rigidity.Assembly.Main.slowMixing` | The sandpile chain on `𝒞_*(Q_n)` mixes in `L²` in time of order `nᵈ log n`. |

Two further forms are proved. Lemma 4.8 in joint form, with the gadget isolated in `H` and the lower
bound `c R^{−2d+2} min(𝔭, 1 − 𝔭)^N` on the probability that `𝒞_∞ ∩ Q_R = H` and `ℓ_q` is nonconstant
on the gadget, where `N` is the number of edges meeting `Q_R`, is
`Rigidity.Assembly.nonConstantOnGadgetJoint`; it supplies what the proof of Lemma 4.7 uses (C37).
Lemma 5.25 with the event `G₃` read on the edge
`(x, x + e₁)` as printed (see C32 below) is `Rigidity.Assembly.Main.goodEventLowerBoundDirectional`.

## Corrections to the published version

The corrected draft differs from arXiv v2 by the corrections below, each marked in
[`paper/percolation-harmonic-corrected.tex`](paper/percolation-harmonic-corrected.tex) by a comment
`% CORRECTION [Cn]` above the changed line, with its reason; a correction applied at several places
carries the tags `Cn`, `Cnb`, `Cnc`, …. The full list, with the reason for each change, is
[`paper/CORRECTIONS.md`](paper/CORRECTIONS.md), and the script
[`paper/make_corrected.py`](paper/make_corrected.py) produces the corrected draft from the arXiv
source by applying them. Each correction was tested in an independent model review. The corrected
draft carries 60 tags, for 38 numbered corrections C1–C39; there is no correction C27.

Corrections C4, C7, C9, C11, C12, C13, C14, C17, C18, C19, C21 and C29 change the statement of a
numbered result; C1, C2, C3, C23, C24 and C31 change a definition that statements use; C34, C38 and
C39 correct the quoted Theorem 2.4 and Lemmas 2.13 and 2.14. C32 is not a correction of a false
statement: it gives an alternative statement of Lemmas 5.25–5.27, and the published Lemma 5.25 is
also proved, as `Rigidity.Assembly.Main.goodEventLowerBoundDirectional`. The others change proofs
only. [`paper/CORRECTIONS.md`](paper/CORRECTIONS.md) also lists the three places where the Lean
proofs do not follow the printed argument: the finiteness of the blocks of the exploration graph in
the proof of Lemma 5.27, the constant `C_χ` of Lemma 5.27, and details of the proof of
Proposition 3.2.

| Change | Where | Kind | Published → corrected, and reason |
| --- | --- | --- | --- |
| C1 | Notation (triangle `T_L`); before Lemma 5.26 | definition | `\|x\| ≤ L` → `x₁ ≤ L`: with the `ℓ¹` norm `\|T_L\| ~ L²/2`, and Lemma 5.26 and its proof use the triangle `x₁ ≤ L`. |
| C2 | Continuum Green's function `Ḡ` (Section 2) | definition | `\|x\|` → `\|x\|₂`: the Euclidean norm (`\|x\|` is the `ℓ¹` norm). |
| C3 | Before Proposition 2.6 | definition | Defines the constant `κ(y)` in `d = 2` and the normalized Green's function `H`: with `G(y, y) = 0` the constant at infinity depends on the pole. |
| C4 | Proposition 2.6 | statement | `∇ₓG − ∇Ḡ − Σᵢ ∇χ_{eᵢ} ∂ᵢḠ` → `∇ₓG − Σᵢ ∇ℓ_{eᵢ} ∂ᵢḠ`: with the edge convention of the paper the printed left side is of order `\|∇Ḡ\|` at a leaf; the corrected planes also vanish on closed edges. |
| C5 | Proof of Proposition 2.6 | proof | Sign: `∇ℓ_ξ = −ξ` on open edges and `0` on closed edges. |
| C6 | Proof of Proposition 2.8 | proof | The bound holds for `H`; in `d = 2` it fails for `G` at a leaf. Mixed derivatives of `G` and `H` coincide. |
| C7 | Lemma 2.16 | statement | Distinct paths and a loop → simple paths meeting only at `N` and a Jordan curve avoiding `N`: as printed the lemma is false (two rays that merge leave one component). |
| C8 | Proof of Lemma 2.16 | proof | Indexing: `αᵢ` runs from `xᵢ` to `x_{i+1}`, indices modulo `K`. |
| C9 | Proposition 4.1 | statement | Harmonic in the interior of the closed rectangle → harmonic on the open gadget `T¹ₙ` for its induced graph: on the closed rectangle the claim is false. See [`paper/open-gadget-correction.tex`](paper/open-gadget-correction.tex). |
| C10 | Proof of Proposition 4.1 | proof | Direction of divisibility: `u(a) = (Bₙ/A_{n+1}) u(t)` is an integer and `gcd(A_{n+1}, Bₙ) = 1`. |
| C11 | Lemma 4.9 | statement | Adds "non-constant" and `\|p̲\| ≥ 1`: as printed the lemma is trivial (constants, slope `0`), and Lemma 4.7 needs a nonzero slope. |
| C12 | Theorem 5.1 | statement | `lim sup \|u(x)\|/\|x\| > 0` → `lim sup \|x\| \|u(x)\| > 0`: for `u → 0` the printed quantity is always `0`, and the theorem is false as printed. |
| C13 | Proposition 5.3 and Section 5 | statement | `u_f = Σ f(y) G(·, y)` → `u_f = Σ f(y) H(·, y)`: with `G`, a leaf at a pole gives a mean-zero potential tending to a nonzero constant, and Propositions 5.7, 5.8 and 5.11 fail. |
| C14 | Lemma 5.6 | statement | The representation with `H` (see C13); it holds for any kernel. |
| C15 | Proof of Theorem 5.1 | proof | Adds the identification `u = u_f`, which the printed proof uses without justification. |
| C16 | Proof of Proposition 5.5 | proof | The decay estimate is for `H` (see C6); for `G` it fails in `d = 2`. |
| C17 | Proposition 5.7 | statement | `p ∈ ℝ²` → `p ∈ ℝ² ∖ {0}`: for `p = 0`, `ℓ₀` is constant and noncompact mean-zero potentials exist. |
| C18 | Proposition 5.8 | statement | Sign of the leading term: `u_f − Σᵢ(…)∂ᵢḠ` → `u_f + Σᵢ(…)∂ᵢḠ`, since `∇Ḡ` is odd. |
| C19 | Proposition 5.11 | statement | The slope `p ≠ 0` is fixed, as in Proposition 5.7. |
| C20 | Proof of Lemma 5.16 | proof | Barrier sign: `G(·, a) ≤ 0` tends to `−∞`; the proof needs `v ≥ 0` tending to `+∞`. |
| C21 | Lemma 5.19 | statement | A component of `𝒞_∞ ∩ (ℝ² ∖ γ)` → `𝒞_∞ ∩ D` for a component `D` of `ℝ² ∖ γ`, as the proof uses. |
| C22 | Proof of Proposition 5.12 | proof | The connectors must join all `K + 2` initial points. |
| C23 | Good event `G₁` (before Lemma 5.25) | definition | Distances from the starting point `x`, so that `G₁(x, K)` is the translate of `G₁(0, K)`. |
| C24 | Good event `G₂` | definition | The printed bound `2 diam R'` is read as `4R'`, twice the diameter `2R'` of `Q_{R'}(x)`. |
| C25 | Proof of Theorem 6.5 | proof | The multiplicative harmonic function of the gadget equals `−1` at two sites, so its eigenvalue is `1 − 4/m`; the theorem is unchanged. |
| C26 | Proof of Lemma 3.1 | proof | The Lipschitz bound is for the chemical distance; membership in `𝒜₁` needs a comparison of the chemical and Euclidean distances. |
| C28 | Proof of Proposition 4.10 | proof | Adds the measurability of the event used with the ergodic theorem and the nonconstancy of `v`. |
| C29 | Proposition 5.11; proof of Proposition 5.7 | statement | `lim sup` → `lim inf`: Step 3 of the proof of Proposition 5.7 contradicts a positive lower limit, not a positive upper limit, and the proof of Proposition 5.11 gives the lower limit. |
| C30 | Proof of Proposition 5.11 | proof | The printed proof treats `p = e₁`; the changes for a general fixed `p ≠ 0` are given. |
| C31 | Good event `G₁` | definition | "There exists a path `γ` from `x`" → "every path `γ` from `x`": with the existential, `P[G₁] ≤ θ(𝔭) < 1`, and Lemma 5.27 applies `G₁` to a given path. |
| C32 | Good event `G₃`; proofs of Lemmas 5.25 and 5.27 | alternative statement | The edge `(x, x + e₁)` → an edge `(x, x')` of `𝒞_∞` at `x`: Proposition 3.2 bounds `\|∇ℓ_{e₁}(0)\|` without direction, and the proof of Lemma 5.27 uses `x + e₁` only as a neighbour of `x`. Lemma 5.25 with the printed event is also proved. |
| C33 | Proof of Theorem 6.5 | proof | Theorem 4.3 of Jerison, Levine and Pike concerns the chain with holding probability `1/(m + 1)`; for this chain the cited bound fails when every site has an even number of exits. The proof uses a site of the cluster with a single exit. |
| C34 | Theorem 2.4 (quoted) | statement | Adds part (iii) of the cited theorem, the local estimate that the proof of Proposition 2.6 uses. |
| C35 | Proof of Proposition 2.6 | proof | The density estimate for bond percolation in every `d ≥ 2` is cited from Dario and Gu, Proposition A.1, instead of Penrose and Pisztora, whose Theorem 1 concerns continuum percolation. |
| C36 | Proof of Lemma 4.8 | proof | Conditioning on `𝒞_∞ ∩ Q_R = H'` reweights the edges that the proof leaves free. The comparison environment opens the faces of `Q_R` instead of closing the edges at its boundary, and an averaging argument over `H'` gives the conditional bound. |
| C37 | Proof of Lemma 4.7 | proof | The event `𝒞_∞ ∩ Q_R = H` depends on edges outside `Q_R`, so its probability is not a product over `Q_R`; the lower bound and the isolation of the gadget come from the proof of Lemma 4.8. |
| C38 | Lemma 2.14 (quoted) | statement | "A continuous loop" → "a Jordan curve (a simple loop)", and "two finite open" → "two disjoint open": as printed the lemma is false for a constant loop or a figure-eight. |
| C39 | Lemma 2.13 (quoted) | statement | `Ω ⊆ ℤ²` → `Ω ⊆ ℝ²`: the domain lies in the plane, as in the cited remark of Rudin. |

## Standing assumptions and scope

1. **Regime.** As in the paper, `2 ≤ d` and `𝔭_c(d) < 𝔭 < 1` throughout, and `d = 2` in Section 5
   and Theorem 1.3. The statement definitions `…Stmt` in `Rigidity/Draft/` omit the regime, and the
   theorems in `Rigidity.Assembly` carry it as the hypotheses `2 ≤ d`, `criticalProbability d < p`
   and `p < 1` (Lemma 5.23 and Proposition 5.24 use only `criticalProbability 2 < p`). Lemma 2.1 is
   proved for every law of independent `Bernoulli(p)` bonds with `0 < p < 1`. Lemma 2.16 is
   deterministic, and so are the results on gadgets (Proposition 4.1, Lemmas 4.2 to 4.6) and
   Proposition 6.4; Propositions 4.1 and 6.4 are proved in every dimension `d ≥ 2`.
2. **Literature inputs.** Twelve results of the literature enter as explicit hypotheses of the
   theorems that use them; none is an `axiom`. They are listed in
   [Assumed literature inputs](#assumed-literature-inputs), with the eight of them that are proved.
3. **Measurability.** Some events quantify over the corrected planes of every configuration and are
   not shown to be measurable. For them, "with positive probability" means that the event contains a
   measurable event of positive probability (Proposition 3.2 and Lemmas 5.25 and 5.27), and an upper bound on
   a probability bounds the outer measure. Lemma 5.26 states that the good event is null-measurable,
   for every value of the parameters. In Lemma 4.8 the lower bound is for the outer measure of the
   event that `ℓ_q` is nonconstant on the gadget, which suffices for its use in Lemma 4.7.
4. **Theorem 6.5.** The chain is the random walk on the sandpile group `ℤ^V / Δ_V ℤ^V` of a largest
   open cluster `V` of `Q_n`, started from the class of the saturated sandpile `deg − 1`, each step
   adding a chip at a uniformly chosen site of `V`; a site of `V` topples by sending one chip along
   each open edge of `𝒞_∞`, and chips leaving `V` are lost. The statement asserts that almost surely,
   for all large `n`, some largest open cluster of `Q_n` lies in `𝒞_∞`, and the two bounds are proved
   for every such cluster that meets the boundary of `Q_n`; ties are covered by quantifying over every
   largest cluster.
5. **Parameters and readings.** The constant `C_f` of Proposition 5.20 and the constants `R`, `c₁`
   of Proposition 5.24, on which the events `E_R(x)` and `G₁` depend, are parameters of the
   statements that use them. Lemma 2.14 is stated for Jordan curves (correction C38), as is the
   literature input that states it. Lemma 5.28 concerns the objects of the proof of Lemma 5.27; it is
   stated for every edge `(x₀, x₁)` of `𝒞_∞` with `ℓ_{e₁}(x₁) > ℓ_{e₁}(x₀)` and `u(x₁) = u(x₀)`, which
   covers the neighbour of `x₀` given by the event `G₃` (C32). The norms and balls of each statement are those stated in its docstring in
   `Rigidity/Draft/`.
6. **Proof routes.** Theorem 1.2 is proved directly, by a finite-energy argument: almost surely a
   corrected plane whose increments are integers is constant. Lemma 4.7 is derived from this fact, and
   Lemma 4.9 from Theorem 1.2 (its hypothesis is then a null event). The argument of Section 4
   (Lemma 4.8 and Proposition 4.1 give Lemma 4.7, and Lemmas 4.7 and 4.9 give Theorem 1.2) is therefore
   verified piece by piece, not as a composition. The paper's proof of Lemma 4.7 uses the gadget bound
   in its isolated joint form, which is proved as `Rigidity.Assembly.nonConstantOnGadgetJoint`;
   Lemma 4.8 itself is proved as printed, by the argument of corrections C36. Where the Lean proofs
   of Lemma 5.27, Lemma 5.28 and Proposition 3.2 depart from the printed argument is listed in
   [`paper/CORRECTIONS.md`](paper/CORRECTIONS.md).
7. **Axioms.** The library contains no `sorry`, `admit`, `native_decide` or new `axiom`. The Lean
   declaration of each proved numbered result depends on exactly `propext`, `Classical.choice` and
   `Quot.sound`.
8. **Not formalized.** Lemma 2.13 in general (Remark 14.20 of Rudin), which no proof uses; its
   special case for the interior of a finite union of lattice squares, the form applied in
   the proof of Proposition 5.12, is proved as `Rigidity.Assembly.polyominoJordan` (the boundary is
   a closed lattice polygon without repeated corner, homeomorphic to the circle), and the Lean proof
   of Proposition 5.12 does not use it, since its loop runs around a spanning tree of the
   connectors. Theorems 2.4 and 2.5, which enter as
   literature inputs (Theorem 2.4 at order zero, `ArmstrongDarioOrderZero`, is also proved); the remarks, problems and conjectures; the figures. The other two quoted
   results, Proposition 2.3 and Lemma 2.14, enter as literature inputs that are proved.

## Assumed literature inputs

The table records the hypotheses of the original theorem statements. Eight of these propositions
are now proved: [`Rigidity.Percolation.supercritical_bond_uniqueness`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/BondUniqueness.lean),
[`Rigidity.Smoothing.micciancio_regev_smoothing`](Rigidity/Proofs/Smoothing/MicciancioRegev.lean),
[`Rigidity.Percolation.kesten_rectangle_crossing`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/KestenCrossing.lean),
[`Rigidity.Topology.jordan_curve_theorem_sphere`](Rigidity/Proofs/Topology/JordanCurveSphere.lean),
[`Rigidity.Percolation.wellConnected_input`](Rigidity/Proofs/Percolation/WellConnected.lean)
(Proposition 2.3; see the note below the table),
[`Rigidity.Proofs.S2.cluster_density_concentration`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Density/ClusterDensityConcentration.lean)
(`ClusterDensityConcentrationInput`, the density concentration of Dario and Gu; see
[Density concentration in every dimension](#density-concentration-in-every-dimension)),
[`Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/GeneralOrderZeroHolds.lean)
(`ArmstrongDarioOrderZero`, Theorem 2.4 at order zero in every dimension; see
[Order-zero regularity in every dimension](#order-zero-regularity-in-every-dimension)), and
[`Rigidity.Green.supercriticalBondGreenColumnExistence_holds`](Rigidity/Proofs/Green/GreenColumnHolds.lean)
(`SupercriticalBondGreenColumnExistence`, the existence and uniqueness of the Green columns, in
every dimension; see [Green columns for d ≥ 3](#green-columns-for-d--3)).
[`Rigidity.Assembly.WithProvedInputs`](Rigidity/Proofs/Assembly/ProvedInputs.lean) gives versions of
Theorems 1.1 and 1.2 without the uniqueness hypothesis, Theorem 1.3 without the uniqueness,
crossing, or sphere Jordan hypotheses, and Theorem 6.5 without the uniqueness or smoothing
hypotheses; `Rigidity.Percolation.wellConnected_input` supplies the hypothesis `WellConnectedInput`
of the versions of Theorems 1.1, 1.3 and 6.5, and
[`Rigidity.Assembly.Unconditional.slow_mixing`](Rigidity/Proofs/Assembly/Unconditional.lean) is
Theorem 6.5 with no literature hypothesis.
[`Rigidity.Assembly.WithProvedDensity`](Rigidity/Proofs/Assembly/ProvedDensity.lean) gives
Proposition 2.6 without the density-concentration hypothesis, and Theorem 1.3 without the
uniqueness, crossing, sphere Jordan, well-connectedness or density-concentration hypotheses.
[`Rigidity.Assembly.WithProvedOrderZero`](Rigidity/Proofs/Assembly/ProvedOrderZero.lean) gives the
theorems of `Rigidity.Assembly.Main` that take `ArmstrongDarioOrderZero`, and that version of
Theorem 1.3, without it.
[`Rigidity.Assembly.WithProvedGreenColumn`](Rigidity/Proofs/Assembly/ProvedGreenColumn.lean) gives
the theorems of `Rigidity.Assembly.Main` that take `SupercriticalBondGreenColumnExistence` with
every proved input supplied: Theorem 1.1 there takes only the two corrector inputs and the
quantitative Green estimate, and Theorem 1.3 these and the regularity of order one.
[`Rigidity.Assembly.WithProvedOrderOne`](Rigidity/Proofs/Assembly/ProvedOrderOne.lean) gives the three of
them that take the regularity of order one without it: Theorem 1.3 there takes only the two corrector
inputs and the quantitative Green estimate. The other inputs listed below remain hypotheses.

For Theorem 1.3, [`Rigidity.Assembly.WithPlanarInputs.fast_decay`](Rigidity/Proofs/Assembly/PlanarInputs.lean)
assumes only dimension-two forms of the qualitative and quantitative corrector estimates,
order-zero and order-one regularity, and the Green-column existence and quantitative estimates.
These six planar forms are stated in
[`PercolationClusterHomogenization/External/PlanarInputs.lean`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/External/PlanarInputs.lean); all six are
proved (see below), and Theorem 1.3 holds with no hypothesis
([`ProvedFluxWeakNorm.fast_decay_holds`](Rigidity/Proofs/Assembly/ProvedFluxWeakNorm.lean)).
The planar well-connectedness and cluster-density concentration estimates are supplied by
[`wellConnected_input_two`](Rigidity/Proofs/Percolation/PlanarWellConnected.lean) and
[`planar_cluster_density_concentration`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Density/PlanarDensityConcentration.lean).
The variant `fast_decay_of_green_exists` assumes, in place of the planar Green-column existence and
uniqueness, only the existence `Rigidity.External.SupercriticalBondGreenColumnExistsTwo`, stated in
[`Rigidity/Proofs/Section5/PlanarGreenUniqueness.lean`](Rigidity/Proofs/Section5/PlanarGreenUniqueness.lean),
and derives the uniqueness from order-zero regularity. This existence is proved
([`planar_greenColumn_exists`](Rigidity/Proofs/Section5/PlanarGreenExistence.lean)), so
[`fast_decay_of_planar_estimates`](Rigidity/Proofs/Assembly/PlanarGreenInputs.lean) assumes only
five planar inputs: the qualitative and quantitative corrector estimates, order-zero and order-one
regularity, and the quantitative Green estimate; see
[Green columns and the coarse-grained cluster for d = 2](#green-columns-and-the-coarse-grained-cluster-for-d--2).

The Green-column input `SupercriticalBondGreenColumnExistence` is proved for `d ≥ 3`
([`Rigidity.Green.greenColumnExistence_of_three_le`](Rigidity/Proofs/Green/SupercriticalGreenColumn.lean)),
and [`Rigidity.Green.supercriticalBondGreenColumnExistence_of_orderZeroTwo`](Rigidity/Proofs/Green/SupercriticalGreenColumn.lean)
derives it in every dimension from the planar order-zero estimate `ArmstrongDarioOrderZeroTwo`.
The planar case is proved, so the input is proved in every dimension
([`Rigidity.Green.supercriticalBondGreenColumnExistence_holds`](Rigidity/Proofs/Green/GreenColumnHolds.lean));
see [Green columns for d ≥ 3](#green-columns-for-d--3).

In dimension two the planar inputs are reduced further. `ArmstrongDarioOrderZeroTwo` follows from the harmonic
approximation `PlanarHarmonicApproximationTwo` of AD Lemma 7.1 and is proved. `SupercriticalBondCorrectorInputTwo`
(R2) follows from `ArmstrongDarioOrderZeroTwo` with the existence of corrected planes and the bound `dim 𝒜₁ ≤ 3`
(see [Order-zero regularity and the planar corrector input from Lemma 7.1](#order-zero-regularity-and-the-planar-corrector-input-from-lemma-71)), and these
are proved too, so R2 is proved in dimension two for `𝔭_c(2) < 𝔭 < 1` with no hypothesis
(`supercriticalBondCorrectorInputTwo_holds`; see
[Corrected planes, the dimension of the harmonic functions of linear growth and the corrector input in dimension two](#corrected-planes-the-dimension-of-the-harmonic-functions-of-linear-growth-and-the-corrector-input-in-dimension-two)).
The planar Green-column input (R6) follows from it with no further hypothesis
(`supercriticalBondGreenColumnExistenceTwo_holds`), the quantitative
corrector estimate from it with Theorem 1 of Dario, and the quantitative Green estimate with Theorem 1 of Dario and Gu
(see [The corrector estimate, the Green column and the Green function estimate in dimension two](#the-corrector-estimate-the-green-column-and-the-green-function-estimate-in-dimension-two)).
The quantitative sublinearity (1.22) of AD is proved in dimension two, and with it Lemma 3.2 of Dario (see
[The quantitative sublinearity of the correctors in dimension two](#the-quantitative-sublinearity-of-the-correctors-in-dimension-two)).
The multiscale Poincaré inequality, the concentration inequality and Lemma 3.3 of Dario are proved too, so Theorem 1 of
Dario and the quantitative corrector estimate (R5) hold in dimension two (`darioOptimalCorrectorTwo_holds`,
`correctorQuantitativeInputTwo_holds`; see
[Steps 1 and 2 of Lemma 3.3 in flip form and Lemma 3.5 for the planar partition](#steps-1-and-2-of-lemma-33-in-flip-form-and-lemma-35-for-the-planar-partition)).
In every dimension, the quantitative corrector estimate `CorrectorQuantitativeInput` follows from
Theorem 1 of Dario in dimension `d ≥ 3` (`DarioOptimalCorrectorThree`: `|χ_q(x) - χ_q(y)| ≤ O_s(C|q|)`)
and the qualitative corrector input, by the printed proof of Proposition 2.12 of Dario and Gu
([`Rigidity.Corrector.GeneralDim.correctorQuantitativeInput_of_dario`](Rigidity/Proofs/Corrector/CorrectorQuantitative.lean);
the dimension two case is `correctorQuantitativeInputTwo_holds`).
The concentration inequality of Dario (Proposition 2.17) holds in every dimension
([`Rigidity.Corrector.GeneralDim.concentration_holds`](Rigidity/Proofs/Corrector/Concentration.lean)).
The multiscale Poincaré inequality (2.26) of Dario (Proposition 2.19) holds in every dimension
([`Rigidity.Poincare.GeneralDim.multiscalePoincare_holds`](Rigidity/Proofs/Poincare/GeneralMultiscalePoincare.lean),
the lattice argument of the planar proof on `ℤ^d`, with a vector field of prescribed divergence
along the coordinate paths in place of the planar row-and-column field).
The volume regularity and the weak Poincaré inequality on the Euclidean balls of the infinite cluster (Barlow 2004,
Theorem 2.18 with Lemma 2.19, and Proposition 2.7 of Dario and Gu in its weak form) hold in every dimension `d ≥ 2`
(`Rigidity.WeakPoincare.clusterGoodBalls_holds`, `clusterVeryGoodBalls_holds`, `clusterPoincare_holds`; see
[Good balls of the infinite cluster and Proposition 2.7 of Dario and Gu in every dimension](#good-balls-of-the-infinite-cluster-and-proposition-27-of-dario-and-gu-in-every-dimension)).
The heat kernel of the variable-speed walk on the open graph of `ℤ^d` is defined, and the Carne–Varopoulos bound and
the Gaussian upper bound of Barlow (Theorem 4 of Dario and Gu, with the prefactor `t^{−d/2}`) are proved in every
dimension `d ≥ 2`
(`Rigidity.Green.carneVaropoulos_holds`, `Rigidity.BarlowLattice.barlowGaussianUpperBound_holds`; see
[The heat kernel and the Gaussian upper bound of Barlow in every dimension](#the-heat-kernel-and-the-gaussian-upper-bound-of-barlow-in-every-dimension)).

The input `ArmstrongDarioOrderOneOrigin` is proved in every dimension from the existence of the corrected planes,
the first part of `SupercriticalBondCorrectorInput`
([`armstrongDarioOrderOneOrigin_of_supercriticalBondCorrectorInput`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/CorrectorSublinearFromRegularity.lean)):
the mesoscopic estimate (7.18) of AD at `k = 2` is proved in every dimension, and it makes the sublinearity of the
corrected planes quantitative. Theorem 1.3 and the two other theorems that take the input are restated without it
in [`Rigidity.Assembly.WithProvedOrderOne`](Rigidity/Proofs/Assembly/ProvedOrderOne.lean); see
[Regularity of order one at the origin from the mesoscopic estimate](#regularity-of-order-one-at-the-origin-from-the-mesoscopic-estimate).
In dimension two, (7.18) at `k = 2` is proved from the estimates on squares of the proof of AD Lemma 7.1, and
`ArmstrongDarioOrderOneOriginTwo` (R4) from them with Theorem 1 of Dario alone (the existence of corrected planes and
the bound `dim 𝒜₁ ≤ 3` are proved); see
[Lemma 7.3 at k = 2 and regularity of order one at the origin in dimension two](#lemma-73-at-k--2-and-regularity-of-order-one-at-the-origin-in-dimension-two).
Theorem 1 of Dario being proved, R4 holds (`armstrongDarioOrderOneOriginTwo_holds`). Of the five planar inputs of
`fast_decay_of_planar_estimates` only the quantitative Green estimate remains, and Theorem 1.3 follows from it alone
([`fast_decay_of_greenQuantitative`](Rigidity/Proofs/Assembly/PlanarDarioGu.lean)), from Theorem 1 of Dario and Gu
alone (`fast_decay_of_darioGu`), or from the inputs of that theorem: `hSec` and the Gaussian upper bound of Barlow
(`fast_decay_of_sections_barlow`), or Proposition 2.13, Theorem 3 and that bound (`fast_decay_of_flux_gradient_barlow`).
The Gaussian upper bound of Barlow is proved (`barlowGaussianUpperBoundTwo_holds`; see
[The Gaussian upper bound of Barlow in dimension two](#the-gaussian-upper-bound-of-barlow-in-dimension-two)), and so is
Proposition 2.13 (`darioGuFluxWeakNormTwo_holds`; see
[Proposition 2.13 of Dario and Gu in dimension two](#proposition-213-of-dario-and-gu-in-dimension-two)).
Theorem 1.3 follows from `hSec` alone
([`WithProvedBarlow.fast_decay_of_sections`](Rigidity/Proofs/Assembly/ProvedBarlow.lean)), or from Proposition 2.13 and
Theorem 3 alone (`WithProvedBarlow.fast_decay_of_flux_gradient`). Theorem 3 is proved from the Gaussian upper bound of
Barlow (`darioGuGradientBoundTwo_holds`; see
[Theorem 3 of Dario and Gu in dimension two from Theorem 4, and Theorems 1 and 2 from Proposition 2.13 and Theorem 4](#theorem-3-of-dario-and-gu-in-dimension-two-from-theorem-4-and-theorems-1-and-2-from-proposition-213-and-theorem-4)),
so Theorems 1 and 2 of Dario and Gu, the quantitative Green estimate in dimension two, and Theorem 1.3 follow from
Proposition 2.13 alone
([`WithProvedBarlow.supercriticalBondGreenQuantitativeTwo_of_flux`](Rigidity/Proofs/Assembly/ProvedGradient.lean),
`fast_decay_of_flux`). Proposition 2.13 being proved, they hold with no hypothesis
([`ProvedFluxWeakNorm.darioGuHeatKernelTwo_holds`](Rigidity/Proofs/Assembly/ProvedFluxWeakNorm.lean),
`supercriticalBondGreenQuantitativeTwo_holds`, `fast_decay_holds`).
In every dimension, the quantitative Green estimate `SupercriticalBondGreenQuantitative` follows from Theorem 1 of
Dario and Gu in each dimension `d ≥ 3` alone (`DarioGuHeatKernelD d`;
[`ProvedFluxWeakNorm.supercriticalBondGreenQuantitative_of_heatKernel`](Rigidity/Proofs/Assembly/GreenQuantitativeEveryDim.lean)):
its planar case is proved, and so is the small-time bound of the heat kernel on `ℤ^d`, from the Carne–Varopoulos
bound (`openHeatSmallTimeD_holds`); see
[Theorem 2 of Dario and Gu for d ≥ 3 from Theorem 1, and in every dimension](#theorem-2-of-dario-and-gu-for-d--3-from-theorem-1-and-in-every-dimension).

| Lean name | Statement | Source | Results that use it |
| --- | --- | --- | --- |
| `LatticeProb.External.SupercriticalBondUniqueness` | `0 < 𝔭_c(d) < 1` for `d ≥ 2`, and for `𝔭_c(d) < p < 1` there is almost surely a unique infinite open cluster | Grimmett, (1.8), (1.10) and (1.11), pp. 13–14, and Theorem 8.1, p. 198; Burton and Keane, Theorem 2 | Theorems 1.1, 1.2, 1.3, 5.1, 6.5; Propositions 3.2, 4.10, 5.3, 5.5, 5.7, 5.8, 5.11, 5.12, 5.20; Lemmas 3.1, 3.3, 4.7, 4.9, 5.6, 5.14, 5.16, 5.17, 5.18, 5.19, 5.25, 5.27, 5.28 |
| `LatticeProb.External.SupercriticalBondCorrectorInput` | almost surely, each slope has a corrected plane, unique up to constants, and every harmonic function of linear growth is a corrected plane (qualitative part of Theorem 2.5) | DG, pp. 5–6, §2.3.1 and Proposition 2.12, p. 22; also AD, Theorem 2(i)–(ii), the remark on p. 9, and (1.22) | Theorems 1.1, 1.2, 1.3, 5.1; Propositions 2.6, 3.2, 4.10, 5.3, 5.7, 5.8, 5.11; Lemmas 3.1, 3.3, 4.7, 4.8, 4.9, 5.25, 5.26, 5.27 |
| `Rigidity.External.CorrectorQuantitativeInput` | sublinearity and Lipschitz bound of the corrector above a minimal scale with stretched exponential moments (quantitative part of Theorem 2.5) | DG, Proposition 2.12, p. 22 (the gradient bound follows from the oscillation bound) | Theorems 1.1, 1.3, 5.1; Propositions 2.6, 3.2, 5.3, 5.7, 5.8, 5.11; Lemmas 5.25, 5.27 |
| `LatticeProb.External.ArmstrongDarioOrderZero` | harmonic functions in large balls at the origin are close to constants, above a minimal scale with stretched exponential moments, and `𝒜₀(𝒞_∞)` is one-dimensional (Theorem 2.4 at order zero) | AD, Theorem 2(iii) at `k = 0` with (1.16), p. 8; the dimension statement after Theorem 2, p. 9; §1.2, p. 5 | Theorems 1.1, 1.3, 5.1; Propositions 2.8, 3.2, 5.3, 5.7, 5.11; Lemmas 3.3, 4.8, 5.25, 5.27 |
| `Rigidity.External.ArmstrongDarioOrderOneOrigin` | large-scale `C^{1,1}` regularity at the origin: approximation by harmonic functions of linear growth (Theorem 2.4, part (iii) at `k = 1`) | AD, Theorem 2(iii) at `k = 1` with (1.16), p. 8 | Theorems 1.3, 5.1; Propositions 2.6, 5.3, 5.8 |
| `LatticeProb.External.SupercriticalBondGreenColumnExistence` | for each pole, almost surely the Green's function of `𝒞_∞` exists and is unique | DG, p. 4 (the definitions around (1.8)) and p. 58; DG state it without proof | Theorems 1.1, 1.3, 5.1; Propositions 3.2, 5.3, 5.7, 5.11; Lemmas 3.3, 5.25, 5.27 |
| `LatticeProb.External.SupercriticalBondGreenQuantitative` | comparison of the Green's function of `𝒞_∞` with the homogenized Green's function `Ḡ` above a minimal scale | DG, Theorem 2, p. 5, (1.10)–(1.11), with `Ḡ` as in (1.9) and the conductivity `ā = θ(𝔭)σ̄²/2` of p. 3 | Theorems 1.1, 1.3, 5.1; Propositions 2.6, 2.8, 3.2, 5.3, 5.5, 5.7, 5.8, 5.11; Lemmas 5.25, 5.27 |
| `Rigidity.External.ClusterDensityConcentrationInput` | concentration of the density of `𝒞_∞` in triadic cubes | DG, Proposition A.1, p. 60 | Theorems 1.3, 5.1; Propositions 2.6, 5.3, 5.8 |
| `Rigidity.External.WellConnectedInput` | a box of radius `N` is well-connected with probability at least `1 − C exp(−c Nˢ)` (Proposition 2.3) | Proposition 2.3 of the paper; see the note below the table | Theorems 1.1, 1.3, 5.1, 6.5; Propositions 3.2, 5.3, 5.7, 5.8, 5.11, 5.21, 5.24; Lemmas 3.1, 5.6, 5.23, 5.25, 5.27 |
| `Rigidity.External.KestenRectangleCrossing` | in supercritical planar bond percolation, `[0, m] × [0, n]` has an open crossing in its long direction outside an event of probability at most `C (m + 1) exp(−c n)` | Kesten, Theorem 11.1, (11.4), p. 338, for the bond percolation graph of Example 2.1(ii), pp. 13–14 | Theorems 1.3, 5.1; Propositions 5.3, 5.7, 5.11, 5.12, 5.20, 5.21, 5.24; Lemmas 5.14, 5.19, 5.23, 5.27, 5.28 |
| `Rigidity.External.JordanCurveTheoremSphere` | the complement of a simple closed curve in `S²` has exactly two components, both open, each with the curve as its frontier (Lemma 2.14) | Hatcher, Proposition 2B.1 and the remark after it, p. 169; the paper cites Rudin, Chapter 14 (also Newman, Chapter V) | Theorems 1.3, 5.1; Propositions 5.3, 5.7, 5.11, 5.12, 5.20; Lemmas 2.16, 5.19, 5.27, 5.28 |
| `Rigidity.External.MicciancioRegevSmoothing` | the smoothing parameter of a lattice of rank `k` is at most `√(ln(2k(1 + 1/ε))/π)` times its `k`-th successive minimum | Micciancio and Regev, Lemma 3.3 (p. 11 of the preprint of the journal version, 14 December 2005), with the isometry remark of Jerison, Levine and Pike, Lemma 4.2 | Theorem 6.5 |

**`WellConnectedInput`.** This is Proposition 2.3 of the paper: a box of radius `N` is well-connected
with probability at least `1 − C exp(−c Nˢ)`, with `s` depending on `d` only. The sources that the
paper cites for it (Pisztora, Theorem 3.2; Penrose and Pisztora, Theorem 5; Antal and Pisztora, (2.24))
state single-scale forms. The statement follows from Couronné and Messikh, Theorem 5, (7), p. 8
(`d = 2`), and from Pisztora's box estimate, his Theorems 1.2 and 3.1 as recalled by Penrose and
Pisztora, p. 35 (`d ≥ 3`), by a union bound over the subcubes, with `s = 1/(d(10d)²)`. For
`d ≥ 3`, Pisztora's estimate holds above the threshold of percolation in slabs, which equals
`𝔭_c(d)` by the theorem of Grimmett and Marstrand; that theorem is proved, in a finite-volume form,
in [Slab connectivity above the critical point](#slab-connectivity-above-the-critical-point). For
`d ≥ 3` the statement of `WellConnectedInput` is proved, with the box estimate replaced by crossing
estimates from slab connectivity; see
[Well-connected cubes and finite clusters for d ≥ 3](#well-connected-cubes-and-finite-clusters-for-d--3).
For `d = 2` it is proved from Kesten's rectangle-crossing estimate in place of the estimate of
Couronné and Messikh; see
[Proposition 2.3 and the density concentration for d = 2](#proposition-23-and-the-density-concentration-for-d--2).
The two cases together prove `WellConnectedInput`, as `Rigidity.Percolation.wellConnected_input`.

Each input was checked against its source in an independent model review. Page numbers refer to the
arXiv versions listed below. AD: S. Armstrong and P. Dario, *Elliptic regularity and quantitative
homogenization on percolation clusters*, Comm. Pure Appl. Math. 71 (2018); arXiv:1609.09431v2.
DG: P. Dario and C. Gu, *Quantitative homogenization of the parabolic and elliptic Green's functions
on percolation clusters*, Ann. Probab. 49 (2021); arXiv:1909.10439v4. Grimmett: G. Grimmett,
*Percolation*, 2nd edition, Springer, 1999. Burton and Keane: R. M. Burton and M. Keane, *Density and
uniqueness in percolation*, Comm. Math. Phys. 121 (1989), 501–505. Couronné and Messikh: O. Couronné
and R. J. Messikh, *Surface order large deviations for 2D FK-percolation and Potts models*, Stochastic
Process. Appl. 113 (2004), 81–99; arXiv:math/0303117v1. Pisztora: A. Pisztora, *Surface order large
deviations for Ising, Potts and percolation models*, Probab. Theory Related Fields 104 (1996).
Penrose and Pisztora: M. D. Penrose and A. Pisztora, *Large deviations for discrete and continuous
percolation*, Adv. Appl. Probab. 28 (1996). Antal and Pisztora: P. Antal and A. Pisztora, *On the
chemical distance for supercritical Bernoulli percolation*, Ann. Probab. 24 (1996). Kesten: H. Kesten,
*Percolation Theory for Mathematicians*, Birkhäuser, 1982. Hatcher: A. Hatcher, *Algebraic Topology*,
Cambridge University Press, 2002. Rudin: W. Rudin, *Real and Complex Analysis*. Newman: M. H. A.
Newman, *Elements of the Topology of Plane Sets of Points*. Micciancio and Regev: D. Micciancio and O.
Regev, *Worst-case to average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007).
Jerison, Levine and Pike: D. C. Jerison, L. Levine and J. Pike, *Mixing time and eigenvalues of the
abelian sandpile Markov chain*, Trans. Amer. Math. Soc. 372 (2019).

The precise Lean statement of each input, with its pinpoint reference and its conventions, is in
[`Rigidity/External/`](Rigidity/External/) or, for the inputs in the namespace
`LatticeProb.External`, in the directory `LatticeProb/External/` of Lattice-Probability at the
pinned commit (five of these files are not on its `main` branch). Eight results use no literature
input: Lemma 2.1, Proposition 4.1, Lemmas 4.2 to 4.6 and Proposition 6.4.
The library also declares `Rigidity.External.AntalPisztoraChemicalDistance` (Antal and Pisztora,
Theorem 1.1), which no numbered result uses.

## Slab connectivity above the critical point

For `d ≥ 3`, the theorem of Grimmett and Marstrand (G. R. Grimmett and J. M. Marstrand, *The
supercritical phase of percolation is well behaved*, Proc. R. Soc. Lond. A 430 (1990), 439–457;
Grimmett, Chapter 7) is proved for bond percolation, in the finite-volume form that the coarse
graining uses.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.uniformCubeSlabConnectivity_of_criticalProbability_lt`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Percolation/Blocks/SlabConnectivity.lean) | If `3 ≤ d` and `criticalProbability d < p`, then `UniformCubeSlabConnectivity d p`. |

The proposition `UniformCubeSlabConnectivity d p`, defined in
[`PercolationClusterHomogenization/Percolation/SlabTriadicPartition.lean`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Percolation/SlabTriadicPartition.lean),
states that there are a width `w ≥ 1` and a constant `ρ > 0` such that for every cube
`U = c + [0, n)ᵈ`, every direction `a` and every `k` with `(k + 1) w ≤ n`, any two vertices of the
slab `{x ∈ U : c_a + k w ≤ x_a < c_a + (k + 1) w}` are joined by an open path inside the slab with
probability at least `ρ`. The theorem depends on exactly `propext`, `Classical.choice` and
`Quot.sound`, and its axiom report is checked with those of the numbered results. The same file
derives from this bound the triadic stopping partition with its exponential size moment and its
localization bound
(`Rigidity.Percolation.triadic_partition_estimates_of_uniformCubeSlabConnectivity`), and the next
section derives from it Proposition 2.3 for `d ≥ 3`.

Steps 1 to 3 below follow Chapter 2 of D. Contreras, *Percolation on graphs of polynomial growth*,
ETH Zürich dissertation (2022), doi:10.3929/ethz-b-000585148, which proves the theorem of Grimmett
and Marstrand by a bootstrap. Step 4 is the route of the Lean proof from the bootstrap to slabs, a
static renormalization in slabs. The files are in
[`PercolationClusterHomogenization/Percolation/Bootstrap/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Percolation/Bootstrap/) and
[`PercolationClusterHomogenization/Percolation/Blocks/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Percolation/Blocks/).

1. **Local inputs** (`Bootstrap/LocalInputs.lean`), from the formal-math library (see
   [Copied code](#copied-code)): the uniqueness zone and the fact that large finite sets meet the
   infinite cluster (S. Martineau and V. Tassion, *Locality of percolation for abelian Cayley
   graphs*, Ann. Probab. 45 (2017), proof of Lemma 3.7 and Lemma 3.6), and the connection of a large
   cube to each face orthant of a larger cube (Grimmett, (7.14)–(7.16)).
2. **Seeds and sprinkling** (dissertation, Lemmas 2.3.2–2.3.5): a seed is joined to each face
   orthant of a large cube (`Bootstrap/SeedFaceLink.lean`); connection estimates compose by
   sprinkling (`Bootstrap/SprinkledExit.lean`, `Bootstrap/Composition.lean`); and a left seed of
   scale `3m'` reaches the anchors of the two subregions of scale `m'` (`Bootstrap/Relay.lean`,
   `Bootstrap/AnchorReach.lean`).
3. **Bootstrap** (dissertation, Theorem 2.1.2): above `𝔭_c(d)`, for every `ε > 0` there is a seed
   radius such that at arbitrarily large scales `m` every left seed and every right seed of scale
   `m` are joined inside `Q_{6m}` with probability at least `1 − ε`
   (`Rigidity.Percolation.exists_seed_link`, `Bootstrap/Link.lean`). The step from scale `m'` to
   scale `3m'` is `Bootstrap/Recursion.lean`, and its iteration `Bootstrap/Iteration.lean`.
4. **Static renormalization.** In a slab box with two long sides and thin sides `12m + 1`, blocks
   centred on a square grid of mesh `10m` are good when the uniqueness zone holds at the centre and
   the block is linked to its four neighbours (`Blocks/LinkEvents.lean`, `Blocks/SlabBlocks.lean`).
   The good blocks form a dependent site percolation of finite range and high density on a
   rectangle of `ℤ²`. The Peierls bound for such percolation, from Leonardo Bonanno's library (see
   [Copied code](#copied-code)), and a recursion over quadrants join any two vertices of the slab
   box with probability bounded below, uniformly in the size of the box
   (`Blocks/GridPeierls.lean`, `Blocks/SlabTwoPoint.lean`). Two vertices of a slab of a cube are
   joined through `d` intermediate vertices, changing one coordinate at a time inside a slab box,
   by Harris' inequality; small cubes are handled by finite energy (`Blocks/SlabConnectivity.lean`).

**Departure from the dissertation.** The probabilistic step of the bootstrap, Lemma 2.4.1, is proved
in a form with zones (`Bootstrap/TwoChances.lean`). Each of the two seeds lies in a zone of its
region and is conditioned to have its cut inside the zone closed at the level `p₀`. The two clusters
are explored, at the level `p₀` raised to `q = p₀ + δ` on the cut from the seed only, inside two
disjoint regions that meet the two subregions of the smaller scale exactly in their zones, and the
traces of the clusters in these zones are conditioned in the same way as the seeds. The recursion is
over seeds with this conditioning (`BootGood`, `Bootstrap/Recursion.lean`), so the conditioning of
the traces is the conditioning at the smaller scale. The levels `p₀` and `q` are the same at every
scale and each bond is sprinkled at most once, so the number of scales is not restricted.

## Well-connected cubes and finite clusters for d ≥ 3

For `d ≥ 3` and `𝔭_c(d) < p`, slab connectivity gives Proposition 2.3 of the paper and the
exponential decay of the radius of finite clusters (Grimmett, Theorem (8.21), due to J. T. Chayes,
L. Chayes, G. R. Grimmett, H. Kesten and R. H. Schonmann, *The correlation length for the
high-density phase of Bernoulli percolation*, Ann. Probab. 17 (1989), 1277–1302).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.wellConnected_of_three_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Percolation/Pisztora/WellConnected.lean) | If `3 ≤ d` and `criticalProbability d < p`, there are `c, C, s > 0` such that every cube `x + Q_N` fails to be well-connected with probability at most `C exp(−c Nˢ)`: the statement of `WellConnectedInput` at `d`, here with `s = 1/(100d³)` and without the hypothesis `p < 1`. |
| [`Rigidity.Percolation.wellConnectedInput_of_planar`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Percolation/Pisztora/WellConnected.lean) | The case `d = 2` of `WellConnectedInput` implies `WellConnectedInput`. |
| [`Rigidity.Percolation.exists_finite_cluster_radius_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Percolation/Pisztora/FiniteClusters.lean) | If `3 ≤ d` and `criticalProbability d < p`, the open cluster of `x` is finite and reaches `ℓ^∞`-distance `l` from `x` with probability at most `C exp(−c l)`, for all `x` and `l`. |
| [`Rigidity.Percolation.exists_finite_cluster_card_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Percolation/Pisztora/FiniteClusters.lean) | Under the same hypotheses, the open cluster of `x` is finite with at least `n` vertices with probability at most `C exp(−c n^{1/d})`. |

The four theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`.

1. **Crossing estimate** (`Rigidity.Percolation.crossing_fail_le`, `Pisztora/CubeEstimates.lean`).
   From the slab bound, a cube of side `n` has, for `10dw ≤ r < 10dn`, a crossing component joined
   inside the cube to every open path that leaves each `ℓ¹`-ball of radius `r/10`, except with
   probability at most `(d + 2)(n + 1)^{2d+1} exp(−c(⌊r/(10dw)⌋ − 1))`. The proof explores the
   slabs of the cube one at a time (`PercolationClusterHomogenization/Percolation/SlabRadiusCrossing.lean` and the modules
   it imports).
2. **Good cubes** (`Pisztora/GoodSubcube.lean`, `Pisztora/WellConnected.lean`). In `z + Q_M` take
   `t = ⌊M^{1/d}/(4 · 100^{1/d})⌋` and `r = 8t`. The crossing component is a largest cluster and
   contains every open path with at least `M/100` steps, because every other cluster has fewer than
   `(4t)^d ≤ M/100` vertices. So `z + Q_M` is good and crossing outside an event of probability at
   most `K exp(−κ M^{1/d})` (`Rigidity.Percolation.exists_not_goodSubcube_le`). A union bound over
   the cube `x + Q_N` and the at most `(4N + 1)^d (N + 1)` cubes `z + Q_M` that meet it with
   `N^{1/(10d)²}/2 ≤ M ≤ N/10` gives the statement. This is the derivation stated with the input,
   with Pisztora's box estimate replaced by the crossing estimate.
3. **Finite clusters** (`Pisztora/FiniteClusters.lean`). If `2t < l` and, for every `k`, the cube
   `x + Q_{M_k}`, `M_k = 2^{k+1} t`, has a crossing root joined inside it to every open path of
   coordinate diameter at least `M_k`, then the open path from `x` to distance `l` joins `x` to the
   first root, and a crossing path of the `k`-th cube, of diameter `M_{k+1}`, joins the `k`-th root
   to the next one; the cluster of `x` then meets every face of every cube and is infinite. By the
   crossing estimate the `k`-th condition fails with probability at most `A exp(−κ 2^k t)`, and the
   sum over `k` gives the bound. This route through the crossing estimate departs from the proof of
   Chayes, Chayes, Grimmett, Kesten and Schonmann. The volume bound follows, since a cluster of
   `ℓ^∞`-radius less than `l` has at most `(2l)^d` vertices.

## Proposition 2.3 and the density concentration for d = 2

For `d = 2` and `𝔭_c(2) < p < 1`, Kesten's rectangle-crossing estimate, which is proved (see
[Assumed literature inputs](#assumed-literature-inputs)), gives Proposition 2.3 of the paper and
the density concentration of Dario and Gu, Proposition A.1, in the plane. With the theorems of the
previous section, Proposition 2.3 holds in every dimension, and so does Theorem 6.5, with no
literature hypothesis.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.wellConnected_input_two`](Rigidity/Proofs/Percolation/PlanarWellConnected.lean) | `WellConnectedInputTwo`, the statement of `WellConnectedInput` at `d = 2`, here with `s = 1/800`. |
| [`Rigidity.Percolation.wellConnected_input`](Rigidity/Proofs/Percolation/WellConnected.lean) | `WellConnectedInput`: Proposition 2.3 for every `d ≥ 2`, from `wellConnected_input_two` and `wellConnected_of_three_le`. |
| [`Rigidity.Proofs.S2.planar_cluster_density_concentration`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Density/PlanarDensityConcentration.lean) | `ClusterDensityConcentrationInputTwo`, the statement of `ClusterDensityConcentrationInput` at `d = 2`: the density of the infinite cluster in a triadic square of side `3ᵐ` differs from `θ(𝔭)` by `O_{2/15}(C 3^{−m})`. |
| [`Rigidity.Assembly.Unconditional.slow_mixing`](Rigidity/Proofs/Assembly/Unconditional.lean) | Theorem 6.5 for every `d ≥ 2` and `𝔭_c(d) < p < 1`, with no literature hypothesis. |

The four theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`.

1. **Well-connected squares** (`Rigidity/Proofs/Percolation/PlanarGoodCube.lean`,
   `PlanarWellConnected.lean` and the modules they import). In the square `z + Q_M`, `M ≥ 10⁴`, let
   `w = ⌊√M⌋/100`. Outside an event of probability at most a polynomial in `M` times `exp(−c w)`,
   every horizontal and vertical strip of width `w` of the square has an open crossing in its long
   direction, and the square has a unique crossing cluster. The strip crossings then lie in the
   crossing cluster, every other open cluster of the square lies in a square of side `2w + 1`, so
   the crossing cluster is a largest cluster, and every open path with at least `M/100` steps is
   joined to it by a transverse crossing. The square is then good, and the union bound over
   subcubes stated with the input gives the statement with `s = 1/800 = 1/(d(10d)²)`. This route
   replaces the estimate of Couronné and Messikh by Kesten's estimate.
2. **Density concentration** (`Rigidity/Proofs/S2/`, from `BondEfronStein.lean` to
   `PlanarDensityConcentration.lean`). Resampling one bond changes the number of vertices of the
   infinite cluster in the square by at most the sum of the sizes of the finite clusters at the
   endpoints of the bond, before and after resampling. These sizes have stretched-exponential
   tails, because a loop of the infinite cluster in an annulus, obtained from rectangle crossings,
   encloses every finite cluster that meets the inner square (`ClusterDensityInfluenceBound.lean`,
   `PercolationClusterHomogenization/Proofs/Percolation/PlanarFiniteCluster.lean`). The Efron–Stein inequality for the
   product of the Bernoulli bonds, applied to the powers of the centred density `X`, gives for
   `n ≥ 2` the recursion
   `E|X|^{2n} ≤ (E|X|ⁿ)² + C n^{14} 3^{−2m} (E|X|^{2n})^{(n−1)/n}`
   (`Rigidity.Proofs.S2.planar_density_moment_recursion`). Solving it bounds the tail of `X` at
   the scale `C 3^{−m}` with the exponent `1/7`, which gives the stated exponent `2/15`. Dario and
   Gu derive the estimate from a concentration inequality of Efron–Stein type beyond the variance;
   the Lean proof replaces it by this iteration of the variance inequality.

## Density concentration in every dimension

For `d ≥ 3` and `𝔭_c(d) < p`, the finite-cluster estimates of
[Well-connected cubes and finite clusters for d ≥ 3](#well-connected-cubes-and-finite-clusters-for-d--3)
give the density concentration of Dario and Gu, Proposition A.1. With the case `d = 2` of the
previous section, `ClusterDensityConcentrationInput` is proved, and the versions of Proposition 2.6
and Theorem 1.3 in `Rigidity.Assembly.WithProvedDensity` do not take it as a hypothesis.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.S2.cluster_density_concentration`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Density/ClusterDensityConcentration.lean) | `ClusterDensityConcentrationInput`: for `d ≥ 2` and `𝔭_c(d) < p < 1`, the density of the infinite cluster in a triadic cube of side `3ᵐ` differs from `θ(𝔭)` by `O_{2(d−1)/(3d²+2d−1)}(C 3^{−dm/2})`; from `planar_cluster_density_concentration` (`d = 2`) and `clusterDensityConcentrationAt_of_three_le` (`d ≥ 3`, without the hypothesis `p < 1`). |
| [`Rigidity.Assembly.WithProvedDensity.green_gradient_homogenization`](Rigidity/Proofs/Assembly/ProvedDensity.lean) | Proposition 2.6 for every `d ≥ 2`, with the hypotheses `SupercriticalBondCorrectorInput`, `CorrectorQuantitativeInput`, `ArmstrongDarioOrderOneOrigin` and `SupercriticalBondGreenQuantitative`. |
| [`Rigidity.Assembly.WithProvedDensity.fast_decay`](Rigidity/Proofs/Assembly/ProvedDensity.lean) | Theorem 1.3, with the hypotheses `SupercriticalBondCorrectorInput`, `CorrectorQuantitativeInput`, `ArmstrongDarioOrderZero`, `ArmstrongDarioOrderOneOrigin`, `SupercriticalBondGreenColumnExistence` and `SupercriticalBondGreenQuantitative`. |

The three theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules
are in [`Rigidity/Proofs/S2/`](Rigidity/Proofs/S2/), from `DensityResamplingEnergy.lean` to
`ClusterDensityConcentration.lean`, and
[`PercolationClusterHomogenization/Proofs/Percolation/BondShellExponential.lean`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/BondShellExponential.lean).

1. **Influences** (`FiniteClusterVolumeMoments.lean`, `InfluenceRadiusTail.lean`,
   `InfluenceRootBoundHigh.lean`). As in the plane, resampling a bond `e` changes the number of
   vertices of the infinite cluster in the cube by at most the sizes of the finite clusters at the
   endpoints of `e`, before and after resampling, and changes it only if one of these finite
   clusters meets the cube. The volume tail `C exp(−c n^{1/d})` of finite clusters gives the
   moments `E|Δ_e|^r ≤ 4^{r+1} (dr)! a^{−dr} C`. By the radius tail `C exp(−c l)`, a bond at
   coordinate distance `n` from the cube changes the count with probability at most `C exp(−cn)`,
   and by the Cauchy–Schwarz inequality the moments of its influence decay exponentially in `n`.
   Summing over the bond shells around the cube gives
   `Σ_e ‖Δ_e‖²_{L^{2r}} ≤ C r^{3d+2} (3ᵐ + 1)^d`
   (`Rigidity.Proofs.S2.densityInfluenceRootBound_of_three_le`).
2. **Moment recursion** (`DensityResamplingEnergy.lean`, `DensityRealEncoding.lean`,
   `DensityMomentGrowth.lean`, `DensityConcentrationOfRoots.lean`). The argument of the planar case,
   written for every `d` under the hypothesis `DensityInfluenceRootBound d p (2γ)` that this sum is
   at most `C r^{2γ} (3ᵐ + 1)^d`. The Efron–Stein inequality for the powers of the centred density
   `X` gives, for `n ≥ 2`,
   `E|X|^{2n} ≤ (E|X|ⁿ)² + C n^{2γ+2} 3^{−dm} (E|X|^{2n})^{(n−1)/n}`
   (`Rigidity.Proofs.S2.density_moment_recursion`), hence `‖X‖_{Lⁿ} ≤ C n^{γ+1} 3^{−dm/2}` and
   `|X| ≤ O_s(C 3^{−dm/2})` for every `0 < s ≤ 1/(γ + 1)`
   (`Rigidity.Proofs.S2.isOsBond_density_of_rootBound`; at the exponent of the source,
   `Rigidity.Proofs.S2.clusterDensityConcentrationAt_of_rootBound`). For `d ≥ 3` the Lean proof
   takes `γ = ⌊(3d + 3)/2⌋`, so that `2γ ≥ 3d + 2`; since `2(γ + 1) ≤ 3d + 5`, the exponent
   `1/(γ + 1)` is at least `2(d − 1)/(3d² + 2d − 1)` (for `d = 3`, `1/7 ≥ 1/8`).

**Departures from Dario and Gu.** Dario and Gu prove Proposition A.1 with an exponential
Efron–Stein inequality (their Proposition A.3, from S. Armstrong and J. Lin, *Optimal quantitative
estimates in stochastic homogenization for elliptic equations in nondivergence form*, Arch. Ration.
Mech. Anal. 225 (2017), Proposition 2.2) and the volume tail `exp(−c n^{(d−1)/d})` of finite clusters
(their Theorem 6, from H. Kesten and Y. Zhang, *The probability of a large finite cluster in
supercritical Bernoulli percolation*, Ann. Probab. 18 (1990), 537–555). The Lean
proof replaces the exponential inequality by the iteration of the Efron–Stein variance inequality
over the moments, as for `d = 2`. For `d ≥ 3` it replaces the tail of Kesten and Zhang by the
exponential decay of the radius of finite clusters (Grimmett, Theorem (8.21)) and the volume tail
`exp(−c n^{1/d})` that follows from it, both proved from slab connectivity in
[Well-connected cubes and finite clusters for d ≥ 3](#well-connected-cubes-and-finite-clusters-for-d--3).
It obtains the scale `3^{−dm/2}` of the source with the exponent `1/(⌊(3d + 3)/2⌋ + 1)` for
`d ≥ 3` and `1/7` for `d = 2`, which are at least the exponent `2(d − 1)/(3d² + 2d − 1)` of the
source, and it derives the stated exponent from them. The case `d = 2` is the planar proof of the
previous section. The modules for `d ≥ 3` and every `d` follow the planar modules of the previous
section; no code is copied from another repository.

## Green columns and the coarse-grained cluster for d = 2

For `d = 2` and `𝔭_c(2) < p < 1`, almost surely every vertex of the infinite cluster is the pole of
a Green column. Dario and Gu state the existence of Green columns without proof (DG, p. 4 and
p. 58); the Lean proof derives it from Kesten's rectangle-crossing estimate and Proposition 2.3,
both proved. With the planar order-zero estimate, which gives the uniqueness, it supplies the
planar Green-column input, and Theorem 1.3 follows from five planar inputs.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Section5.planar_greenColumn_exists`](Rigidity/Proofs/Section5/PlanarGreenExistence.lean) | `SupercriticalBondGreenColumnExistsTwo`: for each vertex `y`, almost surely, if `y` is in the infinite cluster there is a function `g` on the cluster with `−Δg = δ_y`, `g(y) = 0` and `g(x) = o(|x|)`. |
| [`Rigidity.Assembly.WithPlanarInputs.supercriticalBondGreenColumnExistenceTwo_of_orderZero`](Rigidity/Proofs/Assembly/PlanarGreenInputs.lean) | `SupercriticalBondGreenColumnExistenceTwo`, the existence and uniqueness of planar Green columns, from `ArmstrongDarioOrderZeroTwo`. |
| [`Rigidity.Assembly.WithPlanarInputs.fast_decay_of_planar_estimates`](Rigidity/Proofs/Assembly/PlanarGreenInputs.lean) | Theorem 1.3, with the hypotheses `SupercriticalBondCorrectorInputTwo`, `CorrectorQuantitativeInputTwo`, `ArmstrongDarioOrderZeroTwo`, `ArmstrongDarioOrderOneOriginTwo` and `SupercriticalBondGreenQuantitativeTwo`. |

The three theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`.

1. **Green columns** ([`Rigidity/Proofs/Section5/PlanarGreenExistence.lean`](Rigidity/Proofs/Section5/PlanarGreenExistence.lean)
   and the modules `CrossingFlow`, `PlanarCrossingEvents`, `PlanarPotentialSublinear`,
   `WalkFamilyFlow` and `WellConnectedLink` of the same directory). The truncated potentials
   `Σ_{t<n} (p_t(y, y) − p_t(x, y)) / deg y` are bounded by the energy of any unit flow from `y` to
   `x` in the cluster, so a limit point is a Green column as soon as such flows exist with energy
   `o(|x|)`. At the scale `L = 4ᵐ` with `4|x|_∞ ≤ L < 16|x|_∞`, almost surely for all large `m`,
   the thin rectangles of width `m²` in `[−L, L]²` have open crossings in their long direction and
   the well-connected cubes of side `m^q` join them; `2ᵐ` parallel crossings carry a unit flow from
   `y` to `x` with energy at most `624 · 2ᵐ m^{3q+4} = o(4ᵐ)`. The effective resistance between `y`
   and `x` is therefore `o(|x|)`; the logarithmic bound on the resistance is not used. Two Green
   columns differ by a sublinear harmonic function, which is constant by the order-zero estimate
   and vanishes at `y`.
2. **The coarse-grained cluster** ([`Rigidity/Proofs/Percolation/`](Rigidity/Proofs/Percolation/),
   from `PlanarTriadicMesh.lean` to `PlanarNuLowerBound.lean`, with `ClusterCoarsening.lean` and
   `QuadraticVariation.lean`). The first steps of the proof of Theorem 2 of AD, from which
   Theorems 2.4 and 2.5 are quoted, are proved in the plane: the partition of `ℤ²` into good
   triadic squares (AD, Proposition 2.1), from strip meshes and Kesten crossings, with all moments
   of the sizes of its squares finite; the coarsening of functions on the cluster by the anchors of
   the partition squares, with its local error bounds; and the subadditive quantities `μ(U, q)` and
   `ν(U, p)` on the cluster `C_*(U)` of a resolved triadic square `U` of side `L`: their first and
   second variations (AD, Lemmas 4.2 and 4.3), the comparison of `μ` and `ν` ((4.8), Corollary 4.6
   and Lemma 4.7), the bounds `E[−μ(U, q)] ≤ C|q|₁²` ((4.12), in expectation) and
   `E[(μ(U, q) + |q|²/18)⁺] ≤ C|q|₁²/√L`, the subadditivity of `μ` and `ν` over the resolved
   subsquares of side `3ⁿ` up to errors of expectation at most `C|q|₁²|U|/√(3ⁿ)` (Lemma 4.8, (4.32)
   and (4.33)), and the lower bound `c|p|² ≤ E[ν(U, p)] + C|p|₁²/√L` ((4.31)). The planar
   corrector and regularity inputs remain hypotheses.

**Departures from Dario and Gu and from Armstrong and Dario.** The existence of Green columns,
stated by Dario and Gu without proof, is proved by the effective-resistance argument above. AD,
Lemmas 3.2 and 3.3, use paths from a vertex of the cluster of a partition cube to its anchor inside
the neighbouring cubes of the partition, which they assert without proof; in the plane the Lean
proof joins the vertices of `C_*(U)` and the anchors of adjacent partition squares by open paths
inside windows contained in `U` and in the square of side `9s` around the partition square of side
`s` (`PlanarWindows.lean`, `PlanarCubeCluster.lean`), and it bounds the weights of the coarsened
gradient through the reach, the overlap of these squares (`PlanarCoarseWeights.lean`,
`PlanarReachMoments.lean`), whose moments are all finite. In the proof of (4.33), the set `W` of
edges near the boundaries of the subcubes `z + □ₙ` is the set of exceptional vertices: those whose
subsquare `V(x)` of side `3ⁿ` is not resolved, or for which the square of side `9s` around their
partition square leaves `V(x)`; they are counted through the boundary vertices of `V(x)`
(`PlanarNuSubadditiveMoments.lean`). The lower bound (4.31) is proved in expectation, with a
deterministic multiple `λp` of the slope in place of the random slope of AD
(`PlanarNuLowerBound.lean`). No code is copied from another repository.

## Green columns for d ≥ 3

For `d ≥ 3` and `𝔭_c(d) < p < 1`, almost surely every vertex `y` of the infinite cluster is the
pole of exactly one Green column: a function `g` on the cluster with `−Δg = δ_y` that tends to zero
at infinity. Dario and Gu state the existence and uniqueness of Green columns without proof (DG,
p. 4 and p. 58). With the planar case of the previous section, the Green-column input
`SupercriticalBondGreenColumnExistence` follows from the planar order-zero estimate alone, and it
is proved with no hypothesis, the planar case being proved
(`supercriticalBondGreenColumnExistence_holds`). The same
route bounds the heat kernel of the cluster for `d ≥ 2` and the decay of the Green columns for
`d ≥ 3`, with a polynomial loss.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Green.latticeIsoperimetry`](Rigidity/Proofs/Green/LatticeIsoperimetry.lean) | for `d ≥ 2`, every finite `F ⊆ ℤᵈ` has at least `\|F\|^{(d−1)/d}` boundary edges. |
| [`Rigidity.Green.greenColumnExistence_of_three_le`](Rigidity/Proofs/Green/SupercriticalGreenColumn.lean) | for `d ≥ 3`, `𝔭_c(d) < p < 1` and each vertex `y`, almost surely, if `y` is in the infinite cluster there is exactly one Green column with pole `y`. |
| [`Rigidity.Green.supercriticalBondGreenColumnExistence_of_two`](Rigidity/Proofs/Green/SupercriticalGreenColumn.lean) | `SupercriticalBondGreenColumnExistence` from its planar case `SupercriticalBondGreenColumnExistenceTwo`. |
| [`Rigidity.Green.supercriticalBondGreenColumnExistence_of_orderZeroTwo`](Rigidity/Proofs/Green/SupercriticalGreenColumn.lean) | `SupercriticalBondGreenColumnExistence` from `ArmstrongDarioOrderZeroTwo`. |
| [`Rigidity.Green.supercriticalBondGreenColumnExistence_holds`](Rigidity/Proofs/Green/GreenColumnHolds.lean) | `SupercriticalBondGreenColumnExistence`, with no hypothesis. |
| [`Rigidity.Assembly.WithProvedGreenColumn`](Rigidity/Proofs/Assembly/ProvedGreenColumn.lean): `lipschitz`, `fast_decay`, `notLipschitz`, `fastDecayDichotomy`, `fastDecayPotential`, `gradientTrichotomy`, `levelSetDensity`, `goodEventLowerBound`, `largeGradientSensitive`, `goodEventLowerBoundDirectional` | the theorems of `Rigidity.Assembly.Main` that take `SupercriticalBondGreenColumnExistence`, with it and the other proved inputs supplied; they take only those of `SupercriticalBondCorrectorInput`, `CorrectorQuantitativeInput`, `ArmstrongDarioOrderOneOrigin` and `SupercriticalBondGreenQuantitative` that their proofs use. |
| [`Rigidity.Assembly.WithProvedCorrector`](Rigidity/Proofs/Assembly/ProvedCorrector.lean): `correctorQuantitativeInput_of_darioThree`, `fast_decay`, `fastDecayDichotomy`, `fastDecayPotential` | the three theorems of `Rigidity.Assembly.WithProvedOrderOne` with the qualitative corrector input supplied (`supercriticalBondCorrectorInput_holds`, every `d ≥ 2`); they take `CorrectorQuantitativeInput` and `SupercriticalBondGreenQuantitative`. The quantitative corrector input from `DarioOptimalCorrectorThree` (Theorem 1 of Dario in `d ≥ 3`) alone. |
| [`Rigidity.Assembly.WithProvedOrderOne`](Rigidity/Proofs/Assembly/ProvedOrderOne.lean): `fast_decay`, `fastDecayDichotomy`, `fastDecayPotential` | the three theorems of `Rigidity.Assembly.WithProvedGreenColumn` that take `ArmstrongDarioOrderOneOrigin`, with it supplied from `SupercriticalBondCorrectorInput` (`armstrongDarioOrderOneOrigin_of_supercriticalBondCorrectorInput`); they take `SupercriticalBondCorrectorInput`, `CorrectorQuantitativeInput` and `SupercriticalBondGreenQuantitative`. |
| [`Rigidity.Green.heat_le_of_two_le`](Rigidity/Proofs/Green/SupercriticalGreenBounds.lean) | for `d ≥ 2`, `𝔭_c(d) < p < 1` and each vertex `y`, almost surely, if `y` is in the infinite cluster, then for `0 ≤ t ≤ 1` there are `K` and `N` with `p_n(x, y) ≤ K n^{−(d/2 − 1/100)(1 − t)} exp(−t\|x − y\|²/(2n))` for all `n ≥ N` and all vertices `x` of the cluster. |
| [`Rigidity.Green.greenColumn_le_rpow_of_three_le`](Rigidity/Proofs/Green/SupercriticalGreenBounds.lean) | for `d ≥ 3`, almost surely, for every `δ > 0` the Green column `g` with pole `y` satisfies `0 ≤ g(x) ≤ K \|x − y\|^{2 − d + 1/50 + δ}` for `\|x − y\| ≥ R`. |
| [`Rigidity.Green.greenColumn_le_one_add_rpow_of_three_le`](Rigidity/Proofs/Green/SupercriticalGreenBounds.lean) | for `d ≥ 3`, almost surely, for every `δ > 0`, `0 ≤ g(x) ≤ K (1 + \|x − y\|)^{2 − d + 1/50 + δ}` at every vertex `x`. |

The twenty-one theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules
are in [`Rigidity/Proofs/Green/`](Rigidity/Proofs/Green/).

1. **Isoperimetry of `ℤᵈ`** (`LatticeIsoperimetry.lean`). The lattice `ℓ¹` Sobolev inequality
   `LatticeHC.sum_rpow_le_sum_abs_grad` (see [Copied code](#copied-code)) applied to the indicator
   of `F`.
2. **Isoperimetry of the cluster in a cube** (`CoarseIsoperimetry.lean`,
   `ClusterIsoperimetryWellConnected.lean`). Almost surely, for all large `R` the cube `y + Q_{2R}`
   is well-connected (Proposition 2.3, proved), so every cube `z + Q_M` of radius
   `M = ⌈(2R)^θ⌉`, `θ = 1/(10d)²`, meeting it is a good subcube, with largest cluster `V_z`. Every
   vertex `x` of the infinite cluster lies in `V_x`, and `V_z` meets `V_{z ± e_j}`. For a finite set
   `A` of vertices of the cluster in `y + Q_R`, let `F` be the set of `z` with `∅ ≠ V_z ⊆ A` and `P`
   the set of `z` for which `V_z` meets `A` without lying in it. Then `|A| ≤ |F| + |P|`; each
   `z ∈ P` gives a boundary edge of `A` with inner vertex in `z + Q_M`, so
   `|P| ≤ (2M + 1)ᵈ |∂A|`; and a lattice neighbour outside `F` of a point of `F` lies in `P`, so
   `|∂F| ≤ 2d |P|`. The isoperimetry of `ℤᵈ` applied to `F` gives
   `|∂A| ≥ |A|^{(d−1)/d} / (4d (2M + 1)ᵈ) ≥ κ R^{−1/(100d)} |A|^{(d−1)/d}` for every nonempty `A`.
3. **Faber–Krahn inequalities** (`Cheeger.lean`, `ClusterIsoperimetry.lean`). A discrete co-area
   inequality turns an isoperimetric inequality on a set into the Faber–Krahn inequality
   `a Σ_Ω g² ≤ |Ω|^{2/d} Σ |∇g|²` for the functions `g` supported in `Ω` inside it (the Cheeger
   inequality for the first Dirichlet eigenvalue). On the graph ball of radius `R` around `y`, which
   lies in `y + Q_R`, the constant is `a₀ R^{−1/(50d)}`.
4. **On-diagonal decay** (`LocalNash.lean`). The Faber–Krahn inequality gives a Nash inequality,
   and the decrease of `‖p_n(x, ·)‖²` gives `p_{2N}(x, x) ≤ deg(x) (c N)^{−d/2}` when the ball of
   radius `N` around `x` lies in the Faber–Krahn domain.
5. **Green functions** (`HeatDomination.lean`, `ClusterFaberKrahn.lean`, `TransientGreen.lean`,
   `ClusterGreenColumn.lean`). By the Cauchy–Schwarz inequality and reversibility,
   `p_n(x, y) ≤ K n^{−(d/2)(1 − 1/(50d))}` for `n ≥ max(n₀, dist(x, y))`, which is summable for
   `d ≥ 3`. Then `g = Σ_n p_n(·, y) / deg(y)` solves `−Δg = δ_y` and tends to zero at infinity, and
   the maximum principle gives the uniqueness.
6. **Heat kernel and Green column bounds** (`OffDiagonal.lean`, `ClusterHeatKernel.lean`,
   `GreenUpperBound.lean`, `ClusterGreenUpperBound.lean`, `GreenGlobalBound.lean`,
   `SupercriticalGreenBounds.lean`). The off-diagonal bound
   `p_{a+b}(x, y) ≤ √(deg y / deg x) √(p_{2a}(x, x) p_{2b}(y, y))` gives
   `p_n(x, y) ≤ K n^{−γ}`, `γ = (d/2)(1 − 1/(50d)) = d/2 − 1/100`, at every vertex `x`, and its
   weighted geometric mean with the Carne–Varopoulos bound
   `p_n(x, y) ≤ 2 √(deg y / deg x) exp(−dist(x, y)²/(2n))` of Lattice-Probability gives the
   transition bound of the table, since the Euclidean distance is at most the graph distance in the
   cluster. Summing the Carne–Varopoulos bound over `n < |x − y|^{2−θ}` and `K n^{−γ}` over the
   larger `n` gives `g(x) ≤ K |x − y|^{(2−θ)(1−γ)}`, hence the decay `2 − 2γ + δ = 2 − d + 1/50 + δ`
   of the Green columns.

**Departures from Dario and Gu.** Dario and Gu state the existence and uniqueness of Green columns
without proof; the Gaussian bounds of M. T. Barlow (*Random walks on supercritical percolation
clusters*, Ann. Probab. 32 (2004)) for the heat kernel of the cluster, which give them, are not used.
The Lean proof follows the route of P. Mathieu and E. Remy (*Isoperimetry and heat kernel decay on
percolation clusters*, Ann. Probab. 32 (2004)), isoperimetry, Faber–Krahn, Nash and on-diagonal
decay, with two changes: the isoperimetric inequality of the cluster is proved by one coarse
graining by good subcubes, with the polynomial loss `R^{−1/(100d)}` in place of the sharp inequality
for sets of size at least a power of `log R`, and only on-diagonal bounds, combined by the
Cauchy–Schwarz inequality, are used. The decay exponent `(d/2)(1 − 1/(50d)) > 1` is enough for
`d ≥ 3`. Barlow's Gaussian upper bound, as quoted by Dario and Gu (DG, §3.1), is
`p_t(x, y) ≤ C t^{−d/2} exp(−|x − y|²/(Ct))` for `|x − y| ≤ t` above a random time, and it gives
Green functions of order `|x − y|^{2−d}`; the bounds proved here lose the factor
`n^{1/100 + (d/2 − 1/100)t}` in the heat kernel and `|x − y|^{1/50 + δ}` in the Green columns, and
they are stated for the discrete-time simple random walk, whereas Dario and Gu use the
variable-speed continuous-time walk. The lattice Sobolev inequality is copied from
Lattice-High-Contrast-Homogenization and the step inequality of `LocalNash.lean` is adapted from
Lattice-Probability; see [Copied code](#copied-code).

## Multiscale Poincaré inequality

The proofs of Section 5 of Armstrong and Dario bound a function on a triadic cube by the spatial
averages of its gradient over the subcubes of every intermediate scale (AD, Proposition A.2).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Multiscale.multiscalePoincare_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Multiscale/Poincare.lean) | AD Proposition A.2 (`MultiscalePoincare d`, [`Defs.lean`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Multiscale/Defs.lean)): for every triadic cube `□_m` of `ℤᵈ`, every `n` with `m/2 ≤ n ≤ m` and every `u : ℤᵈ ∩ □_m → ℝ`, `‖u − (u)_{□_m}‖_{L̲²(□_m)} ≤ C 3^n ‖∇u‖_{L̲²(□_m)} + C Σ_{k=n}^{m−1} 3^k (the mean over the subcubes of size 3^k of the squared average of ∇u)^{1/2}` |
| [`Rigidity.Proofs.Multiscale.exists_multiscalePoincare_affine`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Multiscale/Affine.lean) | the same inequality for `u − ℓ_ξ`, with `ℓ_ξ(x) = ξ · x`, in the form used for Lemma 5.8 of AD |

The two theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules are
in [`PercolationClusterHomogenization/Proofs/Multiscale/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Multiscale/).

Departures from Armstrong and Dario:

- **Route.** AD smooth `u` and apply the continuum multiscale Poincaré inequality (their
  Proposition A.1, from Armstrong, Kuusi and Mourrat). The Lean proof extends `u` to the closed
  lattice cube with one more layer by clamping, applies the lattice multiscale Poincaré inequality
  with face-weighted block means `LatticeHC.exists_sum_sq_sub_vertexMean_le_multiscale` (see
  [Copied code](#copied-code)), and compares the block means with the subcube averages: the boundary
  layer contributes at most `C 3^{m/2}` times the gradient norm, which is at most `C 3^n` times it
  since `n ≥ m/2`.
- **Normalization.** The gradient sums count each edge once; AD's inner product counts both
  orientations, which changes only the constant.
- **Affine form.** The averages of `∇u` are compared with `(1 − 3^{−k}) ξ`, the exact average of the
  gradient of `ℓ_ξ` over a subcube, where AD write `ξ`; the difference adds at most `(m − n)|ξ|` to
  the right side.

## Partitions into good cubes and functional inequalities on the cluster

The proof of Theorem 2 of AD, from which Theorems 2.4 and 2.5 are quoted, starts from a random
partition of `ℤᵈ` into good triadic cubes (AD, §2) and from functional and elliptic inequalities on
the cluster above the scale of this partition (AD, §3). For every `d ≥ 2` and `𝔭_c(d) < p < 1`, the
partition and its stochastic integrability are proved, and so are the deterministic parts of the
inequalities of §3, with the Sobolev inequality on the cluster (AD, Proposition 3.4) for
`s ≥ d/(d − 1)` in three of its four cases.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.partition_estimates`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Partition/AlmostSure.lean) | AD Proposition 2.1 for the good cubes: almost surely every vertex lies in exactly one maximal stopping cube `□_𝒫(x)` of the partition `𝒫`, `E[exp(size(□_𝒫(x))/θ)] ≤ 2` for every vertex `x`, and the partition is approximately local. |
| [`Rigidity.Percolation.partition_estimates_general`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Partition/GeneralPartition.lean) | AD Proposition 2.1 for any random collection of good cubes whose failure probabilities are at most `C exp(−c 3^{ns})`, with `E[exp((size/θ)^s)] ≤ 2`. |
| [`Rigidity.Percolation.exists_minimalScale`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Partition/MinimalScaleCombined.lean) | AD Proposition 2.4 for `𝒫`: for every `t ∈ ℕ` there are `C` and a measurable random scale `M`, finite almost surely, with a stretched exponential moment such that, almost surely, `M < 3ᵐ` implies `Λ_t(□_m) ≤ C` and that every vertex of `□_m` lies in a partition cube of size at most `3^{dm/(d+t)}`. |
| [`Rigidity.Percolation.exists_minimalScale_general`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Partition/GeneralPartition.lean) | AD Proposition 2.4 for a random collection of good cubes satisfying AD (2.1) and (2.2) with `0 < s ≤ 1`. |
| [`Rigidity.Percolation.exists_measure_not_mem_goodCubes_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Partition/AlmostSure.lean) | AD Lemma 2.7: a triadic cube of scale `n` fails to be good with probability at most `C exp(−c 3ⁿ)`. |
| [`Rigidity.Percolation.TriadicCube.reachable_of_mem_goodCubes`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Partition/Adjacent.lean) | AD Lemma 2.8: the crossing clusters of two good cubes containing lattice neighbours, whose scales are equal or differ by one, are joined by an open path inside the union of the two cubes. |
| [`Rigidity.Percolation.reachable_partitionAnchor_of_walk`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Partition/Paths.lean) | AD Corollary 2.10: along every lattice walk from `x` to `y`, the anchors of `□_𝒫(x)` and `□_𝒫(y)` are joined by an open path inside the union of the partition cubes of the vertices of the walk. |
| [`Rigidity.Percolation.partition_sum_abs_sub_coarseAnchor_rpow_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PartitionCoarseData.lean) | AD Lemma 3.2 on a triadic cube `U` resolved by the partition, for `1 ≤ s < ∞`: `Σ_{x ∈ C_*(U)} \|w(x) − [w]_𝒫(x)\|^s ≤ C^s Σ_{z ∈ C_*(U)} 3^{sdρ(z)} \|∇w 1_{𝐚≠0}\|^s(z)`, with `ρ(z) ≥ scale(□_𝒫(z))` the reach scale. |
| [`Rigidity.Percolation.partition_sum_gradNormIn_coarseAnchor_rpow_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PartitionCoarseData.lean) | AD Lemma 3.3 on a resolved cube `U`, for `1 ≤ s < ∞`: `Σ_{x ∈ U} \|∇[w]_𝒫\|^s(x) ≤ C^s Σ_{z ∈ C_*(U)} size(□_𝒫(z))^{sd−1} \|∇w 1_{𝐚≠0}\|^s(z)`. |
| [`Rigidity.Percolation.exists_partition_sum_rpow_le_of_latticeSobolevOn`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PartitionSobolev.lean) | AD Proposition 3.4 on a resolved cube `U`, for `1 ≤ t ≤ s` and `w` of mean zero on `C_*(U)`, given the Sobolev inequality `Σ_U \|f − (f)_U\|^s ≤ S (Σ_U \|∇f\|^t)^{s/t}` of the lattice cube: `Σ_{C_*(U)} \|w\|^s ≤ K (Σ_{z ∈ C_*(U)} 3^{tdρ(z)} \|∇w 1_{𝐚≠0}\|^t(z))^{s/t}`. |
| [`Rigidity.Percolation.exists_partition_sum_sq_le_two`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PartitionSobolevTwo.lean) | AD Proposition 3.4 for `d = 2`, `s = 2` and `t = 1`, the Sobolev inequality of the planar lattice square being proved. |
| [`Rigidity.Percolation.IntegerCube.exists_latticeSobolevOn`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/SobolevCube.lean) | the Sobolev–Poincaré inequality of the integer cubes of `ℤᵈ`, `d ≥ 2`: for `s ≥ d/(d − 1)` and `t = sd/(s + d)` there is `S` with `Σ_B \|f − (f)_B\|^s ≤ S (Σ_B \|∇f\|^t)^{s/t}` on every cube `B`. |
| [`Rigidity.Percolation.exists_sum_rpow_le_of_eq_zero_on_boundary`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/SobolevZero.lean) | the Sobolev inequality with zero boundary values: `Σ_D \|f\|^s ≤ S (Σ_D \|∇f\|^t)^{s/t}` for every finite `D ⊆ ℤᵈ` and every `f` vanishing at the points of `D` with a lattice neighbour outside `D`. |
| [`Rigidity.Percolation.exists_partition_sum_rpow_le_of_sum_eq_zero`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/SobolevPartition.lean) | AD Proposition 3.4 on a resolved cube `U`, `d ≥ 2`, `s ≥ d/(d − 1)`, for `Σ_{C_*(U)} w = 0`: `Σ_{C_*(U)} \|w\|^s ≤ K (Σ_{z ∈ C_*(U)} 3^{tdρ(z)} \|∇w 1_{𝐚≠0}\|^t(z))^{s/t}`. |
| [`Rigidity.Percolation.exists_partition_sum_rpow_le_of_sum_coarsen_eq_zero`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/SobolevPartition.lean) | the same for `Σ_U [w]_𝒫 = 0`. |
| [`Rigidity.Percolation.exists_partition_sum_rpow_le_of_coarsen_eq_zero`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/SobolevCoarseZero.lean) | the same for `[w]_𝒫 = 0` at the points of `U` with a lattice neighbour outside `U`. |
| [`Rigidity.Percolation.exists_clusterSobolevTwo`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/SobolevReverseHolder.lean) | AD Proposition 3.4 with `s = 2` in the form of the Sobolev hypothesis `ClusterSobolevTwo` of the reverse Hölder inequality, on `C_*(U)` for every resolved cube `U`, `d ≥ 2`. |
| [`Rigidity.Proofs.Cluster.caccioppoli_cluster`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/Caccioppoli.lean) | AD Lemma 3.5: if `V ⊆ U`, every point of `U` with an open edge leaving `U` is at `ℓ∞` distance at least `r > 0` from `V`, and `u` is harmonic at the points of `U` all of whose open edges stay in `U`, then `Σ_V \|∇u 1_{𝐚≠0}\|² ≤ (8d/r²) Σ_{U ∖ int V} u²`. |
| [`Rigidity.Proofs.Cluster.reverse_holder_partition_cube`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/ReverseHolderPartition.lean) | AD Lemma 3.6, deterministic part: on the crossing cluster of a resolved triadic cube `□` of scale `m + 1`, given the Sobolev inequality of the lattice cube with exponents `2` and `2_* = 2d/(d+2)` and `Σ_{C_*(□)} 3^{2dsρ} ≤ C_G \|□\|`, every `u` harmonic on `C_*(□)` has `3^{−md} Σ_{C_*(□) ∩ □'} \|∇u\|² ≤ C (\|□\|⁻¹ Σ_{C_*(□)} \|∇u\|^{t2_*})^{2/(t2_*)}`, `□'` the central subcube and `1/s + 1/t = 1`. |
| [`Rigidity.Proofs.Cluster.gehring_triadic`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/Gehring.lean) | Gehring's lemma on the triadic cubes of `ℤᵈ`: for `0 < θ < 1`, a reverse Hölder inequality `avg_Q g ≤ A (avg_{Q^j} g^θ)^{1/θ}` on every subcube `Q` of `□` whose enlargement `Q^j` lies in `3□` gives `ε > 0` with `avg_□ g^{1+ε} ≤ C (avg_{3□} g)^{1+ε}`. |
| [`Rigidity.Proofs.Cluster.meyers_cluster`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/MeyersCluster.lean) | AD Proposition 3.8, deterministic part: for `u` harmonic on `U₀` and a partition of `3□` into triadic cells of comparable neighbouring sizes, if the triadic cubes `□'` above the cells carry sets `U' ⊆ U₀ ∩ 3□'` with the Sobolev inequality and a moment bound, and `Σ_{x ∈ □} size(x)^t ≤ K\|□\|`, then `E = \|∇u 1_{𝐚≠0}\|²` has `avg_□ E^{1+ε/2} ≤ C (avg_{3□} E)^{1+ε/2}`. |

The twenty-one theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules
are in [`PercolationClusterHomogenization/Proofs/Partition/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Partition/) and
[`PercolationClusterHomogenization/Proofs/Cluster/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Cluster/).

1. **Good cubes and the partition** (`CrossingCluster.lean`, `Adjacent.lean`, `PartitionCube.lean`,
   `AlmostSure.lean`, `GeneralPartition.lean`, `Measurability.lean`, `GoodCubesLocal.lean`). A
   triadic cube of scale at least two is well-connected when it is well-connected relative to its
   rounded three-quarter cube, the notion of the proof of Proposition 2.3; its crossing cluster
   `C_*(Q)` is the union of the open components of `Q` meeting all its faces (AD, Definition 2.5),
   which is then the component of a root. A cube is good when it and its children are well-connected
   (AD, Definition 2.6). Proposition 2.3 bounds the probability that a cube is not good (AD,
   Lemma 2.7), and the stopping-time construction of AD gives the partition `𝒫` into maximal good
   cubes, with its exponential moments, its approximate locality and the measurability of its
   cubes and anchors (AD, Proposition 2.1, for `𝒫` and for a general collection of good cubes).
2. **Paths** (`Adjacent.lean`, `Paths.lean`, `Resolved.lean`, `Local.lean`, `SetCluster.lean`). Two
   good cubes of comparable scales containing lattice neighbours have joined crossing clusters
   (AD, Lemma 2.8), which joins the anchors of the partition cubes along every lattice walk (AD,
   Corollary 2.10). On a cube `U` resolved by the partition (every partition cube meeting `U` lies in
   `U`), every vertex of `C_*(U)` is joined to the anchor of its partition cube by an open path inside
   `C_*(U)` and the `⌈s/10⌉`-neighbourhood of that cube of side `s`.
3. **Minimal scales** (`MinimalScale*.lean`, `Lambda*.lean`, `BadCubes.lean`, `PartitionSize.lean`,
   `StochasticAverage.lean`, `Resolution.lean`). Counting the bad cubes at every scale bounds the sums
   `Σ_{x ∈ □_m} size(□_𝒫(x))^τ` and `Λ_t(□_m)` above a random scale with a stretched exponential
   moment (AD, Proposition 2.4), and bounds the probability that a cube is not resolved.
4. **Coarsening** (`PercolationClusterHomogenization/Proofs/Cluster/`: `CoarseData.lean`, `CoarseInequalities.lean`,
   `CoarseNear.lean`, `CoarseReach.lean`, `PartitionCoarseData.lean`, `PartitionReach*.lean`). The
   coarsened function `[w]_𝒫(x) = w(z̄(□_𝒫(x)))` (AD, Definition 3.1) is compared with `w` along the
   paths of step 2 and its gradient along the paths of Lemma 2.8, which gives Lemmas 3.2 and 3.3 of
   AD with the weights described below; every moment of the reach of the partition is finite.
5. **Sobolev inequality** (`CoarseSobolev.lean`, `PartitionSobolev.lean`, `PlanarLatticeSobolev.lean`,
   `PartitionSobolevTwo.lean`, `Sobolev*.lean`). The Sobolev inequality of `ℤᵈ` with zero boundary
   values follows from the `ℓ¹` Sobolev inequality `LatticeHC.sum_rpow_le_sum_abs_grad` (see
   [Copied code](#copied-code)) applied to powers of `\|f\|` and Hölder's inequality; on a cube, a
   function of mean zero is reflected into the triple cube, cut off, and its mean is controlled by
   the `Lᵖ` Poincaré inequality of the cube. Lemmas 3.2 and 3.3 and these inequalities applied to
   `[w]_𝒫` give AD, Proposition 3.4; in the plane the lattice inequality from `ℓ¹` to `ℓ²` is also
   proved directly by comparing the values along rows and columns.
6. **Caccioppoli, reverse Hölder, Gehring and Meyers** (`Caccioppoli.lean`, `ReverseHolder*.lean`,
   `Gehring*.lean`, `Meyers*.lean`). The Caccioppoli inequality on a cluster (AD, Lemma 3.5) uses the
   local Caccioppoli inequality `caccioppoli_of_support` of Lattice-Probability; with the Sobolev
   inequality it gives the reverse Hölder inequality (AD, Lemma 3.6). Gehring's lemma on triadic
   cubes, from a Vitali covering, level sets and the layer-cake formula, applied to the energy
   averaged over the cells of a partition, gives the Meyers estimate (AD, Proposition 3.8).

Departures from Armstrong and Dario:

- **Good cubes.** Cubes of side three are not well-connected in the Lean definition, so good cubes
  have scale at least three: the test cubes of a cube of side three are single points, and the
  uniqueness of the crossing cluster and Lemma 2.8 need not hold for it. The anchor is the point of
  `C_*(Q)` closest to the centre of `Q` in the `ℓ∞` norm, with ties broken lexicographically (AD,
  Definition 3.1); AD, §2, use the Manhattan distance inside the middle child.
- **Paths and the weights of Lemma 3.2.** The proof of AD, Lemma 3.2, joins a vertex to its anchor
  inside the partition cubes at distance at most one from its own, from the identity
  `C_*(□_{n+1}(z)) ∩ □_n(z) = C_∞ ∩ □_n(z)` stated after AD, Definition 2.9, which need not hold at
  the vertices near the boundary of `□_n(z)`. The Lean proof uses the paths of step 2, inside the
  `⌈s/10⌉`-neighbourhood of the partition cube; this neighbourhood can meet much smaller partition
  cubes, so the weight `size(□_𝒫(z))^{sd}` of Lemma 3.2 becomes `3^{sdρ(z)}`, where the reach scale
  `ρ(z) ≥ scale(□_𝒫(z))` is the largest scale of a partition cube whose connecting paths may pass through `z`.
  Lemma 3.3 keeps the weights of AD. Lemmas 3.2 and 3.3 and Proposition 3.4 are proved on cubes
  resolved by the partition, with the weight `3^{tdρ(z)}` in Proposition 3.4.
- **Proposition 3.4.** Three of the four cases of AD are proved: `Σ_{C_*(U)} w = 0`,
  `Σ_U [w]_𝒫 = 0`, and `[w]_𝒫 = 0` on the lattice boundary of `U`, where AD ask for it on the
  boundary `∂_𝐚U` of the cluster, which is smaller; the lattice Sobolev inequality applied to `[w]_𝒫`
  uses the lattice boundary. The case `w = 0` on `∂_𝐚U` is not proved: AD apply Lemmas 3.2 and 3.3
  to the function equal to `[w]_𝒫` off the partition cubes at the boundary and to `0` on them, which
  needs an open path from each point of such a cube, inside cubes of comparable size, to a point of
  `∂_𝐚U`, and AD do not give one.
- **The Sobolev inequality of `ℤᵈ`** is proved, where AD obtain it from that of `ℝᵈ` by affine
  interpolation: with zero boundary values from the `ℓ¹` inequality, and on cubes by reflection and
  the `Lᵖ` Poincaré inequality. It discharges the Sobolev hypothesis `ClusterSobolevTwo` of the
  reverse Hölder inequality in every dimension (`exists_clusterSobolevTwo`); the reverse Hölder and
  Meyers theorems of the table keep the Sobolev inequality as a hypothesis in their statements. The Sobolev inequality on the clusters of integer cubes, and the
  reverse Hölder and Meyers theorems that use it with this hypothesis proved, are in
  [Clusters of integer cubes, the Meyers estimate and the coarse energy bounds toward Lemma 5.5](#clusters-of-integer-cubes-the-meyers-estimate-and-the-coarse-energy-bounds-toward-lemma-55).
- **Proposition 2.4** is proved by counting bad cubes, with a stretched exponential moment of some
  order `r > 0` for the minimal scale in place of every `r < sd/(d + t + s)`. The bound
  `Λ_t(U, 𝒮) ≤ O_{s/t}(C)` stated after the proof of AD, Proposition 2.1, is proved in the form
  `O_{s/(t+d)}(C)`, uniformly in `U` (`LambdaOs.lean`); the order `s/t` cannot hold uniformly when
  `U` is a single vertex, and AD do not use it.
- **Caccioppoli inequality.** Unit conductances, the `ℓ∞` distance of AD, and the constant `8d`;
  for conductances in `[λ, 1]` the constant is `8d/λ` (`caccioppoli_of_distance`).
- **Gehring's lemma.** AD obtain the discrete Gehring lemma from the continuum one by affine
  interpolation; the Lean proof proves it on triadic cubes of `ℤᵈ` directly. The reverse Hölder
  inequality of Step 1 of the proof of AD, Proposition 3.8, is used on the cubes inside `□_{m+1}`
  only, which is all the local Gehring lemma needs, with the energy on `C_*(□_{m+1}) ∩ □`. The
  moment exponent of the Meyers estimate is `t = (2 + ε)(1 + ε)(d + 1)/ε`, twice that of AD.
- **Deterministic parts.** Lemma 3.6 and Proposition 3.8 are proved for every configuration, with
  the Sobolev inequality, the moment bounds and, for the Meyers estimate, the clusters of the
  triadic cubes as hypotheses; the probability bounds of Lemma 3.6 and Proposition 3.8 and the
  partition `ℛ` of AD, Definition 3.7, are not proved in this section; they are proved in
  [Section 3 and the isotropy of the homogenized matrix in every dimension](#section-3-and-the-isotropy-of-the-homogenized-matrix-in-every-dimension).

## Localization of the subadditive quantities and the homogenized matrix for d = 2

Continuing the planar steps of
[Green columns and the coarse-grained cluster for d = 2](#green-columns-and-the-coarse-grained-cluster-for-d--2),
the localization and approximate stationarity of `μ` and `ν` (AD, §4.3) and the first step of AD,
§5, the limits of their expectations and the homogenized matrix `ā`, are proved for `d = 2` and
`𝔭_c(2) < p < 1`. Here `ν(□_m, ξ)` and `μ(□_m, q)` are the planar subadditive quantities on the
cluster of the triadic square `□_m` of scale `m` centred at the origin, and the expectations are
taken on the event that the partition exists and resolves `□_m`.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.exists_measure_planarCappedDiscrepancy_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarNuStationarity.lean) | AD Proposition 4.9 for `d = 2`: the planar partition differs somewhere in a triadic square `V` of scale `n` from the partition capped at scale `n` with probability at most `C exp(−c 3ⁿ)`. |
| [`Rigidity.Percolation.exists_planarNuLoc_localization`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarNuLocal.lean) | AD Proposition 4.10 for `ν`, `d = 2`: a version of `ν(V, ξ)` measurable with respect to the edges near `V` differs from it on an event of probability at most `C exp(−c 3ⁿ)`, and the expectations differ by at most `C\|ξ\|₁² exp(−c 3ⁿ)`. |
| [`Rigidity.Percolation.exists_planarMuLoc_localization`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarMuLocal.lean) | AD Proposition 4.10 for `μ`, `d = 2`, with the error `C\|q\|₁² exp(−c 3ⁿ)` in expectation. |
| [`Rigidity.Percolation.map_planarNuStat_shift`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarLocalStationary.lean) | AD (4.40) for `d = 2`: the law of the local version of `ν(z + □_n, ξ)` does not depend on `z ∈ 3ⁿℤ²`. |
| [`Rigidity.Percolation.map_planarMuStat_shift`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarLocalStationary.lean) | the same for `μ`. |
| [`Rigidity.Percolation.exists_tendsto_planarNuMean`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarNuConvergence.lean) | `E[ν(□_m, ξ)]` converges as `m → ∞`, to a limit between `c\|ξ\|²` and `(9/4)\|ξ\|₁²`. |
| [`Rigidity.Percolation.exists_tendsto_planarMuMean`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarMuConvergence.lean) | `E[−μ(□_m, q)]` converges as `m → ∞`, to a limit between `0` and `C\|q\|₁²`. |
| [`Rigidity.Percolation.planarNuLimit_eq_planarAhom`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarNuQuadratic.lean) | AD Definition 5.1 for `d = 2`: the limit is the quadratic form `(1/2) ξ · ā ξ` of a matrix `ā`. |
| [`Rigidity.Percolation.exists_planarAhom_bounds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarNuQuadratic.lean) | AD (5.1) for `d = 2`: `c\|ξ\|² ≤ (1/2) ξ · ā ξ ≤ (9/4)\|ξ\|₁²` with `c > 0`. |
| [`Rigidity.Percolation.exists_planarMuLimit_two_sided`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarMuLimitBounds.lean) | `\|q\|²/18 ≤ lim_m E[−μ(□_m, q)] ≤ C\|q\|₁²`. |
| [`Rigidity.Percolation.sum_mul_le_planarMuLimit_add_planarNuLimit`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarDuality.lean) | for all slopes `q` and `ξ`, `q · ξ ≤ lim E[−μ(□_m, q)] + lim E[ν(□_m, ξ)]`. |

The eleven theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules
are in [`PercolationClusterHomogenization/Proofs/Percolation/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Percolation/), from `PlanarLocality.lean`
and `TriadicCappedPartition.lean` to `PlanarDuality.lean`.

1. **Capped partition and translations** (`TriadicCappedPartition.lean`, `PlanarTranslation.lean`,
   `PlanarAnchorTranslation.lean`, `PlanarClusterTransport.lean`, `PlanarMuTransport.lean`). Declaring
   every cube of scale above `n` good caps the partition at scale `n`; the capped partition and the
   anchors move with the translations of `3ⁿℤ²`, and `μ` and `ν` are invariant under the relabellings
   of the cluster that respect the open edges.
2. **Localization** (`PlanarNuStationarity.lean`, `PlanarNuMeasurable.lean`, `PlanarMuMeasurable.lean`,
   `PlanarLocality.lean`, `PlanarNuLocal.lean`, `PlanarMuLocal.lean`). The partition and its capped
   version differ in `V` with probability at most `C exp(−c 3ⁿ)` (AD, Proposition 4.9). The local
   versions of `ν` and `μ` take the value of `ν` and `μ` at any configuration with the same capped
   cubes, anchors and open edges in the square of side `14 · 3ⁿ` around `V`; they are measurable with
   respect to these edges, hence independent for distant squares (AD, Proposition 4.10).
3. **Stationarity and limits** (`PlanarLocalStationary.lean`, `PlanarLocalLimits.lean`,
   `PlanarNuConvergence.lean`, `PlanarMuConvergence.lean`, `PlanarLimitCubes.lean`). The subadditivity
   of `ν` and `μ` over the resolved subsquares and the approximate stationarity of their expectations
   make `E[ν(□_m, ξ)]` and `E[−μ(□_m, q)]` approximately monotone, with errors
   `C\|ξ\|₁²(3^{−n/2} + exp(−c 3ⁿ))`, so they converge, along every sequence of squares of scale `m`.
4. **The homogenized matrix** (`PlanarNuQuadratic.lean`, `PlanarMuQuadratic.lean`,
   `PlanarMuLimitBounds.lean`, `PlanarDuality.lean`). `ν` and `μ` are quadratic in the slope, so the
   limits are quadratic forms; the limit of `E[ν]` defines `ā` (AD, Definition 5.1), with the bounds
   (5.1), and `q · ξ ≤ ν(U, ξ) − μ(U, q)` passes to the limits.

Departures from Armstrong and Dario:

- **Anchors.** The anchor of a planar partition square is chosen through its displacement from the
  centre of the square, so that anchors move with translations.
- **Localization.** AD define local quantities through the local partitions `𝒫_loc` of
  Proposition 2.1 and use their exact stationarity (4.40); the Lean proof caps the partition at the
  scale of `V`, proves the approximate stationarity of `E[ν]` and `E[−μ]` on resolved squares with
  error `C\|q\|₁² exp(−c 3ⁿ)`, and defines the local versions through the capped partition on the
  square of side `14 · 3ⁿ` around `V`; the stationary versions are taken through the origin square,
  where their laws are exactly invariant.
- **Section 5.** This section proves the convergence of the expectations, Definition 5.1 and (5.1),
  and the inequality `q · ξ ≤ lim E[−μ] + lim E[ν]`; the identification
  `lim E[−μ(□_m, q)] = (1/2) q · ā⁻¹ q` and the further parts of AD, §5, are in
  [Energy defects, finite-volume matrices and the identification of the limit for d = 2](#energy-defects-finite-volume-matrices-and-the-identification-of-the-limit-for-d--2).

## Energy defects, finite-volume matrices and the identification of the limit for d = 2

Continuing [the previous section](#localization-of-the-subadditive-quantities-and-the-homogenized-matrix-for-d--2),
the parts of AD, §5, that do not use the Meyers estimate on the cluster are proved for `d = 2` and
`𝔭_c(2) < p < 1`. Write `ε_k = 3^{−k/2} + exp(−c 3ᵏ)`. The quantity `τ_k` of AD, §5, is the sum of
the positive parts of the increments of `E[μ(□_k, ·)]` at the unit vectors and of `E[ν(□_k, ·)]` at
`ā⁻¹` applied to them. The matrix `ā_{□_n}⁻¹` of AD, Definition 5.6, is the matrix of the quadratic
form `2 E[−μ(□_n, ·)]`. The expectation of `ω(□_n, q)` is
`E[ν(□_n, ā⁻¹q)] + E[−μ(□_n, q)] − q · ā⁻¹q`, and `D_n` is the quantity of the proof of AD,
Lemma 5.10. The numbering is that of the arXiv v2 source: Definition 5.6 precedes the weak
convergence Lemma 5.7, the flatness Lemma 5.8, the decay of `ω` Lemma 5.9 and its iteration
Lemma 5.10.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.sum_clusterForm_sub_add_sum_planarMu_subcubes_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarSecondVariation.lean) | AD Lemma 4.2 and (5.11) for `μ`, `d = 2`: for the minimizer on a resolved cube and the minimizers on its subcubes of scale `n`, the energy of the differences plus the sum of `μ` over the subcubes is at most `μ` of the large cube. |
| [`Rigidity.Percolation.sum_clusterForm_sub_add_planarNu_le_sum_subcubes`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarSecondVariation.lean) | the same for `ν`, for any solution of the first variation equation on the large cube. |
| [`Rigidity.Percolation.exists_lintegral_planarMuDefect_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarMuEnergyDefect.lean) | AD Lemma 5.4, display (5.10), for `μ`: the expected energy of the differences between the restricted minimizer and the minimizers on the subcubes of scale `n` is at most the volume times the decrease of `E[−μ]` between the two scales, up to `C\|q\|₁² ε_n`. |
| [`Rigidity.Percolation.exists_lintegral_planarNuDefect_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarNuEnergyDefect.lean) | the same for `ν`, with maximizers. |
| [`Rigidity.Percolation.exists_planarMuDefect_le_planarMuTau`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarMuIncrements.lean) | AD (5.9) and (5.10) for `μ`: for `n ≤ m`, the expected energy of the differences, divided by the volume, is at most `2\|q\|² ∑_{n ≤ k < m} τ_k^μ` plus `C\|q\|₁² (∑_{n ≤ k < m} ε_k + ε_n)`. |
| [`Rigidity.Percolation.exists_planarNuDefect_le_planarNuTau`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarNuDefectTau.lean) | the same for `ν` at `ā⁻¹ q`, with `τ^ν`. |
| [`Rigidity.Percolation.summable_planarTau`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarTauSummable.lean) | `τ_k` is summable. |
| [`Rigidity.Percolation.exists_planarMuDefect_le_tendsto`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarTauSummable.lean), [`exists_planarNuDefect_le_tendsto`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarNuDefectTau.lean) | AD Lemma 5.4, qualitative form: the expected energy of the differences divided by the volume is at most `(\|q\|² + \|q\|₁²) R_n` with `R_n → 0`, uniformly in `m ≥ n`. |
| [`Rigidity.Percolation.planarMuLimit_eq_iff_planarOmegaLimit_eq_zero`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaLimit.lean), [`forall_planarOmegaLimit_eq_zero_iff`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaMatrix.lean) | AD Proposition 5.2: the limit of `E[ω(□_n, q)]` exists and is nonnegative, and `lim E[−μ(□_n, q)] = (1/2) q · ā⁻¹ q` for all `q` if and only if the limit of `E[ω]` vanishes, if and only if the finite-volume matrices converge to `ā⁻¹`. |
| [`Rigidity.Percolation.integral_coarsePairing_planarMuMinimizer`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarFiniteVolumeMatrix.lean) | AD (5.23), the centering in Lemma 5.7: the expected spatial average of the coarsened gradient of the minimizer of `μ(□_n, q)` against `r` is `r · ā_{□_n}⁻¹ q`. |
| [`Rigidity.Percolation.tendsto_planarAhomInvFinite`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarFiniteVolumeMatrix.lean) | the matrices `ā_{□_n}⁻¹` converge entrywise to twice the matrix of the limit of `E[−μ]`. |
| [`Rigidity.Percolation.exists_planarAhomInvFinite_bounds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarFiniteVolumeBounds.lean), [`exists_abs_planarAhomInvFinite_sub_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarFiniteVolumeClose.lean) | AD (5.22) and (5.24): the matrices are uniformly elliptic from some scale on, and two of them differ by at most `2 ∑ τ_k` plus a vanishing error. |
| [`Rigidity.Percolation.tsum_sum_grad_mul_solenoidalField`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarSolenoidalPairing.lean), [`solenoidalField_eq`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarSolenoidalField.lean), [`abs_solenoidalField_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarSolenoidalField.lean) | AD Lemma 5.7, Step 1, and (5.28) with right side zero, `d = 2`: a finitely supported, exactly divergence free field, bounded by `10 \|e\|₁`, equal to `e` near `□_n`, is orthogonal to every gradient. |
| [`Rigidity.Percolation.exists_abs_planarNu_sub_planarMu_sub_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarQuadraticResponse.lean) | first display of the proof of AD Lemma 5.9, per cube: `ν(U, p) − μ(U, q) − q · p` differs from the energy of the difference between the maximizer and the minimizer, divided by twice the volume, by at most `\|q · p\|/L` plus the boundary error. |
| [`Rigidity.Percolation.exists_planarOmegaD_succ_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaStepOne.lean), [`exists_neg_le_planarOmegaD`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaDBounds.lean) | AD Lemma 5.10, Step 1 and the lower bound of `D_n`: from some scale on, `D_{n+1} ≤ D_n − c τ_n + C ε_n` and `D_n ≥ −C 3^{−n/2}`. |
| [`Rigidity.Percolation.exists_le_mul_pow_of_omega_iteration`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaIteration.lean), [`exists_le_mul_pow_of_omega_iteration_of_ge`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaIteration.lean) | AD Lemma 5.10, Steps 1 to 3, for real sequences, also when the hypotheses hold only from a starting scale on. |
| [`Rigidity.Percolation.exists_planarOmegaD_le_pow_of_decay`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaDecayIteration.lean), [`exists_planarTau_le_pow_of_decay`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaDecayIteration.lean), [`exists_abs_planarAhomInvLimit_sub_le_of_decay`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarFiniteVolumeRate.lean) | AD Lemma 5.10 with the bound of Lemma 5.9 as an explicit hypothesis `h59`: `D_n`, `τ_n` and the distance from `ā_{□_n}⁻¹` to its limit decay geometrically. |
| [`Rigidity.Percolation.planarMuLimit_eq_of_decay`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarIdentification.lean) | AD Proposition 5.2, qualitative part, with the bound of Lemma 5.9, `D_n ≤ C (σⁿ + ∑_{l ≤ n} ρ^{n−l} τ_l)` from some scale on with `σ, ρ < 1`, as an explicit hypothesis: `lim E[−μ(□_n, q)] = (1/2) q · ā⁻¹ q` for every `q`. |

The theorems of the table and their supporting results (the limit matrix is invertible, the matrices
`ā_{□_n}` converge to its inverse, `D_n` converges, the limit matrix is below `ā⁻¹`) depend on
exactly `propext`, `Classical.choice` and `Quot.sound`; thirty-five of them have axiom reports in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean). The modules are in
[`PercolationClusterHomogenization/Proofs/Percolation/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Percolation/), from `PlanarSecondVariation.lean`
and `PlanarMuEnergyDefect.lean` to `PlanarIdentification.lean`.

1. **Energy defects** (`PlanarSecondVariation.lean`, `PlanarMuEnergyDefect.lean`,
   `PlanarNuEnergyDefect.lean`). The second variation identities for `μ` and `ν` on a resolved
   cube and their subadditive form, summed over the subcubes of scale `n`, bound the energy of the
   differences between the restricted optimizer and the optimizers of the subcubes by the decrease
   of the expectation between the two scales.
2. **The quantity `τ`** (`PlanarMuIncrements.lean`, `PlanarNuIncrements.lean`,
   `PlanarNuDefectTau.lean`, `PlanarTauSummable.lean`). The increments of the expectations are
   almost nonnegative quadratic forms, controlled by their values at the unit vectors, so that the
   energy defects are controlled by the sums of `τ_k`, which are summable.
3. **Finite-volume matrices** (`PlanarFiniteVolumeMatrix.lean`, `PlanarFiniteVolumeInverse.lean`,
   `PlanarFiniteVolumeBounds.lean`, `PlanarFiniteVolumeClose.lean`,
   `PlanarFiniteVolumeInverseLimit.lean`, `PlanarCoarseGradientMean.lean`). The matrices
   `ā_{□_n}⁻¹` and their inverses, their ellipticity, their closeness at two scales and their
   limit.
4. **Solenoidal field** (`PlanarSolenoidalField.lean`, `PlanarSolenoidalPairing.lean`). The
   discrete curl of a cut off affine stream function on the plaquettes.
5. **The quantity `ω` and the identification** (`PlanarOmegaLimit.lean`, `PlanarOmegaMatrix.lean`,
   `PlanarOmegaDLimit.lean`, `PlanarQuadraticTrace.lean`, `PlanarOmegaStepOne.lean`,
   `PlanarOmegaDBounds.lean`, `PlanarOmegaIteration.lean`, `PlanarOmegaDecayIteration.lean`,
   `PlanarFiniteVolumeRate.lean`, `PlanarIdentification.lean`, `PlanarQuadraticResponse.lean`). The
   limit of `E[ω]` and its vanishing, the decrease of `D_n` along `τ_n`, the iteration of AD,
   Lemma 5.10, and the identification of the limit of `E[−μ]` from the bound of Lemma 5.9.

Departures from Armstrong and Dario:

- **Hypothesis of the identification.** In this section the bound of Lemma 5.9 for `D_n` is not proved
  (it is proved from Lemmas 5.5 and 5.7 in
  [Lemmas 5.8 and 5.9 and the qualitative part of Proposition 5.2 for d = 2](#lemmas-58-and-59-and-the-qualitative-part-of-proposition-52-for-d--2)). Its proof
  uses Lemmas 5.5 to 5.8, and Lemma 5.5, with Steps 2 and 3 of Lemma 5.7, needs the Meyers estimate
  of AD, Proposition 3.8, on the planar cluster, which is proved in a deterministic form with its
  good events as hypotheses in
  [Clusters of integer cubes, the Meyers estimate and the coarse energy bounds toward Lemma 5.5](#clusters-of-integer-cubes-the-meyers-estimate-and-the-coarse-energy-bounds-toward-lemma-55).
  The theorem `planarMuLimit_eq_of_decay` and the geometric rates derived from Lemma 5.10 therefore
  take the bound as the explicit hypothesis `h59`; without it, the identification is reduced to the
  vanishing of the limit of `E[ω]`. The rate of Proposition 5.2 in expectation, Lemma 5.10, Lemma 5.11 Step 2 and a deterministic form of
  Lemma 5.3 are proved for `p > 𝔭_c(2)` in [The rate of Proposition 5.2 and Lemmas 5.3, 5.10 and 5.11 (Step 2) in dimension two](#the-rate-of-proposition-52-and-lemmas-53-510-and-511-step-2-in-dimension-two); Proposition 5.2 in the `O_s` form, Lemma 5.11 and
  Proposition 5.13 are proved in [Propositions 5.2 and 5.13, Lemma 5.11 and the minimal scales in dimension two](#propositions-52-and-513-lemma-511-and-the-minimal-scales-in-dimension-two). Lemmas 5.5 and 5.7 in `d = 2` are proved in [Lemmas 5.5 and 5.7 in dimension two](#lemmas-55-and-57-in-dimension-two).
- **Lemma 5.4.** The estimate is proved for every `n ≤ m` with the error
  `C\|q\|₁² (∑_k ε_k + ε_n)`, `ε_k = 3^{−k/2} + exp(−c 3ᵏ)`, where AD take `n ∈ [m/2, m)` and the
  error `3^{−n/4}`; the quantity `τ^ν` is built at `ā⁻¹ e_i`, as in AD.
- **Lemma 5.7.** The field of Step 1 is the discrete curl of a cut off affine stream function, so
  it is exactly divergence free and supported in the square of half side `5/4 · 3ⁿ + 1`, whereas AD
  discretize a smooth field that is almost divergence free. Steps 2 and 3 are not proved in this
  section; see [Lemmas 5.5 and 5.7 in dimension two](#lemmas-55-and-57-in-dimension-two).
- **Lemma 5.10, Step 2.** The display for `D̃_n − D̃_{n+1}` has `D_k − D_{k−1}` where `D_k − D_{k+1}`
  is meant, and the bound of Lemma 5.9 is resummed over `l ∈ [N₀, n]` where `l ≤ k` is meant, the
  terms with `l < N₀` being `O(3^{N₀−k})`. The Lean proof uses the exact recursions
  `D̃_{n+1} = μ D̃_n + D_{n+1}` for the weighted averages instead.

## Clusters of integer cubes, the Meyers estimate and the coarse energy bounds toward Lemma 5.5

Armstrong and Dario use the reverse Hölder inequality of Lemma 3.6 on every triadic cube `□'`
above a cell of the Gehring partition, with the Sobolev inequality of Proposition 3.4 on the cluster
of the triple `3□'`, which is an integer cube of side `3^{k+1}` but in general not a triadic cube.
Here Lemmas 3.2 and 3.3 and Proposition 3.4 (with `s = 2` and `∑_{C(B)} w = 0`) are proved on the
cluster `C(B)` of every integer cube `B` resolved by the partition, in every dimension `d ≥ 2`, and
the deterministic part of the Meyers estimate (AD, Proposition 3.8) and of Step 3 of the proof of
Lemma 5.5 follow in `d = 2`. The results are conditional: each states, as hypotheses, exactly the
events and moment bounds listed in its row, which are not proved here.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Cluster.reverse_holder_partition_cube_of_moment`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/ReverseHolderMoment.lean), [`reverse_holder_partition_of_moment`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/ReverseHolderMoment.lean) | AD Lemma 3.6, deterministic part, every `d ≥ 2`, with the Sobolev hypothesis proved: for a resolved cube `□_{m+1}` with `∑_{z ∈ C_*(□_{m+1})} (3^{ρ(z)})^{2ds} ≤ C_G \|□_{m+1}\|` and `u` harmonic on `C_*(□_{m+1})`, `3^{−md} ∑_{C_*(□_{m+1}) ∩ □_m} \|∇u 1_{𝐚≠0}\|² ≤ C (\|□_{m+1}\|⁻¹ ∑_{C_*(□_{m+1})} \|∇u 1_{𝐚≠0}\|^{t 2_*})^{2/(t 2_*)}`, as in `reverse_holder_partition_cube`. |
| [`Rigidity.Proofs.Cluster.planar_reverse_holder_cube_of_moment`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/ReverseHolderPlanar.lean) | the same for the planar partition, with the weight `((3^ρ)² + 3^{ρ'})^{1/4}` and the moment bound `∑ ((3^ρ)² + 3^{ρ'})^s ≤ C_G 3^{2(m+1)}`. |
| [`Rigidity.Percolation.exists_planarBox_sum_sq_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarBoxSobolev.lean), [`exists_clusterSobolevTwo_box`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PartitionBoxSobolev.lean) | AD Proposition 3.4 with `s = 2`, with Lemmas 3.2 and 3.3 proved on the cluster of an integer square (`d = 2`) or integer cube (every `d ≥ 2`) `B` resolved by the partition, for `w` of mean zero on the cluster: `∑_{C(B)} w² ≤ K (∑_{z ∈ C(B)} w_ρ(z) \|∇w 1_{𝐚≠0}\|(z))²` with the weight `w_ρ` built from the reach scales of `B`, which are bounded by the reach of the partition (`three_pow_reachScale_le_planarReach_box`, `three_pow_reachScale_le_partitionReach_box`). |
| [`Rigidity.Proofs.Cluster.reverse_holder_clusterEnergy_local`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/MeyersPlanarBox.lean), [`meyers_cluster_of_local`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/MeyersPlanarBox.lean) | the reverse Hölder inequality for functions harmonic near the cube, and `meyers_cluster` with a weight chosen for each cube `□'`. |
| [`Rigidity.Proofs.Cluster.planar_meyers`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/MeyersPlanarBox.lean), [`planar_meyers_clusterHarmonic`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarMeyersHarmonic.lean) | AD Proposition 3.8, deterministic part, `d = 2`, with the Sobolev inequality on the clusters of the triples proved, for `u` harmonic on the cluster of a triadic cube `V ⊇ 3□` (for the extension by zero of a harmonic function of a smaller cube in the second form). Hypotheses: the planar partition event; a Gehring partition of `3□` into cells of comparable neighbouring sizes with `∑_{x ∈ □} (3^{s(x)})^t ≤ K \|□\|`; for every triadic `□' = cube k y` above a cell with `3□' ⊆ 3□`, the partition cubes of the vertices of `3□'` have scale at most `k` and `∑_{z ∈ 3□'} planarReach(z)^8 ≤ C_G \|3□'\|`. |
| [`Rigidity.Proofs.Cluster.partition_meyers`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/MeyersPartitionBox.lean) | the same in every dimension `d ≥ 2` on `C_*(V) ∩ 3□`, `V` resolved, with `∑_{z ∈ 3□'} partitionReach(z)^{2d(d+2)} ≤ C_G \|3□'\|` and the partition scales below `k`. |
| [`Rigidity.Proofs.Cluster.sum_mul_le_of_meyers_cells`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarCoarseMeyers.lean), [`planarBox_coarse_energy_le_of_meyers`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarCoarseMeyers.lean) | AD display (5.16), deterministic, `d = 2`: with the Meyers estimate on cells `□'` covering the cluster of a resolved square `B ⊆ V`, triples of overlap at most `N`, and cell averages of a weight `W ≥ 3^{ρ'}` with `(avg_{□'} W^{3q})^{1/q} ≤ A`, `∑_B \|∇[w]_𝒫\|² ≤ C² A C_M^{1/p} N ∑_V \|∇w 1_{𝐚≠0}\|²`. |
| [`Rigidity.Percolation.edgePairing_sq_le_of_subset`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarEdgePairing.lean), [`coarsePairing_eq_edgePairing`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarEdgePairing.lean) | AD Lemma 5.5, Step 2 (removal of the boundary layer): `⟨∇f, g⟩_V² ≤ 8 G² \|B\| E_B + 16 G² \|V ∖ B\| E_V` for `\|g\| ≤ G`. |
| [`Rigidity.Proofs.Cluster.edgePairing_clusterExtend_sq_le_clusterForm`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarCoarseEnergy.lean), [`edgePairing_innerCells_sq_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarInnerCells.lean) | AD Lemma 5.5, Steps 2 and 3 on one subcube, with the Hölder inequality inside the cells of scale `j` of the inner square: `⟨∇[w]_𝒫, g⟩_V² ≤ Λ B(w, w)`. Hypotheses: the partition scales on `V` are at most `j`, the Meyers estimate for `w` on the cells, the bound `A` on the cell averages of the weight, and `W ≥ 3 planarReach` on the cluster. |
| [`Rigidity.Proofs.Cluster.sum_edgePairing_sq_le_planarMuDefect`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRestrictDefect.lean) | AD Lemma 5.5, deterministic part, summed over the resolved subcubes of scale `n`: `∑_V ⟨∇[w_V]_𝒫, g⟩_V² ≤ 2 Λ D_n(U, q)`, with the hypotheses of `edgePairing_innerCells_sq_le` on each subcube. |
| [`Rigidity.Percolation.exists_measure_partitionScale_gt_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarPartitionScaleTail.lean) | for every `m`, the probability that some vertex of a finite set `S` has a planar partition cube of scale larger than `j` is at most `C \|S\| 3^{−(j+1)(m+1)}`. |
| [`Rigidity.Proofs.Cluster.ofReal_sum_gradNormIn_coarse_planarMuMinimizer_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarCoarseMinimizer.lean), [`exists_lintegral_coarse_minimizer_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarCoarseEnergyMoments.lean), [`exists_lintegral_coarse_minimizer_sq_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarCoarseEnergySecondMoment.lean) | AD (4.24), `d = 2`: for the minimizer `u_V` of `μ(V, q)` on a resolved triadic cube, `∑_V \|∇[u_V]_𝒫\|² ≤ C \|q\|₁² (3 max_V R)³ ∑_V R⁴` with `R = planarReach`, `E[∑_V \|∇[u_V]_𝒫\|²] ≤ C_a \|q\|₁² \|V\|^{1+1/a}` for `a ≥ 2`, and the second moment `≤ C \|q\|₁⁴ \|V\|^{2+2/a}` for `a ≥ 3`. |
| [`Rigidity.Percolation.edgePairing_sub_sum_subcubes_sq_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarSubcubePairing.lean), [`Rigidity.Proofs.Cluster.exists_lintegral_edgePairing_sub_sum_subcubes_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarHolderAway.lean) | AD Lemma 5.7, Step 2, display (5.29), `d = 2`: the pairing of a bounded field with the coarsened gradient on `U` differs from the sum over the subcubes of scale `n` by at most the number of crossing edges times the energy, and in expectation `E[(⟨∇[u_U], g⟩_U − ∑_V ⟨∇[u_U], g⟩_V)²] ≤ C G² \|q\|₁² 3^{−n} \|U\|² \|U\|^{1/a}`. |

The theorems of the table and their supporting results depend only on axioms among `propext`, `Classical.choice`
and `Quot.sound`; sixty-five of them (sixty-one theorems and four definitions) have axiom reports in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean). The modules are in
[`PercolationClusterHomogenization/Proofs/Cluster/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Cluster/), from `ReverseHolderMoment.lean` to
`PlanarRestrictDefect.lean`.

1. **Windows and clusters of integer cubes** (`PlanarBoxWindows.lean`, `PlanarBoxCluster.lean`,
   `PartitionBoxPaths.lean`, `PartitionBoxCluster.lean`). A vertex joined to the anchor of its
   partition cube by a path that leaves the integer cube only far from the vertex is joined to it
   inside the window of the cube; the cluster `C(B)` of an integer cube resolved by the partition is
   the set of vertices of `B` joined inside `B` to the anchor of their partition cube, and its
   coarse-graining data are built from the windows and pair windows inside `B`.
2. **Sobolev inequality and Meyers estimate** (`PlanarBoxSobolev.lean`, `PartitionBoxSobolev.lean`,
   `ReverseHolder*.lean`, `Meyers*.lean`, `PlanarMeyersHarmonic.lean`). Lemmas 3.2 and 3.3 and the
   lattice Sobolev inequality on integer cubes give Proposition 3.4 on `C(B)`, and with it the
   reverse Hölder inequality at every cube used by the Gehring argument.
3. **Coarse energy of Lemma 5.5** (`PlanarCoarseMeyers.lean`, `PlanarEdgePairing.lean`,
   `PlanarInnerSquare.lean`, `PlanarInnerCells.lean`, `PlanarRestrictQuad.lean`,
   `PlanarRestrictCoarse.lean`, `PlanarCoarseEnergy.lean`, `PlanarRestrictDefect.lean`). The Meyers
   estimate on the cells of the inner square, Lemma 3.3 and the Hölder inequality bound the energy
   of the coarsened differences of the minimizers, and the pairing with a bounded field, by the
   energy defect of Lemma 5.4.
4. **Moments** (`PlanarCoarseMinimizer.lean`, `PlanarCoarseEnergyMoments.lean`,
   `PlanarCoarseEnergySecondMoment.lean`, `PlanarPartitionScaleTail.lean`,
   `PlanarSubcubePairing.lean`, `PlanarHolderAway.lean`). The reach of the planar partition has all
   moments, which bounds the coarsened energy of the minimizers in expectation (AD (4.24)) and the
   probability that a partition cube is larger than a given scale.

Departures from Armstrong and Dario:

- **Clusters of the triples.** AD apply Proposition 3.4 on `C_max(3□')`; the Lean proof uses the
  cluster `C(3□')` of the integer cube, the vertices joined to the anchor of their partition cube
  inside it. It lies in the crossing cluster of every resolved triadic cube containing `3□'`, is
  closed under open edges inside `3□'`, and contains the vertices of the crossing cluster in `□'`.
  The weight of the Sobolev inequality is the reach of the partition, not the size of the partition
  cube.
- **Reverse Hölder inequality at non-central cubes.** AD prove Lemma 3.6 for central subcubes of a
  triadic cube and obtain the other cubes of the proof of Proposition 3.8 by stationarity. The Lean
  proof of the Meyers estimate derives the inequality at every `□'` from the Caccioppoli
  inequality and the Sobolev inequality on `C(3□')`, and takes the good event of the partition
  `ℛ` at `□'` as a hypothesis in place of the stationarity.
- **Departure from AD18, Lemma 5.5 Step 3: Hölder inside the cells (AD, arXiv v2 numbering, display after "apply the proposition in each
  `Q'`").** The second inequality of the display,
  `(\|□_n\|⁻¹ ∑ \|Q'\|^{1−s/2} a_{Q'}^{s/2})^{2/s} ≤ \|□_n\|⁻¹ ∑ \|Q'\|^{2/s−1} a_{Q'}`, is not true
  as written: by concavity the right side carries `\|□_n\|^{−2/s}`, and for one charged unit cell
  the two sides differ by the factor `\|□_n\|^{1−2/s}`; the global Hölder inequality over the cells
  loses the power `(#cells)^{(s−2)/s}` (it is `sum_rpow_le_of_meyers_cells`). The repair is the
  Hölder inequality inside each cell with the cell average of the weight (`sum_mul_le_of_meyers_cells`),
  the cells being the triadic squares of scale `⌈n/2⌉` not touching the boundary of the subcube, on
  the event that the Meyers estimate holds on all cubes of scale at least `⌈n/2⌉` and the cell
  averages of the weight are bounded. The weight is the pair reach of the partition, bounded by
  three times the reach of the planar partition, in place of the sizes of the partition cubes.
- **Display (4.24) and the moments.** The bounds are proved with the reach of the planar partition
  and the factor `\|V\|^{1/a}` for every `a ≥ 2` in place of `3^{δ n}`, `δ > 0`; the second moment
  is added for the estimates off the good events.
- **Conditional statements.** The Meyers estimate (`planar_meyers`, `partition_meyers`), the
  per-subcube bound `edgePairing_innerCells_sq_le` and its sum over the subcubes
  `sum_edgePairing_sq_le_planarMuDefect` are deterministic: the good events they assume (the
  Gehring partition and the bounds on the reach over the triples, the partition scales and the
  Meyers estimate on the cells of the inner squares, the bounds on the cell averages of the weight)
  are not shown to hold with high probability in this section. Consequently Lemma 5.5 itself and
  Lemma 5.7 Step 3 are not proved here; they are proved for `p > 𝔭_c(2)` in [Lemmas 5.5 and 5.7 in dimension two](#lemmas-55-and-57-in-dimension-two). Lemmas 5.8 and 5.9 are proved from Lemmas 5.5 and 5.7 in
  [Lemmas 5.8 and 5.9 and the qualitative part of Proposition 5.2 for d = 2](#lemmas-58-and-59-and-the-qualitative-part-of-proposition-52-for-d--2).

## The subadditive quantities on the clusters of triadic cubes of Z^d

Section 4 of Armstrong and Dario defines `μ(U, q)` and `ν(U, p)` on the cluster `C_*(U)` of a
resolved triadic cube `U` of `ℤ^d`, and proves their basic properties. For `d = 2` this is in
[Localization of the subadditive quantities and the homogenized matrix for d = 2](#localization-of-the-subadditive-quantities-and-the-homogenized-matrix-for-d--2)
and the sections after it. Here the same results are proved in every dimension `d ≥ 2`, in
[`PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/), with the names
`cubeMu`, `cubeNu`, `cubeForm`, `cubeHarmonic` in place of the planar `planarMu`, `clusterForm`, and
so on. On the partition event and for a resolved cube, `cl_𝒫(U) = U` and `C_*(U)` is the crossing
cluster of `U`; the space `A_*(U)` of the paper is `cubeHarmonic`, the functions on `C_*(U)` harmonic
at the vertices of `C_*(U)` in the lattice interior of `U`. AD numbering below is that of the arXiv v2
source (Definition 4.1, Lemmas 4.2 to 4.5, Corollary 4.6, Lemmas 4.7 and 4.8, Definition 5.1).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.cubeMu`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeEnergy.lean), [`cubeNu`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeEnergy.lean), [`exists_cubeMu_minimizer`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeEnergy.lean), [`exists_cubeNu_maximizer`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeEnergy.lean) | AD Definition 4.1 and Lemma 4.2: `μ(U, q) = inf_{A_*(U)} (B(u, u)/2 − ℓ_q(u))/\|U\|` and `ν(U, p) = sup_{A_*(U)} (F_p(v) − B(v, v)/2)/\|U\|` are attained, at solutions of the first variation equations `B(w, u) = ℓ_q(w)` and `B(w, v) = F_p(w)` for `w ∈ A_*(U)`; here `B` is the Dirichlet form on the open edges of `C_*(U)`, `ℓ_q` the coarse pairing over the lattice edges inside `U`, and `F_p` the flux pairing. |
| [`cubeMu_mul_latticeVolume_add_cubeForm_sub`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeFluxPairing_sub_add_cubeForm_sub`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeMu_mul_latticeVolume_eq`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeNu_mul_latticeVolume_eq`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeNu_sub_cubeMu_eq`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeMu_smul_add_smul`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeNu_smul_add_smul`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeVariations.lean) | AD Lemma 4.2, (4.4), (4.6), (4.7) and (4.8): the second variations, the values `\|U\| μ(U, q) = −B(u, u)/2` and `\|U\| ν(U, p) = B(v, v)/2` at the optimizers, the comparison identity of `ν` and `μ`, and the quadratic dependence of `μ` and `ν` on `q` and `p`. |
| [`cubeMu_nonpos`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeEnergyBounds.lean), [`cubeNu_nonneg`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeEnergyBounds.lean), [`cubeNu_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeEnergyBounds.lean), [`neg_cubeMu_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeMuUpperBound.lean), [`exists_lintegral_neg_cubeMu_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeMuMoment.lean) | `μ(U, q) ≤ 0 ≤ ν(U, p) ≤ (3^d/4) \|p\|₁²` ((4.13)); the bound of `−μ` by the partition sizes, `−μ(U, q) ≤ d C₃² \|q\|₁² \|U\|⁻¹ ∑_{z ∈ C_*(U)} size(□_𝒫(z))^{2d−2}` ((4.12)), through AD Lemma 3.3 with `s = 1`; and `E[−μ(U, q); partition event, U resolved] ≤ C \|q\|₁²` ((4.16), in expectation). |
| [`exists_cubeNu_maximizer_affine`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuDirichlet.lean), [`exists_cubeHarmonic_eq_on_boundary`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuDirichlet.lean), [`cubeNu_le_of_affine_boundary`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuDirichlet.lean), [`exists_cubeNu_eq_of_affine_boundary`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuDirichlet.lean) | AD Lemma 4.3, (4.1) and (4.9): the functions vanishing outside the lattice interior of `U` are orthogonal to `A_*(U)`, the Dirichlet problem on `C_*(U)` with any boundary values is solvable, the maximizer of `ν(U, p)` is affine of slope `p` at the boundary vertices of `C_*(U)` up to a constant, and `ν(U, p) \|U\|` is the least half energy of a function with such boundary values. |
| [`cubeCoarsePairing_eq_faces`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeStokes.lean), [`abs_cubeCoarsePairing_sub_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNablaAffine.lean), [`cubeBoundaryError_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeBoundaryErrorBound.lean), [`cubeBoundaryWeight_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeBoundaryWeightBound.lean), [`exists_integral_sum_faces_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeSizeMoments.lean), [`exists_integral_sum_margin_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeSizeMoments.lean) | AD Lemma 4.5, (4.27), in every dimension: by the discrete Stokes formula the coarse pairing is a sum of coarsened values over the faces of `U`; for the maximizer `v` of `ν(U, p)`, `\|ℓ_q(v) − (q · p) L^{d−1}(L − 1)\| ≤ \|q\|₁ E_p(v)`, the boundary error `E_p(v)` being a weighted variation of `v` over the partition cubes at the faces, bounded by the Hölder and Young inequalities through the weight `W_∂(z) ≤ ∑_i 2 size(□_𝒫(z))^{d−1} 1{margin_i(z) < size(□_𝒫(z))}`; and the expectations of the sums of the sizes over the faces and of the margin-weighted sums are at most `C L^{d−1}`. |
| [`exists_abs_cubeNu_sub_cubeMu_sub_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeMuNuComparison.lean), [`exists_cubeMu_le_cubeNu_sub`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeMuNuComparison.lean) | AD Corollary 4.6, (4.29): `\|ν(U, p) − μ(U, q) − q · p − B(v − u, v − u)/(2\|U\|)\| ≤ \|q · p\|/L + \|q\|₁ E_p(v)/\|U\|`, with `E_p(v)` the boundary error, and `μ(U, q) ≤ ν(U, p) − q · p` up to the same errors. |
| [`exists_cubeMu_le_neg_sum_sq`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeMuLowerBound.lean), [`le_cubeNu_add_of_resolved`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLowerBound.lean), [`exists_le_integral_cubeNu`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLowerBoundMean.lean) | AD Lemma 4.7, (4.30) and (4.31): `μ(U, q) ≤ −\|q\|²/(3^d d) + t \|q\|²/L + \|q\|₁ E_{tq}(v)/\|U\|` with `t = 2/(3^d d)`; `κ \|p\|² ≤ ν(U, p)` up to explicit errors for every `κ > 0`; and, in expectation, `c \|p\|² ≤ E[ν(U, p)] + C \|p\|₁² 3^{−m/2}` for every triadic cube `U` of scale `m`. |
| [`sum_cubeMu_subcubes_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeSubadditive.lean), [`cubeNu_le_sum_subcubes`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeSubadditive.lean), [`flux_error_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuSubadditiveError.lean), [`cubeNu_mul_latticeVolume_le_sum_add`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuSubadditiveError.lean), [`sum_exp_neg_margin_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeExceptionalTail.lean) | AD Lemma 4.8, (4.32) and (4.33): for a resolved `U` and `n ≤` the scale of `U`, the sum over the vertices `x` of `U` of `μ(V(x), q)` over the resolved subcubes `V(x)` of scale `n` is at most `\|U\| μ(U, q)` plus the coarse pairing of the minimizer over the exceptional lattice edges, and `\|U\| ν(U, p)` is at most the sum over `x` of `ν(V(x), p)` plus the flux pairing of the maximizer over the open edges not inside the cluster of a resolved subcube; the second is bounded by `(3^d/4) \|p\|₁² (s G + \|U\|/s)` for every `s > 0`, `G` the number of exceptional vertices. |
| [`sum_cubeForm_sub_add_sum_cubeMu_subcubes_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeSecondVariation.lean), [`sum_cubeForm_sub_add_cubeNu_le_sum_subcubes`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeSecondVariation.lean), [`cubeNuDefect_add_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuEnergyDefect.lean), [`exists_lintegral_cubeNuDefect_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuEnergyDefect.lean) | the subadditivity of `μ` and `ν` with the energies of the differences on the left side (AD, proof of Lemma 5.4, (5.11) and its analogue for `ν`): `∑_V B_V(u\|_V − u_V)/2 + ∑_V \|V\| μ(V, q) ≤ \|U\| μ(U, q) + E_q(u)` and `∑_V B_V(v\|_V − v_V)/2 + \|U\| ν(U, p) ≤ ∑_V \|V\| ν(V, p) + F_p^{exc}(v)`; and the expectation of the energy `D^ν_n(U, p)` of the differences of the maximizers of `ν` is at most `\|U\| (E[ν(V, p)] − E[ν(U, p)] + C \|p\|₁² 3^{−n/2})`. |
| [`cubeNu_eq_of_equiv`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLocal.lean), [`measurable_cubeNu`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLocal.lean), [`integral_cubeNu_eq_of_scale_eq`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLocal.lean), [`integrable_cubeNu`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLocal.lean) | `ν(U, p)` depends only on the open edges inside `U`, is a measurable and integrable function of the configuration, and `E[ν(U, p)]` is the same for all triadic cubes of a given scale (exact stationarity). |
| [`exists_integral_cubeNu_le_of_scale_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuMonotone.lean) | AD (4.49), every `d ≥ 2`: `E[ν(U, p)] ≤ E[ν(V, p)] + C \|p\|₁² 3^{−n/2}` for triadic cubes `V`, `U` of scales `n ≤ m`. |
| [`cubeNu_eq_sum_polarization`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`exists_tendsto_cubeNuMean`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`tendsto_cubeNuLimit`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`cubeAhom`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`cubeNuLimit_eq_cubeAhom`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`cubeAhom_symm`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`cubeAhom_bounds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`exists_cubeAhom_lower_bound`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/CubeNuLowerBoundMean.lean) | AD Definition 5.1 and (5.1), every `d ≥ 2`: `ν(U, ·)` is a quadratic form given by polarization; `E[ν(□_m, ξ)]` converges as `m → ∞`; the limit is `(1/2) ξ · ā ξ` for a symmetric matrix `ā = cubeAhom`, and `c \|ξ\|² ≤ (1/2) ξ · ā ξ ≤ (3^d/4) \|ξ\|₁²`. |

The theorems of the table and their supporting results depend only on axioms among `propext`,
`Classical.choice` and `Quot.sound`; fifty-seven of them (fifty-four theorems and three definitions)
have axiom reports in [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean). The modules are the
twenty-four files of [`PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Percolation/GeneralDim/).
The quantities `cubeMu` and `cubeNu` at `d = 2` are not identified with the planar `planarMu` and
`planarNu`: the planar quantities are built on the meshed family of good squares, the general ones
on the partition into good cubes of every dimension.

1. **Cluster and variational structure** (`CubeEnergy.lean`, `CubeVariations.lean`,
   `CubeEnergyBounds.lean`, `CubeNuDirichlet.lean`). The cluster, the Dirichlet form, the two
   pairings and the quantities `μ`, `ν`, with their first and second variations and the Dirichlet
   problem with affine data.
2. **Boundary terms and comparison** (`CubeStokes.lean`, `CubeNablaAffine.lean`,
   `CubeBoundaryErrorBound.lean`, `CubeBoundaryWeightBound.lean`, `CubeSizeMoments.lean`,
   `CubeMuNuComparison.lean`, `CubeMuUpperBound.lean`, `CubeMuLowerBound.lean`,
   `CubeNuLowerBound.lean`, `CubeNuLowerBoundMean.lean`, `CubeMuMoment.lean`). The coarse pairing as
   a sum over the faces, the boundary error of the maximizer of `ν`, the bounds on `μ` and `ν`
   and their expectations.
3. **Subadditivity and the limit** (`CubeSubcubes.lean`, `CubeSubadditive.lean`,
   `CubeSecondVariation.lean`, `CubeNuSubadditiveError.lean`, `CubeExceptionalTail.lean`,
   `CubeNuMonotone.lean`, `CubeNuEnergyDefect.lean`, `CubeNuLocal.lean`, `CubeNuLimit.lean`). The
   restriction of functions to resolved subcubes, the subadditivity inequalities, the exceptional
   vertices, the stationarity and approximate monotonicity of `E[ν]`, and the homogenized matrix.

Departures from Armstrong and Dario:

- **Resolved triadic cubes.** `μ` and `ν` are defined for the triadic cubes `U` resolved by the
  partition, where `cl_𝒫(U) = U` and `\|U\| = 3^{dn}`; `A_*(U)` is the space of functions on `C_*(U)`
  harmonic at the vertices of `C_*(U)` in the lattice interior of `U` (the interior of `U` for the
  lattice edges). On a cube that is not resolved `μ` is not used; `ν` is defined on every cube, through its
  crossing cluster, and its expectation is taken without an indicator (next item).
- **Locality of `ν`.** `ν(U, p)` is defined through the crossing cluster of `U` and the open edges
  inside it, hence is a local function of the configuration with exactly stationary expectation
  (`cubeNu_eq_of_equiv`, `integral_cubeNu_eq_of_scale_eq`). This replaces AD Proposition 4.9, Proposition 4.10 and
  (4.40) for `ν`. The expectation `E[ν(U, p)]` is taken without the indicator of the event that `U`
  is resolved. The quantity `μ`, which uses the anchors of the partition, is localized, and its
  stationarity and the limit of `E[−μ]` are proved, in
  [Localization, stationarity and the limit of μ, and Definition 3.9, in every dimension](#localization-stationarity-and-the-limit-of-μ-and-definition-39-in-every-dimension).
- **Rates.** (4.49) holds with the rate `3^{−n/2}` in place of `3^{−n}`, and the lower bound (4.31)
  in expectation is proved with a deterministic slope `κ p` in place of the random one of AD, with
  the error `3^{−m/2}`.
- **Boundary error (4.27).** The paths of the cluster of the partition cubes at the faces stay in
  the crossing clusters of the partition cubes of the boundary vertices; the Hölder step uses the
  weight `W_∂` above and the moments of the partition sizes.
- **Definition 5.1.** The homogenized matrix `ā` is defined by polarization of the limit of
  `E[ν(□_m, ξ)]`, and bounded above and below by (5.1).
- **Counting convention.** AD write `⟨q, ∇[u]_𝒫⟩` as a sum over ordered pairs; the coarse pairing here
  counts each lattice edge once, as in the planar modules. The first line of AD (4.19) has a sign
  misprint: `μ(U, q) = −(1/2) ⟨∇u, a ∇u⟩_{C_*(U)}/\|U\|`.

## Lemmas 5.8 and 5.9 and the qualitative part of Proposition 5.2 for d = 2

Lemma 5.8 (flatness of the coarsened minimizers of `μ` and maximizers of `ν`) and Lemma 5.9 (the
decay of `D_n`) of Armstrong and Dario are proved in `d = 2`, in
[`PercolationClusterHomogenization/Proofs/Percolation/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Percolation/) from `PlanarFlatnessInputs.lean` to
`PlanarOmegaDecay.lean`, from the weak convergence of the spatial averages of the coarsened gradients
(Lemma 5.7, display (5.25)) and the almost additivity of these averages (Lemma 5.5, display (5.12))
alone. The proofs use the coarse energy bounds (4.24), (4.25) and the display (4.26) in `L²`, which are
proved here, not assumed. With Lemma 5.10 and `planarMuLimit_eq_of_decay` this gives the
identification `lim E[−μ(□_m, q)] = (1/2) q · ā⁻¹ q` (the qualitative part of Proposition 5.2) with
the following three hypotheses, for `𝔭_c(2) < p < 1`:

- [`PlanarWeakConvergence`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessInputs.lean), display (5.25) of
  Lemma 5.7: `E[\|\|□\|⁻¹ ⟨∇[u(·, □, q)]_𝒫⟩_□ − ā_{□_n}⁻¹ q\|²] ≤ C \|q\|² (τ_n + 3^{−n/4})` for every
  triadic cube `□` of scale `n`;
- [`PlanarRestrictQuadCoarsenMu`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessInputs.lean) and
  [`PlanarRestrictQuadCoarsenNu`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessInputs.lean), display
  (5.12) of Lemma 5.5, for `n ∈ [(9/10) m, m)`, with the almost-sure measurability of the quantities
  of the display.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.exists_coarseEnergyMu_majorant`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarCoarseEnergyMajorant.lean), [`exists_coarseEnergyNu_majorant`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarCoarseEnergyMajorant.lean) | AD (4.24) and (4.25), `d = 2`: for every `δ > 0` the normalized energy of the coarsened minimizer of `μ` and of the coarsened maximizer of `ν` on a cube `□` is almost surely below a measurable function of expectation at most `C(δ) \|q\|² size(□)^δ`. |
| [`sum_sq_planarNuGradAvg_sub_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarNablaAffineSq.lean), [`exists_lintegral_planarNuGradAvg_sub_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarNablaAffineMoments.lean) | AD (4.26) in `L²(P)`, `d = 2`: the spatial average of the coarsened gradient of the maximizer of `ν(V, p)` is within `C \|p\|² 3^{−n/4}`, in the second moment, of `p`. |
| [`exists_flatness_le_multiscale`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessBound.lean) | the multiscale Poincaré inequality (AD Proposition A.2) in the form of the first display of the proof of Lemma 5.8: the mean square of `w − ℓ_ξ` minus its mean is at most `C 3^{2n}(‖∇w‖² + \|ξ\|²) + C 3^m ∑_{k=n}^{m−1} 3^k (…)`. |
| [`exists_planarMuFlatness_majorant`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessMu.lean), [`exists_lintegral_planarMuFlatness_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessMu.lean), [`exists_planarNuFlatness_majorant`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessNu.lean), [`exists_lintegral_planarNuFlatness_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessNu.lean), [`exists_planarMuFlatness_majorant_ae`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessAE.lean), [`exists_planarNuFlatness_majorant_ae`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarFlatnessAE.lean) | AD Lemma 5.8, (5.32) and (5.33), `d = 2`: `E[\|□_{n+1}\|⁻¹ ∑ \|[u]_𝒫(x) − x · ā_{□_n}⁻¹ q − c\|²] ≤ C \|q\|² 3^{2n}(3^{−n/10} + 3^{−n} ∑_{k ≤ n} 3^k τ_k)` and the same for `v` and `ξ`, `c` the mean; the `_ae` forms hold from Lemmas 5.7 and 5.5 alone, with an almost-sure measurable majorant. |
| [`caccioppoli_dist`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaCaccioppoli.lean), [`clusterForm_restrict_le_caccioppoli`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaCaccioppoli.lean) | AD Lemma 3.5 from `□_{n+1}` to `□_n` on planar clusters: `B_{□_n}(w, w) ≤ 16 (3^n − 1)⁻² ∑_{C_*(□_{n+1})} (w − c)²` for `w` harmonic in the interior (the Caccioppoli step (5.39) of the proof of Lemma 5.9). |
| [`planarNu_sub_planarMu_sub_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaPointwise.lean), [`planarOmega_chain`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaChain.lean), [`planarOmega_real_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaAssembly.lean), [`planarOmega_integral_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaAssembly.lean) | the pointwise chain of the proof of Lemma 5.9, (5.38) to (5.41): `ν(V, p) − μ(V, q) − q · p` is bounded by the boundary error, three times the energies of the differences of Lemma 5.4, and the Caccioppoli term in the coarsening errors and the flatness errors of Lemma 5.8, and then, summed over the subcubes, by the subadditivity gaps; its integrated form. |
| [`exists_boundaryMajorant`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaBad.lean), [`exists_lintegral_not_resolved_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaBad.lean), [`exists_badMajorant`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaBad.lean), [`exists_lintegral_subMuSum_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaIntegrals.lean), [`exists_lintegral_subNuSum_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaIntegrals.lean), [`exists_lintegral_nuSubGap_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaIntegrals.lean), [`exists_muSubGap_majorant`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaIntegrals.lean), [`exists_subadditivityMajorant`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaMajorants.lean), [`exists_coarseError_majorant`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaMajorants.lean), [`planarTau_le_weighted`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaRates.lean) | the expectations of the terms of the chain: the boundary term (`C \|p\|₁ 3^{−n/2}`), the event that `□_n` is resolved and `□_{n+1}` is not (`C 9^{−n}`), the sums of `−μ` and `ν` over the subcubes by approximate stationarity, the subadditivity gaps (`C \|ξ\|₁² \|U\| 3^{−n/2}`), and the coarsening error through the reach of the partition, each with a measurable majorant, and the comparison `τ_n ≤ 3^{−n} ∑_{k ≤ n} 3^k τ_k`. |
| [`exists_planarOmegaD_le_of_inputs`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaDecay.lean), [`exists_planarOmegaD_decay`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaDecay.lean) | AD Lemma 5.9, (5.37), `d = 2`, in the form used by Lemma 5.10: for `n ≥ N`, `D_n ≤ K (3^{−n/10} + 3^{−n} ∑_{k ≤ n} 3^k τ_k)`, that is `D_n ≤ C σⁿ + C ∑_{l ≤ n} ρ^{n−l} τ_l` with `σ = 3^{−1/10}` and `ρ = 1/3`, without the absolute value. |
| [`Rigidity.Percolation.planarMuLimit_eq_of_inputs`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarOmegaDecay.lean) | AD Proposition 5.2, qualitative part, `d = 2`: `lim E[−μ(□_m, q)] = (1/2) q · ā⁻¹ q` from `PlanarWeakConvergence`, `PlanarRestrictQuadCoarsenMu` and `PlanarRestrictQuadCoarsenNu`; the hypothesis `h59` of `planarMuLimit_eq_of_decay` is discharged by `exists_planarOmegaD_decay`. |

The theorems of the table and their supporting results depend only on axioms among `propext`,
`Classical.choice` and `Quot.sound`; thirty-three of them (thirty theorems and three definitions,
those of the three hypotheses) have axiom reports in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean). The remaining hypotheses of the
identification are Lemma 5.7 (`PlanarWeakConvergence`) and Lemma 5.5
(`PlanarRestrictQuadCoarsenMu`, `PlanarRestrictQuadCoarsenNu`), which are the inputs that
[Clusters of integer cubes, the Meyers estimate and the coarse energy bounds toward Lemma 5.5](#clusters-of-integer-cubes-the-meyers-estimate-and-the-coarse-energy-bounds-toward-lemma-55)
reduces to the good events of the Meyers estimate; they are not proved in this section, and are theorems
for `p > 𝔭_c(2)` in [Lemmas 5.5 and 5.7 in dimension two](#lemmas-55-and-57-in-dimension-two).

Departures from Armstrong and Dario:

- **Index of the sum in (5.12).** AD print the sum `∑_{k=n}^{m+1} τ_k` in display (5.12) of
  Lemma 5.5; the last display of its proof and its use in the proof of Lemma 5.8 give
  `∑_{k=n}^{m−1} τ_k`, and the hypotheses `PlanarRestrictQuadCoarsenMu` and
  `PlanarRestrictQuadCoarsenNu` are stated with the sum over `k ∈ [n, m)`.
- **Lemma 5.7 for every cube.** `PlanarWeakConvergence` is stated for every triadic cube of scale `n`;
  AD state it for `□_n` and use it for every translate `z + □_n` by stationarity.
- **Flatness.** The flatness is measured with the mean of `w − ℓ_ξ` subtracted instead of AD's additive
  normalization of `u` and `v`; both rates in Lemma 5.8 are `3^{−n/10}` (AD print `3^{−2n/(2d+1)}` for
  `v`), which suffices for Lemma 5.9.
- **Lemma 5.9.** It is stated without the absolute value, as used in Lemma 5.10 and in the hypothesis
  `h59` of `planarMuLimit_eq_of_decay`.
- **The maximizer of `ν`.** `planarNuSolution` is the maximizer on the partition event for resolved
  cubes and `0` otherwise, a convention of this formalization (AD state `u ≡ 0` off the event, for `μ`); the
  values used agree.
- **(4.26) in `L²(P)`.** In `d = 2` the spatial average of the coarsened gradient of the maximizer of `ν` is within
  `C |p|² 3^{−n/4}` of `p` in the second moment, a weaker rate than printed; it is the rate the proof of Lemma 5.8 here uses.
- **Measurability.** Lower integrals are subadditive only for measurable summands. In the proof of
  Lemma 5.9 only one summand, the gap of `ν`, is not shown to be measurable; every other term has a
  measurable majorant, and measurability of the quantities of Lemma 5.5 is part of its hypothesis.

## Lemmas 5.5 and 5.7 in dimension two

Lemma 5.5 (display (5.12), for `μ` and for `ν`), Lemma 5.7 (display (5.25)) and the qualitative part of
Proposition 5.2 hold in `d = 2` for `𝔭_c(2) < p < 1` with no further hypothesis
([`planarRestrictQuadCoarsenMu_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHRestrictQuad.lean),
[`planarRestrictQuadCoarsenNu_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHRestrictQuad.lean),
[`planarWeakConvergence_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHWeakConv.lean),
[`planarMuLimit_eq`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHWeakConv.lean)): the three hypotheses of the
identification in the previous section are discharged, and
`lim E[−μ(□_m, q)] = (1/2) q · ā⁻¹ q` for every `q`.

The partition `𝓡` of Definition 3.7 is obtained from Propositions 2.1 and 2.4 applied to a local family
[`planarRHGood`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHLocal.lean). A cube is good when, on each of its
children `□`, the reverse Hölder inequality with exponent `2d/(d+1)` holds for every set of `3□`
closed under its open edges and every function harmonic on it. Its failure events are determined by
the open edges inside the threefold enlargement (hypothesis (2.1);
`measurableSet_not_mem_planarRHGood_local`). As at (3.12), its failure probability is bounded through
the planar partition: when the planar cells of `3□` have scale at most `k − 2` and
`∑ planarReach⁸ ≤ C |3□|`, the planar Lemma 3.6 holds on the cluster of the triple
(`planarRHCube_of_scales`). The parts of a closed set that no open edge leaves carry no energy, by the
Caccioppoli inequality; the parts that leave the triple meet its cluster, by the anchor property of the
planar cells. The concentration of the averages of the powers of the reach (the analogue of AD
Proposition 2.4 for the planar partition) is proved as well (`planarReachConcentration_holds`). The
hypothesis `PlanarGehringPartition`, a Gehring partition in the form used by the planar Meyers estimate,
remains only as the hypothesis of the earlier theorems `planarRestrictQuadCoarsenMu_of_gehring`,
`planarRestrictQuadCoarsenNu_of_gehring`, `planarWeakConvergence_of_gehring` and
`planarMuLimit_eq_of_gehring_partition`, which the theorems above supersede.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Cluster.measurableSet_not_mem_planarRHGood_local`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHLocal.lean) | the failure event of a cube `T` of the local family is determined by the open edges inside `3T`, as the hypothesis (2.1) of Proposition 2.1 requires. |
| [`planarRHCube_of_scales`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHEvent.lean), [`planarRHFailureBound_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHProb.lean) | the planar form of AD Lemma 3.6 on the triple of a cube whose partition cubes are small, and the failure bound (2.2) of the local family, `C exp(−c 3^{ns})`, for `p > 𝔭_c(2)`. |
| [`planarRHPartition_of_failureBound`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHPartition.lean), [`planarRHPartition_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHProb.lean) | the partition `𝓡` of AD Definition 3.7 in `d = 2`, with comparable neighbours, predecessors in the local family and, for every `t` and `B`, `∑_{x ∈ □} size(cell(x))^t ≤ K \|□\|` off an event of probability `C 3^{−Bk}` (Propositions 2.1 and 2.4). |
| [`Rigidity.Proofs.Cluster.planar_meyers_rh_uniform`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHMeyers.lean), [`meyers_triadic_uniform`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/MeyersUniform.lean), [`planar_meyers_uniform`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/MeyersUniform.lean), [`planar_meyers_clusterHarmonic_uniform`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/MeyersUniform.lean), [`partition_meyers_uniform`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/MeyersUniform.lean) | AD Proposition 3.8, deterministic part, in the form `∃ ε t, ∀ K, ∃ C`: the exponents `ε` and `t` depend only on the reverse Hölder constant (as the minimal scale `𝓜_t(𝓡)` requires) and only the constant depends on the moment bound `K`; for the local family `planarRHGood` in `planar_meyers_rh_uniform`. |
| [`planarReachConcentration_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarReachConcentrationHolds.lean), [`Rigidity.Percolation.exists_measure_not_mem_planarCoarseGood_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarReachDomination.lean), [`planarReach_le_stoppingSize`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarReachDomination.lean) | the analogue of AD Proposition 2.4 for the planar partition: `∑_{x ∈ □} planarReach(x)^τ ≤ A \|□\|` off an event of probability `C 3^{−Bk}`, through the coarsely good cubes, whose failure is determined by the threefold enlargement and whose stopping size dominates the reach. |
| [`planarRestrictQuadCoarsenMu_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHRestrictQuad.lean), [`planarRestrictQuadCoarsenNu_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHRestrictQuad.lean) | AD Lemma 5.5, display (5.12), `d = 2`, `p > 𝔭_c(2)`: on the good event the deterministic bound of Step 3 applies, and off it the Cauchy–Schwarz inequality with a measurable majorant built from the moments of the reach. |
| [`Rigidity.Proofs.Cluster.exists_planarMuRestrictError_majorant`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRestrictErrorMajorant.lean), [`exists_planarNuRestrictError_majorant`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRestrictErrorMajorant.lean), [`measure_restrictBad_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRestrictBad.lean), [`Rigidity.Percolation.measurable_planarMuRestrictError`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarRestrictErrorMeasurable.lean), [`measurable_planarNuRestrictError`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarRestrictErrorMeasurable.lean), [`measurable_planarMuGen_indicator`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarMuGeneral.lean) | the measurable majorants of the restriction errors, the probability of the bad event of the proof of Lemma 5.5, and the measurability of the errors (part of the hypothesis of the previous section, proved here). |
| [`Rigidity.Proofs.Cluster.exists_lintegral_sum_subcube_solenoidal_sq_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarOneVarEstBound.lean), [`exists_lintegral_planarMuRestrictFieldError_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRestrictFieldQuad.lean) | AD Lemma 5.7, display (5.30), `d = 2`: for `n ≥ 9`, `E[\|∑_V \|□_n\|⁻¹ ⟨∇[u(·, V, q)]_𝒫, g⟩_V\|²] ≤ C \|e\|₁² \|q\|² (τ_n + 3^{−n/4})`, the sum over the subcubes `V` of scale `n` of `□_{n+1}` and `g` the solenoidal field of Step 1; the expectation of the error of the pairing of a bounded field with the coarsened gradient on `U` against its restriction to the subcubes (from the hypothesis `PlanarGehringPartition`; the same bounds with no further hypothesis, above the partition `𝓡` of `planarRHPartition_holds`, are [`exists_lintegral_sum_subcube_solenoidal_sq_le_rh`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHWeakConv.lean) and [`exists_lintegral_planarMuRestrictFieldError_le_rh`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHRestrictQuad.lean), on which `planarWeakConvergence_holds` rests). |
| [`Rigidity.Proofs.Cluster.exists_measure_not_planarCapGood_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarSwitchLocProb.lean), [`exists_lintegral_sq_sub_switchLoc_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarSwitchLocProb.lean), [`exists_variance_planarMuGradAvg_origin_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarWeakConvOrigin.lean) | AD Proposition 4.9 and Lemma 5.7, display (5.31), `d = 2`: the planar partition is determined by the edges of a neighbourhood at the cap `k`, off an event of probability at most `C (2 · 3^{n−k} + 29)² exp(−c 3^k)`; for `n ≥ 120` and `k = ⌊n/12⌋` the pairing and its local version differ in mean square by at most `C G² \|q\|₁² 3^{−n/4}`; the variance of the spatial average at the origin is at most `C \|q\|² (τ_n + 3^{−n/4})` (the last from `PlanarGehringPartition`; with no further hypothesis in [`exists_variance_planarMuGradAvg_origin_le_rh`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHWeakConv.lean), on which `planarWeakConvergence_holds` rests). |
| [`Rigidity.Percolation.exists_lintegral_planarMuDefect_le_tau`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarDefectTauCube.lean), [`exists_lintegral_planarNuDefect_le_tau`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Percolation/PlanarNuDefectTauCube.lean) | AD Lemma 5.4, display (5.10), `d = 2`, on every triadic cube `U`: `E[1{𝒫, U resolved} D_n(U, q)] ≤ \|U\| C \|q\|² (∑_{k=n}^{m−1} τ_k + 3^{−n/4})` for `μ` and for `ν`. |
| [`planarWeakConvergence_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHWeakConv.lean), [`planarMuLimit_eq`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarRHWeakConv.lean) | AD Lemma 5.7, display (5.25), for every triadic cube, and AD Proposition 5.2, qualitative part, `d = 2`, `p > 𝔭_c(2)`: `lim E[−μ(□_m, q)] = (1/2) q · ā⁻¹ q`. |

The theorems of the table and the earlier theorems from `PlanarGehringPartition` depend only on axioms among
`propext`, `Classical.choice` and `Quot.sound`; forty reports (thirty-eight theorems and two definitions)
are in [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Departures from Armstrong and Dario:

- **The partition `𝓡`.** The good cubes ask the reverse Hölder inequality for all sets of the triple
  of each child closed under the open edges and all functions harmonic on them, not only for
  `𝒞_max(3□)` with the numerator `𝒞_*(□)` as in Definition 3.7. A cube of positive scale is good when
  the inequality holds on each of its nine children, with the energy of the closed set on the child as
  numerator; no well-connectedness is asked, and the cubes of scale zero are good. The family stays local, so that
  Propositions 2.1 and 2.4 apply to it; its failure probability is bounded through the planar
  partition, as AD bound (3.12) through the minimal scale of `𝒫`, with polynomial rates in place of
  the stretched exponentials of the tails of `𝓡`.
- **Moment exponent.** The Meyers estimate is restated with `ε` and `t` chosen before the moment
  bound `K`, the order that the minimal scale `𝓜_t(𝓡)` requires. The Lean uses
  `t = (2+ε)(1+ε)(d+1)/ε`, given by the Hölder inequality; the exponent printed at AD18.tex:1657-1663
  has a harmless factor-2 slip.
- **Lemma 5.5, Step 3.** The Hölder inequality is applied inside each cell, as in the section on the
  Meyers estimate; the cells are the triadic squares of scale `⌊n/2⌋ − 1` of the inner square, so that the
  triples and their lattice neighbourhoods lie inside the subcube, the weight is `W_t = 3 planarReach`, and
  `W = 3 √A₂ 3^k` on `U`. Off the good event the Cauchy–Schwarz inequality is used with a measurable
  majorant built from the moments of the reach; the decay is `C 3^{−Bk}`.
- **Proposition 2.4.** The concentration of the reach is proved for the planar partition through the
  coarsely good cubes (the subcubes five scales down are good; the failure of a cube is determined by
  its threefold enlargement and each subcube is ninefold local), whose stopping size dominates the reach.
- **Lemma 5.7, display (5.31).** The cap is at `k = n/12` (AD: `⌈n/2⌉`), with deterministic window bounds on
  the capped event in place of moments; the local version is the clamp to `[−M, M]` of the value at a
  configuration of the capped event with the same open edges in the neighbourhood, and `Ψ` is obtained by
  polarization of the matrix `planarMuGen` with the fields restricted to the interior (AD use `μ_loc`
  pairs on the interior). This route needs `n ≥ 120`; `n < 120` is covered by the deterministic bound, and
  every cube by translation on the local good events.

## The rate of Proposition 5.2 and Lemmas 5.3, 5.10 and 5.11 (Step 2) in dimension two

For `𝔭_c(2) < p < 1` and with no hypothesis, the rate of convergence of the expectations in
Proposition 5.2 (display (5.4)), Lemma 5.10 (display (5.42)), Step 2 of the proof of Lemma 5.11 and a
deterministic pointwise form of Lemma 5.3 are proved, in
[`PercolationClusterHomogenization/Proofs/Cluster/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Cluster/). The decay of `D_n` of Lemma 5.9 holds
without the hypothesis `h59` (`exists_planarOmegaD_decay_holds`, from Lemmas 5.5 and 5.7 of the previous
section), `τ_n` and the finite-volume matrices `ā_{□_n}⁻¹` converge to `ā⁻¹` geometrically, and then
`|E[−μ(□_n, q)] − (1/2) q · ā⁻¹ q| + |E[ν(□_n, ξ)] − (1/2) ξ · ā ξ| ≤ C (|ξ|² + |q|²) 3^{−nα}` for
some `α ∈ (0, 1/4]`. The quantity `ρ = sup_q |q|⁻² ω₊` has a measurable majorant of expectation at
most `C 3^{−nα}`, its truncated stationary version has expectation at most `C (1 + C₁) 3^{−nα}`, and
sums of truncated versions over the subcubes of a cube of scale `n + 3 + j` satisfy the Chernoff
bound of Step 2. Proposition 5.2 in the `O_s` form, Steps 1 and 3 of Lemma 5.11 and
Proposition 5.13 (`p.boundN`) are not proved in this section: Step 1 of Lemma 5.11 needs a stretched
exponential tail of the minimal scale (the averages of the sizes of the cells over a cube, AD18.tex:1958
through Proposition 2.4), whereas the concentration of the partition proved here
(`planarReachConcentration_holds`, `planarRHPartition_holds`) has the polynomial tail `C 3^{−Bk}`. They are
proved in [Propositions 5.2 and 5.13, Lemma 5.11 and the minimal scales in dimension two](#propositions-52-and-513-lemma-511-and-the-minimal-scales-in-dimension-two).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Cluster.exists_planarOmegaD_decay_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarConvergenceRate.lean), [`exists_planarOmegaD_le_geometric`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarConvergenceRate.lean), [`exists_planarTau_le_geometric`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarConvergenceRate.lean) | AD Lemma 5.9 with no hypothesis, and the geometric decay `D_n, τ_n ≤ K l^n` for `n ≥ N`, `l < 1`. |
| [`planarAhomInvLimit_eq_inv`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarConvergenceRate.lean), [`exists_abs_planarAhom_inv_sub_planarAhomInvFinite_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarConvergenceRate.lean) | AD Lemma 5.10, Step 4, `d = 2`: the limit of the finite-volume matrices is `ā⁻¹`, and `\|(ā⁻¹)_{ij} − (ā_{□_n}⁻¹)_{ij}\| ≤ K l^n` for `n ≥ N`. |
| [`planar_convexp`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarConvergenceRate.lean) | AD Proposition 5.2, display (5.4), `d = 2`: there are `α ∈ (0, 1/4]` and `C` with `\|E[−μ(□_n, q)] − (1/2) q · ā⁻¹ q\| + \|E[ν(□_n, ξ)] − (1/2) ξ · ā ξ\| ≤ C (\|ξ\|² + \|q\|²) 3^{−nα}` for all `n`, `ξ`, `q`. |
| [`planar_omegadecayrate`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarOmegaSupRate.lean) | AD Lemma 5.10, display (5.42), `d = 2`: for each `n` there is a measurable `M`, at least `ρ(□_n) = sup_q \|q\|⁻² ω₊(□_n, q)` almost surely, with `E[M] ≤ C 3^{−nα}`. |
| [`exists_integral_min_planarRhoStat_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarSIStepTwo.lean) | AD Lemma 5.11, Step 2: the truncated stationary version `ρ_stat` of `ρ` on a cube `V` satisfies `E[min(ρ_stat, C₁)] ≤ C (1 + C₁) 3^{−nα}`. |
| [`measureReal_sum_ge_le_of_bounded`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/BoundedChernoff.lean), [`planar_SIupgrade_step2`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarSIStepTwo.lean) | the Chernoff bound of Step 2 (variables in `[0, A]` with expectations at most `ε`, each independent of the sum of any set of the others not containing it: `P[∑ ≥ \|s\| t] ≤ exp(−\|s\|(t − (e − 1)ε)/A)`), and AD Lemma 5.11, Step 2, the display at AD18.tex:3944-3947: the sum of `min(ρ_stat, C₁)` over the 729 groups of subcubes of scale `n` of a cube of scale `n + 3 + j`, `9^j` per group, exceeds `729 · 9^j t` with probability at most `729 exp(−9^j (t − (e − 1) C (1 + C₁) 3^{−nα})/C₁)`. |
| [`abs_quadratic_sub_half_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarMinimalSet.lean), [`planar_minimalset`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarMinimalSet.lean) | AD Lemma 5.3, `d = 2`, in a deterministic pointwise form: on the partition event for a resolved cube `U`, `\|μ(U, q) + (1/2) q · ā⁻¹ q\| ≤ (4 Y S + √(8 (Λ + 1)(ρ + Y S))) \|q\|²` and the corresponding bound for `ν(U, ā⁻¹ q) − (1/2) q · ā⁻¹ q`, with `Y` the random error of the comparison of Corollary 4.6, `Λ` the bound of `−μ`, `ρ` of Lemma 5.10 and `S` an `ℓ¹` operator bound of `ā⁻¹` (`‖ā⁻¹ v‖₁ ≤ S ‖v‖₁`); the statement assumes `Y(U) < ∞`, which holds almost surely since `E[Y] < ∞`. |

The twelve declarations of the table have axiom reports in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean), and depend only on axioms among `propext`,
`Classical.choice` and `Quot.sound`.

Departures from Armstrong and Dario, which are choices of the formalization:

- **Display (5.4).** The `μ` part follows from the rate of `ā_{□_n}⁻¹` (Lemma 5.10, Step 4, display (5.24)); the `ν` part is obtained by
  summing the increments bounded by `τ_k` through (5.9), with `α ≤ 1/4`. AD derive (5.4) from (5.5) and Lemma 5.3.
- **Zero off the event.** `μ` and `ν` are set to `0` off the partition event and for unresolved cubes
  (AD set `u = 0` there); `ω` is then `−q · ā⁻¹ q`, so that `ω₊` and `ρ` are `0`.
- **A measurable majorant for `ρ`.** The supremum over the uncountably many `q` is not shown measurable;
  Lemma 5.10 is stated through a measurable majorant `M`.
- **The random error of Corollary 4.6.** The error `Y` of the comparison, of expectation at most `C 3^{−n/2}`, is kept random
  in Step 4 of Lemma 5.10 and in `planar_minimalset`.
- **Independence in Lemma 5.11.** Each local quantity is independent of the sums of the others only
  over pairwise disjoint local regions (of side `14 · 3^n`). The subcubes are therefore grouped by their
  position modulo `27`, and a union bound over the `729` groups replaces the single product of Step 2.
- **Lemma 5.3.** A gradient step replaces the minimizer `q₀` (so no `k(□)` is needed), and the random factor
  `√(Λ(U) + 1)` multiplies `ρ^{1/2}`; the statement is deterministic and pointwise, with the errors named.

Misprints in the source whose meaning is clear: AD18.tex:2232 (`|q|²` appears twice); :3929 (`t := 1/K` with
`K` undefined, `t = 1/C`); :3975 and :4003-4029 (`μ − (1/2) q · ā⁻¹ q` for `μ + (1/2) q · ā⁻¹ q`); :4003, :4012-4016,
:4018-4025 and :4029 (`exp(−C⁻¹ 3^{−αm})` for `exp(−C⁻¹ 3^{αm})`); :4195 (`(1/2) p · ā p + ν` for `(1/2) p · ā p − ν`).

## Propositions 5.2 and 5.13, Lemma 5.11 and the minimal scales in dimension two

For `𝔭_c(2) < p < 1` and with no other hypothesis, the stretched exponential form of the convergence of
the subadditive quantities (Proposition 5.2, displays (5.2) and (5.3)), Lemma 5.11, the random scale of
Proposition 5.13 and the minimal scales of Proposition 2.4 are proved, in
[`PercolationClusterHomogenization/Proofs/Cluster/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Cluster/). The bounds are stated with `IsOsBond`, the
stretched exponential moment (`X ≤ O_r(θ)`) of the source, and are stable statements that the later results of
the dimension-two chain take as hypotheses
([`PlanarScaleStatements.lean`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarScaleStatements.lean)).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Cluster.exists_planar_minimalScale`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarMinimalScales.lean) | AD Proposition 2.4 for a family of cubes with the local measurability (2.1) and the failure bound (2.2): for every `τ` and `α > 0` a minimal scale `M ≤ O_r(θ)` such that, whenever `M ≤ 3^m`, the `τ`-th moment of the sizes on `□_m` is at most `K \|□_m\|` and every size is at most `3^{α m}`. |
| [`Rigidity.Proofs.Cluster.planarMinimalScales_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarMinimalScales.lean) | the statement `PlanarMinimalScales p` ([`PlanarScaleStatements.lean`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarScaleStatements.lean)): the partition `𝓡` of Definition 3.7 (maximal stopping cubes of the local family `planarRHGood`), with, for all `t, α > 0`, a minimal scale `M ≤ O_r(θ)` above which on `□_m` the `t`-th moments of the sizes of the cells of `𝓡`, of the planar partition cubes and of `planarReach` are at most `K \|□_m\|` and these sizes are at most `3^{α m}`. |
| [`planarMinimalScales_partition_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarScaleForms.lean), [`planarMesoscopicConvergence_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarScaleForms.lean) | the two statements `Rigidity.Dirichlet.PlanarMinimalScales` and `Rigidity.Dirichlet.PlanarMesoscopicConvergence`, in the form of the inputs of the proof of Theorem 1 in dimension two: both bounds of (2.13) for the planar partition (`t ≥ 1`), and Proposition 5.13 on the triadic subcubes of `□_m` of scale `⌈m/8⌉`. |
| [`exists_measure_not_planarReachLe_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarReachEvent.lean), [`planarRho_le_avg_of_planarReachLe`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarReachErrors.lean), [`planarComparisonError_le_of_planarReachLe`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarReachErrors.lean), [`sum_subcubesAt_eq_sum_sum`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarSubcubeIndex.lean) | the event that the reach is at most `3^ℓ` on a cube and the deterministic bounds on it: `-μ`, the error of the comparison of Corollary 4.6, the subadditivity errors and the subadditivity (5.56) of `ρ`; the subcubes of `□_{n+3+j}` are the cubes `⟨n, a + 27 b⟩`. |
| [`exists_planarRho_tail`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarSIUpgrade.lean) | AD Lemma 5.11, Steps 1 to 3: the stretched exponential tail of `ρ(□_{n+3+j})` at an explicit threshold, together with the event that the reach is at most `3^ℓ`. |
| [`exists_planarSubaddGood_tail`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarSubaddTail.lean), [`exists_planarSubaddGood_tail_cube`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarBoundN.lean) | AD Proposition 5.2 as a tail bound: `\|μ(V, q) + (1/2) q · ā⁻¹ q\| ≤ K \|q\|² 3^{−β scale V}` and `\|ν(V, ξ) − (1/2) ξ · ā ξ\| ≤ K \|ξ\|² 3^{−β scale V}` on the partition event with `V` resolved, off an event of probability at most `K' exp(−c 3^{m s})`, for `□_m` and then for every triadic cube and every translate. |
| [`planar_subadd_os`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarSubaddOsMain.lean) | AD Proposition 5.2, displays (5.2) and (5.3), `d = 2`: there are `r, α, C > 0` such that, for every triadic cube `V`, the random error `X(V)` of `μ(V, ·) + (1/2) q · ā⁻¹ q` and `ν(V, ·) − (1/2) ξ · ā ξ` (with `μ = ν = 0` off the event that the partition exists and resolves `V`) is measurable with `X(V) ≤ O_r(C 3^{−α scale V})`, `\|μ-error(q)\| ≤ X \|q\|²` and `\|ν-error(ξ)\| ≤ X \|ξ\|²`. |
| [`planar_SIupgrade_os`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarSIUpgradeOs.lean) | AD Lemma 5.11, `d = 2`: `sup_q \|q\|⁻² \|ω(V, q)\| ≤ O_r(C 3^{−α scale V})`, with a measurable majorant, for every triadic cube `V`. |
| [`planar_muupbound_os`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarSIUpgradeOs.lean) | AD (4.17), `d = 2`, with the rate `size^{−α}` in place of `size^{−1}`: `−μ(V, q) ≤ (K + Z(V)) \|q\|²` with `Z(V) ≤ O_r(C 3^{−α scale V})`. |
| [`planarBoundN_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarBoundN.lean), [`exists_planarBoundN_general`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarBoundN.lean) | AD Proposition 5.13, `d = 2` (the statement `PlanarBoundN p`): a random scale `N ≤ O_r(θ)` such that, whenever `N ≤ 3^m` and `n = ⌈m/4⌉`, on the triadic cubes `V` of scale `n` in `□_m`, and on `□_n` in the configuration translated by `−z` for every `z ∈ □_m`, the partition event holds, the cube is resolved, and `\|μ + (1/2) q · ā⁻¹ q\| ≤ C \|q\|² 3^{−mα}`, `\|ν − (1/2) ξ · ā ξ\| ≤ C \|ξ\|² 3^{−mα}`; the second theorem allows any `n(m)` with `n(m) ≤ m ≤ L n(m)`. |
| [`osBound_indicator`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/OsTailCalculus.lean), [`OsBound.add`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/OsTailCalculus.lean), [`OsBound.mul`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/OsTailCalculus.lean), [`isOsBond_of_osBound`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/OsTailCalculus.lean) | the calculus of the stretched exponential bounds used above, in the tail form: indicators, sums, products (AD (1.9)) and the passage to `IsOsBond`. |

The twenty-three reports of the declarations of this section and of the `O_s` calculus are in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Departures from Armstrong and Dario:

- **Lemma 5.11, Step 1.** The bad event is that the reach exceeds `3^ℓ` somewhere on `□_m`, of probability
  at most `9^m · 2 exp(−3^ℓ/θ)`, with the constant `C₁ = C 81^ℓ` growing with `ℓ` and `3^ℓ ≈ 3^{nα/24}`. AD obtain a
  fixed constant `C₁` through the minimal scales ((4.17)).
- **Lemma 5.11, Step 3.** On that event the errors of the subadditivity (5.56) are bounded deterministically,
  by `C (ℓ + 1) 531441^ℓ 3^{−n/2}`, in place of an `O_s(C 3^{−k/4})` bound.
- **Proposition 5.2.** It is proved first as a tail bound and transported from `□_m` to every triadic cube and
  every translate; the `O_s` form follows from the bound `X ≤ 12 K 3^{−βm} + c (1 + M⁴) 1_{bad}`, with `M` the
  largest size of a partition cube meeting `V` and the tail calculus at the exponent `r = 1/5`. Lemma 5.11 in the
  `O_s` form is derived from Proposition 5.2, whereas AD derive Proposition 5.2 from Lemma 5.11 and Lemma 5.3.
- **Proposition 5.13.** The translates `z + □_n` are taken for every `z ∈ □_m` (AD take `z ∈ 3^k ℤ²` with
  `k = ⌈m/8⌉`), as `□_n` in the translated configuration, together with the triadic subcubes of scale `n` for the
  partition of `ω`; the scale is `N = 3 sup{3^m : the bound fails at m}`, controlled through the exponential
  moment of the exceptional scale of Lemma 2.3; and the scales are `n = ⌊m/2⌋` in Lemma 5.11 (AD take `⌈m/2⌉`).
- **Signs in Proposition 5.13.** The statement uses the signs of Proposition 5.2, `μ + (1/2) q · ā⁻¹ q` and
  `ν − (1/2) ξ · ā ξ`.

## The Dirichlet problem and the excess-decay iteration

The proof of Theorem 2 of AD compares a solution on the cluster with the solution of the homogenized
Dirichlet problem on a cube (AD, §6) and iterates this comparison over the scales to obtain the
large-scale regularity (AD, §7). The deterministic steps of both are proved, for every `d`: the
comparison of the energies and the error chain of AD, Proposition 6.1, with the inputs on the
cluster (the subadditive quantities `μ` and `ν` in every dimension and the convergence rates of
AD, §5) as hypotheses; and the iteration of AD, Lemma 7.2, with its excess-decay and
harmonic-approximation hypotheses, the excess decay being proved for the harmonic functions of
`ℤᵈ` and of the plane.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Dirichlet.innerEdgeEnergy_dirichletSolution_div_le_of_coarse`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/LemmaSixTwoCoarse.lean) | AD Lemma 6.2 on the lattice: the normalized homogenized energy of the solution `u_hom` of the discrete `ā`-Dirichlet problem on a cube `Q` of side `L`, with the boundary interpolation `w̃` of the coarsened function as datum, is at most the energy of `u` in `Q` plus the errors of the `μ` test and `C((r + N)/L)^{1−2/s}` times the bound of Lemma 6.4 (iii). |
| [`Rigidity.Dirichlet.patch_cubeCutoff_of_not_mem`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/CutoffRegions.lean) | AD Lemma 6.3 (i) on the lattice: off the cube the patched function is the outer function. |
| [`Rigidity.Dirichlet.innerEdgeEnergy_patch_div_le_of_coarse`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/LemmaSixThreeCoarse.lean) | AD Lemma 6.3 (ii) on the lattice: the energy on the cluster of the patch `ũ` of the `ν`-maximizers and of `u_hom` is at most the homogenized energy of `u_hom` plus the boundary-layer and patching errors. |
| [`Rigidity.Dirichlet.exists_sum_sq_patch_sub_div_le_of_coarse`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/LemmaSixThreeCoarse.lean) | AD Lemma 6.3 (iii) on the lattice: `L^{−d} Σ (ũ − u_hom)²` is at most the `L²` distances of the maximizers to their affine functions plus `C N⁴ r^{−2}` times the bound of Lemma 6.4 (iii). |
| [`Rigidity.Dirichlet.sum_abs_grad_boundaryInterpolation_rpow_div_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/Interpolation.lean) | AD Lemma 6.4 (iii) on the lattice: for `1 ≤ s < p`, the normalized `Lˢ` norm of `∇w̃` is at most the moments of the partition sizes times `(V⁻¹ Σ_{C_*} \|∇u 1_{𝐚≠0}\|^p)^{s/p}`. |
| [`Rigidity.Dirichlet.sum_sq_sub_le_of_inner_energy_chain`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/PropSixOne.lean) | AD Proposition 6.1 on the lattice, from the energy comparisons: if `u` is harmonic in `Q`, `ũ = u` off the interior of `Q`, `E_hom(u_hom) ≤ E(u) + δ₁` and `E(ũ) ≤ E_hom(u_hom) + δ₂`, then `Σ (u − u_hom)² ≤ 2P(δ₁ + δ₂)/λ + 2δ₃`, with `P` a Poincaré constant for `ũ − u` and `δ₃` a bound for `Σ (ũ − u_hom)²`. |
| [`Rigidity.Dirichlet.sum_energy_cubeLayer_div_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/LayerEnergyBound.lean) | the energy of the discrete homogenized solution in the boundary layer of width `ℓ + 1` of a cube of side `N` is at most twice that of its datum plus `C((ℓ + 1)/N)^γ (N^{−d} Σ \|∇f\|^p)^{2/p}`, for `p > 2` and small `γ > 0`. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/KIterationGeneral.lean) | AD Lemma 7.2 for every `k`, for abstract seminorms with the excess-decay hypothesis: `D_k(r) ≤ C(r/R)^{k+1} D_k(R) + C r^{1−α}(D_0(R)/R + E/r)` for `r ∈ [X ∨ C, R/2]`. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_zero`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/KIteration.lean) | AD Lemma 7.2 for `k = 0`: `D_0(r) ≤ C(r/R) D_0(R) + C r^{1−α}(D_0(R)/R + E/r)`. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_one`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/KIteration.lean) | AD Lemma 7.2 for `k = 1`, with the quadratic polynomials: `D_1(r) ≤ C(r/R)² D_1(R) + C r^{1−α}(D_0(R)/R + E/r)`. |
| [`Rigidity.Proofs.Regularity.harmonicRegularity_latticeHarmonicClass`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/LatticeHarmonicExcess.lean) | the excess decay of order one of the harmonic functions on the balls of `ℤᵈ`, above a fixed radius. |
| [`Rigidity.Proofs.Regularity.harmonicRegularity_planarHarmonicClass`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicRegularity.lean) | the excess decay of order one of the harmonic functions on the discs of `ℝ²`, in the normalized `L²` norms, with the constant `1024`. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_zero_latticeHarmonic`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/LatticeHarmonicExcess.lean) | AD Lemma 7.2 for `k = 0` with the harmonic functions on the balls of `ℤᵈ`, from the harmonic-approximation hypothesis alone. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_one_latticeHarmonic`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/LatticeHarmonicExcessTwo.lean) | AD Lemma 7.2 for `k = 1` with the harmonic functions and the harmonic quadratic functions on the balls of `ℤᵈ`, from the harmonic-approximation hypothesis alone. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_zero_planar`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicRegularity.lean) | AD Lemma 7.2 for `k = 0` in the plane, in the normalized `L²` norms of Lebesgue measure with the harmonic functions on discs, from the harmonic-approximation hypothesis alone. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_one_planar`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicRegularityTwo.lean) | AD Lemma 7.2 for `k = 1` in the plane, from the harmonic-approximation hypothesis alone. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_3_zero_planar`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicRegularity.lean) | the iteration of AD Lemma 7.3 for `k = 0` in the plane, from the harmonic-approximation hypothesis. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_3_one_planar`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicRegularity.lean) | the same for `k = 1`. |
| [`Rigidity.Proofs.Regularity.armstrongDario_orderZero_origin_planar`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicRegularity.lean) | order-zero regularity at the origin in the plane: one constant `φ` with `‖u − φ‖_{L̲²(B_r)} ≤ C(r/R)B` for `r ∈ [X ∨ C, R/2]`, under the harmonic-approximation hypothesis. |

The nineteen theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules
are in [`PercolationClusterHomogenization/Proofs/Dirichlet/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Dirichlet/) and
[`PercolationClusterHomogenization/Proofs/Regularity/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Regularity/).

1. **The discrete Dirichlet problem** (`BoundaryData.lean`, `BoundaryLayer.lean`, `Hardy*.lean`,
   `WeightedEnergy.lean`, `LayerEnergy*.lean`). Existence and uniqueness, the Dirichlet principle,
   the energy identity and the maximum principle on lattice cubes, and the energy of the
   homogenized solution in a boundary layer through a Hardy-weighted energy estimate.
2. **Lemma 6.2** (`LemmaSixTwo*.lean`, `TrialEnergy*.lean`, `MuTest.lean`, `Mesoscopic*.lean`,
   `CubeTiling.lean`, `CubeStokes.lean`). The coarsened function, cut off near the boundary and
   averaged over the translates of a mesoscopic cube, is a trial function for the homogenized
   energy, compared with the energy of `u` through the `μ` test.
3. **Lemma 6.3** (`LemmaSixThree*.lean`, `Patching*.lean`, `Tile*.lean`, `AffinePatch.lean`,
   `InteriorH2.lean`, `SecondDifferences.lean`, `BoundaryCaccioppoli.lean`). The `ν`-maximizers on
   the tiles are patched along the affine approximations of `u_hom`, with the interior second
   differences of `u_hom` and the boundary-layer energy.
4. **Lemma 6.4 and Proposition 6.1** (`Interpolation.lean`, `EnergyComparison.lean`,
   `DirichletError.lean`, `PropSixOne.lean`). The boundary interpolation of the coarsened function is
   bounded by Lemmas 3.2 and 3.3, and the two energy comparisons give the `L²` error by the
   Pythagorean identity for harmonic functions.
5. **The iteration** (`BallExcess.lean`, `KIteration*.lean`, `SinglePolynomial.lean`). Lemma 7.2 is
   proved for abstract seminorms with a reverse monotonicity, Poincaré and excess-decay hypotheses,
   for every `k`, and for `k = 0, 1` in cluster, lattice and continuum instances.
6. **Excess decay** (`LatticeHarmonic*.lean`, `MixedDifferenceSobolev.lean`, `DiscreteTaylor.lean`,
   `PlanarHarmonic*.lean`). For harmonic functions on the balls of `ℤᵈ` by discrete Taylor
   expansions and Sobolev bounds of mixed differences; in the plane from the harmonic functions as
   real parts of holomorphic functions, the Borel–Carathéodory and Cauchy estimates and the
   mean-value property.

Departures from Armstrong and Dario:

- **The homogenized problem is discrete.** `u_hom` is the solution of the discrete Dirichlet problem
  for the constant conductance `ā` on the lattice cube, with the boundary interpolation `w̃` of the
  coarsened function as datum; AD use the continuum problem on the cube with a mollified datum.
  Lemma 6.4 (i) and (ii) are therefore not needed and (iv) is not used; Lemma 6.2 averages over all
  translates of the mesoscopic cube, and the energies are those of the edges inside `Q`.
- **No Meyers estimate for `u_hom`.** AD bound the boundary-layer energy of `u_hom` by the Meyers and
  `H²` estimates of AD, Proposition 6.5 (from Giusti); the Lean proof uses the interior second
  differences and a Hardy-weighted energy estimate on the lattice.
- **Lemma 6.3, Step 1.** Testing `v_y` in `μ(y + □_n, q)` gives a lower bound for the energy of
  `v_y`; the upper bound needed is obtained from the first variation of `ν` at its maximizer `v_y`,
  `E(v_y) = ⟨p, 𝐚∇v_y⟩`, so that `ν = E(v_y)/(2\|cl\|)` (`energy_le_of_nu_maximizer`).
- **Inputs on the cluster.** The `μ` test, the `ν`-maximizers and their Poincaré bounds, the
  convergence rates of AD, §5, and the Poincaré inequality for `ũ − u` enter as hypotheses.
- **Lemma 7.2.** The excess decay of `ā`-harmonic functions is proved for `ā = ½σ²I` (AD note that `ā`
  is a multiple of the identity, by the symmetries of the model): for the harmonic functions of
  `ℤᵈ`, and in the plane for the continuum norms of AD; for `d ≥ 3` the continuum excess decay is not
  proved. The harmonic approximation (AD, Lemma 7.1) and the transfer from the coarsened function to
  `u` in AD, Lemma 7.3, remain hypotheses; the general `k` follows the case `k = 0` with the excess
  over the polynomials of degree `k`, whose details AD omit, referring to Step 3 of the proof of
  Lemma 2.4 of Armstrong, Kuusi and Mourrat.

## Theorem 1 of Armstrong and Dario in dimension two

Theorem 1 of Armstrong and Dario (the homogenization error for the Dirichlet problem on the cluster of a cube)
is proved in `d = 2` for every `𝔭_c(2) < p < 1` and every exponent `p' > 2`, with no further hypothesis
([`Rigidity.Dirichlet.planarHomogenizationError_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/PlanarTheoremOneHolds.lean)),
in the form `PlanarHomogenizationError p p'`
([`PlanarStatements.lean`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/PlanarStatements.lean)): `ā = σ I` with `σ > 0`, and there
are `s, α, C > 0` and a measurable random scale `X ≤ O_s(C)` such that, whenever `X ≤ 3^m`, the partition event
holds, the cube `□_m` is resolved and, for every `u` harmonic on the cluster `𝒞_*(□_m)` off the boundary of the
cube, there is a discrete harmonic function `u_hom` on the lattice cube (for the constant conductance `1`) that
equals `u` on `𝒞_*(□_m)` off the interior of the cube, with
`|□_m|⁻¹ Σ_{edges of □_m} |∇u_hom|² ≤ C M²` and
`3^{−m} (|□_m|⁻¹ Σ_{𝒞_*(□_m)} (u − u_hom)²)^{1/2} ≤ C 3^{−mα} M`,
where `M = (|□_m|⁻¹ Σ_{𝒞_*(□_m)} |∇u 1_{𝐚≠0}|^{p'})^{1/p'}`. The rate is `α' = c₀/32` with
`c₀ = min(8α, 1/2, 4(1 − 2/t), 4γ)`, `t = (2 + p')/2` and `γ = min(1/16, (t − 2)/(2t))`, where `α` is the exponent of
the convergence of `μ` and `ν`.

The proof is the chain of Section 6, with the two inputs of the source in Section 5 and Section 2 supplied by
theorems:

* the convergence of `μ` and `ν` on the mesoscopic cubes, Definition 5.12, Proposition 5.13 and (6.4)–(6.5)
  (`planarMesoscopicConvergence_holds`, from
  [Propositions 5.2 and 5.13, Lemma 5.11 and the minimal scales in dimension two](#propositions-52-and-513-lemma-511-and-the-minimal-scales-in-dimension-two));
* the minimal scales of the planar partition, both bounds of (2.13) (`planarMinimalScales_partition_holds`, from
  the same section).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Dirichlet.planarHomogenizationError_of_inputs`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/PlanarTheoremOne.lean), [`planarHomogenizationError_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/PlanarTheoremOneHolds.lean) | AD Theorem 1, `d = 2`, `PlanarHomogenizationError p p'` for `p' > 2`: from the two inputs `PlanarMesoscopicConvergence p` and `PlanarMinimalScales p`, and then with no hypothesis. |
| [`Rigidity.Percolation.exists_planarAhom_eq_smul_one`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarAhomIsotropic.lean), [`planarNuLimit_signedPermSlope`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/PlanarSignedPermCluster.lean) | the remark after (5.22): `ā = σ I` with `σ > 0`, from the invariance of the limit of the expectations of `ν` under the reflection and the transposition of the coordinates, which carry the planar partition, the cluster of a resolved cube and `ν` to those of the transported configuration. |
| [`Rigidity.Dirichlet.planarMu_le_test`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/PlanarMuTest.lean), [`exists_mu_test_of_subcubes`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/SubcubeMuTest.lean), [`sum_subcube_errors_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/SubcubeMuTest.lean) | the `μ` test of display (6.9) on a resolved subcube, the `μ` test on a translate of a mesoscopic cube from the tests on a block of its subcubes, and the sum of the errors of these tests over the translates. |
| [`planar_lemmaSixTwo`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/PlanarLemmaSixTwo.lean), [`planar_lemmaSixThree`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/PlanarLemmaSixThree.lean) | AD Lemma 6.2 (the `μ` test at every translate of the mesoscopic cube from the tests on its triadic tiles) and Lemma 6.3 (ii) (the patch of the maximizers of `ν` on the tiles), `d = 2`, with explicit errors. |
| [`planar_sum_abs_grad_boundaryInterpolation_rpow_div_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/PlanarInterpolation.lean), [`sum_three_pow_pairReachScale_rpow_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/PlanarInterpolation.lean), [`exists_planar_sum_sq_le_of_eq_zero`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/PlanarPoincareZero.lean) | AD Lemma 6.4 (iii) for the planar partition with the reach scales, the bound of the moments of the pair reach scales by the moments of the sizes of the partition cubes, and the Poincaré inequality on the cluster of a planar cube for functions vanishing on its boundary (Proposition 3.4 with `s = 2`). |
| [`planar_sum_sq_sub_uhom_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/PlanarPropSixOne.lean), [`planar_error_chain`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/PlanarErrorChain.lean), [`chain_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Dirichlet/PlanarChainBound.lean) | AD Proposition 6.1 in `d = 2` from Lemmas 6.2 and 6.3, the error chain `Σ_{𝒞_*} (u − u_hom)² ≤ 2 P (δ₁ + δ₂) + 2 δ₃` with explicit errors, and its bound by a power of the tile size, `B Λ¹² L⁴ M² K^{−c₀}`. |

The seventeen reports for the declarations of this section are in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Departures from Armstrong and Dario:

- **The homogenized solution is discrete.** `u_hom` is the solution of the discrete Dirichlet problem for the
  constant conductance `σ = ā` on the lattice cube, with the datum built from the coarsened `u` (as in
  [The Dirichlet problem and the excess-decay iteration](#the-dirichlet-problem-and-the-excess-decay-iteration)); AD
  take an `ā`-harmonic function on the continuum cube.
- **Triadic mesoscopic cubes.** The cubes are `z + □_k` with `z ∈ 3^k ℤ²` and `k = ⌈m/8⌉`, the triadic subcubes of
  `□_m`, in place of `z + □_n` with `n = ⌈m/4⌉` of Definition 5.12; Lemma 6.2 then averages the triadic tests over all
  translates.
- **The gradient bound in homogeneous form.** The bound is stated as
  `|□_m|⁻¹ Σ |∇u_hom|² ≤ C M²`, with `M` the normalized `p'`-norm of the open gradient of `u`, which is what
  Lemma 6.4 (iii) and the Dirichlet principle give.

Misprint in the source whose meaning is clear: the display (1.14) at AD18.tex:446 (`e.homogbnd`) prints on the right
side the mean of `|∇u 1_{𝐚≠0}|^p`, which is not homogeneous in `u` while the left side is quadratic.

## Lemma 7.1 and the order-zero regularity in dimension two from Theorem 1

Lemma 7.1 of Armstrong and Dario, the harmonic approximation of the coarsening `[u]_𝒫` on the balls of the
cluster, holds in `d = 2` for `𝔭_c(2) < p < 1` with no hypothesis, and so does the order-zero regularity of
Theorem 2(iii) at `k = 0` ([`planarHarmonicApproximationTwo_holds`, `armstrongDarioOrderZeroTwo_holds`](Rigidity/Proofs/Regularity/PlanarHarmonicApproximationHolds.lean)).
The three estimates on the squares `□_j` of the proof of Lemma 7.1 (the statement `PlanarSquareEstimatesTwo p`, with
`L = 6`) are proved almost surely above one minimal scale `X ≤ O_s(θ)`, from Theorem 1
([Theorem 1 of Armstrong and Dario in dimension two](#theorem-1-of-armstrong-and-dario-in-dimension-two)) and the
minimal scales of Proposition 2.4
([Propositions 5.2 and 5.13, Lemma 5.11 and the minimal scales in dimension two](#propositions-52-and-513-lemma-511-and-the-minimal-scales-in-dimension-two)):
the statements `PlanarMinimalScalesTwo p` and `PlanarHomogenizationErrorTwo p p'` of the files on Lemma 7.1 are the
statements `Rigidity.Proofs.Cluster.PlanarMinimalScales p` and `Rigidity.Dirichlet.PlanarHomogenizationError p p'`
(`planarMinimalScalesTwo_holds`, `planarHomogenizationErrorTwo_holds`).
Theorem 2(iii) at `k = 1` at the origin in dimension two follows from this and from the named hypothesis
`DarioOptimalCorrectorTwo` (Theorem 1 of Dario) alone, since `PlanarCorrectedPlaneExistenceTwo` and
`PlanarOrderOneDimensionTwo` are proved (`armstrongDarioOrderOneOriginTwo_of_dario` and
`armstrongDarioOrderOneOriginTwo_of_darioOptimalCorrector`; see
[Corrected planes, the dimension of the harmonic functions of linear growth and the corrector input in dimension two](#corrected-planes-the-dimension-of-the-harmonic-functions-of-linear-growth-and-the-corrector-input-in-dimension-two)).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Regularity.planarHarmonicDistTwo_of_homogenizationError`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicDistTwo.lean) | AD (7.7) on the planar squares above a minimal scale: the coarsening `[u]_𝒫` is within `C 3^{−jα} Γ_{j+3}` of a lattice harmonic function on `□_j`. The function is `u_hom` of Theorem 1 on `□_{j+1}`; its gradient is bounded by the interior estimate for the lattice Laplacian, the anchors are counted with the sizes at most `(3^{j+1})^{α'/2}`, `α' = min(α, 1)`, and the gradient norm of Theorem 1 is bounded by the Meyers estimate from `□_{j+1}` to `□_{j+2}` and the Caccioppoli inequality on `𝒞_*(□_{j+3})` (`PlanarGradNormBound`, `PlanarHarmonicComparison`, `PlanarHomogenizedGradient`). |
| [`planarCoarseComparisonTwo_of_minimalScales`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarCoarseComparisonTwo.lean), [`coarseComparison_on_square`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarCoarseComparison.lean) | AD (7.8) in the `L²` form on the planar squares above a minimal scale: `3^{−j} ‖u − [u]_𝒫‖_{L²(𝒞_*(□_j))} ≤ K Γ_{j+3}` from Lemma 3.2 with the reach scales, the Hölder inequality, the planar Meyers estimate on the cells of the minimal scales, and the Caccioppoli inequality. |
| [`planarCoarseBoundTwo_of_minimalScales`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarCoarseBoundTwo.lean), [`sum_sq_coarse_sub_mean_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarCoarseBound.lean), [`squareL2_coarse_sub_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarCoarseBound.lean) | the bound of Step 2 of the proof of Lemma 7.1 for a constant `w = a`: the coarsened function minus its mean on `□_j` by the Poincaré inequality, Lemma 3.3 with the pair reach scales, the Meyers and Caccioppoli inequalities; and minus a constant by averaging over the cluster of the square, which carries a fixed proportion of it, with (7.8). |
| [`planarSquareEstimatesTwo_of_parts`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationInputs.lean), [`planarSquareEstimatesTwo_holds`](Rigidity/Proofs/Regularity/PlanarHarmonicApproximationHolds.lean) | the three estimates combined into `PlanarSquareEstimatesTwo p`, with the common minimal scale the maximum of the three, and then with no hypothesis. |
| [`planarHarmonicApproximationTwo_of_inputs`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationInputs.lean), [`planarHarmonicApproximationTwo_holds`](Rigidity/Proofs/Regularity/PlanarHarmonicApproximationHolds.lean) | AD Lemma 7.1 in dimension two, from `PlanarMinimalScalesTwo` and `PlanarHomogenizationErrorTwo` for every supercritical `p`, and then with no hypothesis. |
| [`armstrongDarioOrderZeroTwo_of_inputs`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationInputs.lean), [`armstrongDarioOrderZeroTwo_holds`](Rigidity/Proofs/Regularity/PlanarHarmonicApproximationHolds.lean) | AD Theorem 2(iii) at `k = 0` in dimension two (`ArmstrongDarioOrderZeroTwo`), from the same inputs and then with no hypothesis. |
| [`planarPartitionSizeScale_of_minimalScales`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarPartitionSizeScale.lean) | the partition cubes of the vertices of `□_m` have scale at most `m − 2` above a minimal scale, from the minimal scales of Proposition 2.4 with `t = 1` and `α = 1/2`. |
| [`armstrongDarioOrderOneOriginTwo_of_dario`](Rigidity/Proofs/Regularity/PlanarHarmonicApproximationHolds.lean) | AD Theorem 2(iii) at `k = 1` at the origin in dimension two (`ArmstrongDarioOrderOneOriginTwo`), from `DarioOptimalCorrectorTwo`, `PlanarCorrectedPlaneExistenceTwo` and `PlanarOrderOneDimensionTwo`, by the route of the section on Lemma 7.3 at `k = 2`. |

The sixteen reports for the declarations of this section are in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Departures from Armstrong and Dario: those of the section on order-zero regularity above (the lattice route, with
`Ā` the lattice harmonic functions and the discrete `u_hom` of Theorem 1), and the following.

- **One minimal scale.** The three estimates share the scale `X`, the maximum of the minimal scales of the three
  estimates, in the form `PlanarSquareEstimatesTwo` with `L = 6`.
- **The `L²` form of (7.8).** The comparison of `u` with `[u]_𝒫` is proved in `L²`, in place of the exponent `p'`
  of the source.

Misprint in the source whose meaning is clear: AD18.tex:5137-5146 (the squares of (7.2)), as noted in the section on
order-zero regularity above.

## Order-zero regularity in every dimension

Lemma 7.1 of Armstrong and Dario for the partition into good cubes, and with it Theorem 2(iii) at
`k = 0`, are proved in every dimension `d ≥ 2` in Percolation-Cluster-Homogenization, from Theorem 1
of Armstrong and Dario in every dimension, by the route of the planar proof of
[Lemma 7.1 and the order-zero regularity in dimension two from Theorem 1](#lemma-71-and-the-order-zero-regularity-in-dimension-two-from-theorem-1)
(see its correspondence, section "Lemma 7.1 and the order-zero regularity in every dimension from
Theorem 1"). The input `LatticeProb.External.ArmstrongDarioOrderZero` is therefore proved, and the
theorems below restate those of `Rigidity.Assembly.Main` and `Rigidity.Assembly.WithProvedDensity`
that take it, without it.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/GeneralOrderZeroHolds.lean) | `ArmstrongDarioOrderZero` with no hypothesis: for `d ≥ 2` and `𝔭_c(d) < p < 1`, the infinite cluster is unique, `𝒜₀(𝒞_∞)` is one-dimensional, and harmonic functions in large balls at the origin are close to constants above a minimal scale with stretched exponential moments (AD, Theorem 2(iii) at `k = 0`). |
| [`Rigidity.Assembly.WithProvedOrderZero`](Rigidity/Proofs/Assembly/ProvedOrderZero.lean): `lipschitz`, `fastDecay`, `notLipschitz`, `nonConstantOnGadget`, `fastDecayDichotomy`, `fastDecayPotential`, `gradientTrichotomy`, `levelSetDensity`, `goodEventLowerBound`, `largeGradientSensitive`, `goodEventLowerBoundDirectional` | the eleven theorems of `Rigidity.Assembly.Main` with the hypothesis `ArmstrongDarioOrderZero`, with the same statements and the other hypotheses. |
| [`Rigidity.Assembly.WithProvedOrderZero.fastDecayWithProvedDensity`](Rigidity/Proofs/Assembly/ProvedOrderZero.lean) | Theorem 1.3, with the hypotheses `SupercriticalBondCorrectorInput`, `CorrectorQuantitativeInput`, `ArmstrongDarioOrderOneOrigin`, `SupercriticalBondGreenColumnExistence` and `SupercriticalBondGreenQuantitative`. |

The thirteen declarations depend on exactly `propext`, `Classical.choice` and `Quot.sound`.

## Regularity of order one at the origin from the mesoscopic estimate

`Rigidity.External.ArmstrongDarioOrderOneOrigin` (Theorem 2.4, part (iii) at `k = 1`; AD Theorem 2(iii)
at `k = 1`) is a theorem from the existence of the corrected planes alone, the first part of
`LatticeProb.External.SupercriticalBondCorrectorInput`
([`armstrongDarioOrderOneOrigin_of_supercriticalBondCorrectorInput`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/CorrectorSublinearFromRegularity.lean)).
It was first proved from
[`ArmstrongDarioMesoscopicDegreeTwo`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/OrderOneOrigin.lean), AD Lemma 7.3, display (7.18) at `k = 2`
for bond percolation at the origin, with `Ā₂` the harmonic quadratic polynomials and the normalization
`r^{−d/2} ‖·‖_{L²(𝒞_∞ ∩ B_r)}`, together with `Rigidity.External.CorrectorQuantitativeInput` and
`LatticeProb.External.SupercriticalBondCorrectorInput` (the table below). The mesoscopic estimate is proved
in every dimension in Percolation-Cluster-Homogenization from Lemma 7.1 for the partition into good cubes
([`armstrongDarioMesoscopicDegreeTwo_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/GeneralMesoscopicDegreeTwo.lean)). For a corrected
plane `u` of slope `q`, letting `R → ∞` in (7.18) bounds its excess over `Ā₂` on `B_r` by `C |q| r^{1−δ}`, and
the telescoping of the near-best harmonic quadratic polynomials on the balls `B_{2^k 𝒳}` gives the
sublinearity (1.18) of AD with a minimal scale of class `O_s`
([`correctorSublinearL2At_of_correctedPlanes`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/CorrectorSublinearFromRegularity.lean)); (1.18) replaces
`CorrectorQuantitativeInput` in the lifts of the affine functions. In
dimension two it is proved from the estimates on squares of Lemma 7.1, which are proved in [Lemma 7.1 and the order-zero regularity in dimension two from Theorem 1](#lemma-71-and-the-order-zero-regularity-in-dimension-two-from-theorem-1) (see
[Lemma 7.3 at k = 2 and regularity of order one at the origin in dimension two](#lemma-73-at-k--2-and-regularity-of-order-one-at-the-origin-in-dimension-two)).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_of_supercriticalBondCorrectorInput`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/CorrectorSublinearFromRegularity.lean) | `ArmstrongDarioOrderOneOrigin` from the existence of the corrected planes, the first part of `SupercriticalBondCorrectorInput`. |
| [`Rigidity.Proofs.Regularity.correctorSublinearL2At_of_correctedPlanes`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/CorrectorSublinearFromRegularity.lean) | for `d ≥ 2` and `𝔭_c(d) < p < 1`, from the existence of the corrected planes: almost surely every slope `q` has a harmonic function `u` of linear growth with `‖u − q · x‖_{L̲²(𝒞_∞ ∩ B_r)} ≤ K |q|₁ r^{1−δ}` for `r ≥ 𝒳`, `𝒳` of class `O_s` (AD (1.18)). |
| [`Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_of_correctorSublinear`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/OrderOneOriginSublinear.lean) | `ArmstrongDarioOrderOneOrigin` from (1.18) with a minimal scale of class `O_s`. |
| [`Rigidity.Proofs.Regularity.armstrongDarioMesoscopicDegreeTwo_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/GeneralMesoscopicDegreeTwo.lean) | `ArmstrongDarioMesoscopicDegreeTwo` with no hypothesis: (7.18) at `k = 2` in every dimension `d ≥ 2`. |
| [`Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_of_mesoscopicDegreeTwo`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/OrderOneOrigin.lean) | `ArmstrongDarioOrderOneOrigin` from `ArmstrongDarioMesoscopicDegreeTwo`, `CorrectorQuantitativeInput` and `SupercriticalBondCorrectorInput`. |
| [`Rigidity.Proofs.Regularity.ballExcess_le_of_clusterBallVolumeL2`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/OrderOneOrigin.lean) | the change of normalization from `r^{−d/2} ‖·‖_{L²}` to the ball excess, under the volume comparison `K` of the cluster balls, with the constant multiplied by `√K`. |
| [`Rigidity.Proofs.Regularity.orderOneEndpointData_cluster`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/ClusterOrderOne.lean), [`clusterLiftMap_mem_harmonicGrowthSpace`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/ClusterOrderOne.lean) | the hypotheses of the endpoint iteration on the cluster: the lifts of the affine functions by the corrected planes, with relative error `C t^{−1/2}` on `B_t` (absolute error `C t^{1/2}`), the trace-free quadratic polynomials, and the comparison of sizes from the density of the infinite cluster in cubes. |
| [`Rigidity.Proofs.Regularity.weighted_endpoint_step`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/OrderOneEndpoint.lean), [`orderOneEndpoint_step`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/OrderOneEndpoint.lean), [`orderOneEndpoint_iterate`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/OrderOneEndpoint.lean), [`orderOneEndpoint_fit`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/OrderOneEndpoint.lean), [`exists_forall_le_of_orderOneEndpoint`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/OrderOneEndpoint.lean) | the endpoint iteration for abstract data: one step at the endpoint of the scale range, the product of the step factors bounded by `exp(c r^{−δ}/(1 − θ^δ))`, the fit `N_t(u − Lℓ₀) ≤ C (t/R)² N_R(u)` at each radius `t ∈ [𝒳, R/2]`, and one lifted affine function `Lℓ` for all such radii. |

`ArmstrongDarioMesoscopicDegreeTwo` is a definition of a proposition, not an axiom. The thirteen theorems of the
table and the definition, which have axiom reports in [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean),
depend only on `propext`, `Classical.choice` and `Quot.sound`.

Departures from Armstrong and Dario:

- **The deduction of Theorem 2(iii).** AD deduce Theorem 2 from Lemma 7.3 through Proposition 3.1 of
  Armstrong, Kuusi and Mourrat, which lifts the polynomials of degree two. Here an endpoint iteration is
  used, which lifts only the affine functions, and the quadratic coefficient stays an ordinary trace-free
  quadratic polynomial; the case `k = 0` (order zero) is not used.
- **The lifts.** The affine functions are lifted by the corrected planes of slope `e_i` normalized at a vertex
  `a_0` of the cluster in `B_{X−1}` (`SupercriticalBondCorrectorInput`), with the error
  `|g_i − x_i| ≤ C t^{1/2}` from `CorrectorQuantitativeInput`, with the edge `(a_0, a_1)` in `B_X`.
  The literature proof of `CorrectorQuantitativeInput` (DG, Proposition 2.12) rests on the regularity theory of
  AD, so this route cannot later serve as a proof of that input.
- **(1.18) from (7.18).** AD obtain (1.18) by the construction of the corrected planes of Armstrong, Kuusi and
  Mourrat, Proposition 3.1, from Theorem 1 with the minimal scale of the flatness (5.33). Here (1.18) is derived
  from (7.18) at `k = 2` and the existence of the corrected planes, with the minimal scale of (7.18) and of the
  density of the cluster in cubes; this route uses neither `CorrectorQuantitativeInput` nor the uniqueness part
  of `SupercriticalBondCorrectorInput`.
- **Normalization.** The statement (7.18) is used with `|B_r| = r^d`; the Lebesgue measure
  `ω_d r^d` gives the same statement, and `Ā₂` is the space of the trace-free quadratic polynomials, as the
  homogenized matrix is a multiple of the identity.
- **The random scale.** `X = c_0 max(X_{(7.18)}, M_cube, M_corr(0), 1)` with `c_0` deterministic, and the
  exponent `s` is the minimum of the three exponents.

## Order-zero regularity and the planar corrector input from Lemma 7.1

Two reductions of the planar inputs are proved in
[`PercolationClusterHomogenization/Proofs/Regularity/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Regularity/), together with deterministic steps of the proof of
AD Lemma 7.1 in dimension two. Lemma 7.1 itself, with the estimates on squares
(`PlanarSquareEstimatesTwo`), is proved in [Lemma 7.1 and the order-zero regularity in dimension two from Theorem 1](#lemma-71-and-the-order-zero-regularity-in-dimension-two-from-theorem-1). The bound on the
scales of the partition cubes (`PlanarPartitionSizeScale`) follows from the minimal scales of Proposition 2.4
(`planarPartitionSizeScale_of_partCubeMoments`, see
[Lemma 7.3 at k = 2 and regularity of order one at the origin in dimension two](#lemma-73-at-k--2-and-regularity-of-order-one-at-the-origin-in-dimension-two)).

* **R3 in dimension two** (`ArmstrongDarioOrderZeroTwo`, AD Theorem 2(iii) at `k = 0`) from
  `PlanarHarmonicApproximationTwo`, the statement of Lemma 7.1: for `𝔭_c(2) < p < 1` there are `s, θ, A, α, K`
  and a measurable scale `X ≥ 1` with `X ≤ O_s(θ)` such that almost surely, for every `R` with `A X ≤ R` and
  every `u` harmonic on `𝒞_∞ ∩ B_R`, the coarsening `[u]_𝒫(x) = u(anchor of the planar partition cube of x)`
  satisfies the harmonic approximation against the lattice harmonic functions on the balls of `ℤ²`, and its
  `L²` comparison with `u` and with constants holds on the balls.
* **`PlanarHarmonicApproximationTwo` from the estimates on squares.**
  `planarHarmonicApproximationTwo_of_squareEstimates` derives it from `PlanarSquareEstimatesTwo p` (the
  estimate (7.7), the `L²` form of (7.8) and the bound of Step 2 for constant `w`, on the squares `□_j` above a
  minimal scale `X ≤ O_s(θ)`, for the functions harmonic on balls of `𝒞_∞`) and `PlanarPartitionSizeScale p`
  (the partition cubes of the vertices of `□_m` have scale at most `m − 2` above a minimal scale
  `M ≤ O_s(θ)`). Both are proved for `𝔭_c(2) < p < 1` (see the sections on Lemma 7.1 and on Lemma 7.3 at `k = 2`).
* **R2 in dimension two** (`SupercriticalBondCorrectorInputTwo`) from `ArmstrongDarioOrderZeroTwo`,
  `PlanarCorrectedPlaneExistenceTwo` (every slope has a corrected plane on the planar infinite cluster, AD
  Theorem 2(ii) at `k = 1`, with the sublinearity in the uniform norm of the remark after (1.19), AD18.tex:527-562,
  whose conclusion is (1.22)) and `PlanarOrderOneDimensionTwo` (`dim 𝒜₁ ≤ 3`, AD Theorem 2(i) at `k = 1`).
  The last two are proved for `𝔭_c(2) < 𝔭 < 1`, so `supercriticalBondCorrectorInputTwo_holds` is R2 in dimension two
  with no hypothesis (see
  [Corrected planes, the dimension of the harmonic functions of linear growth and the corrector input in dimension two](#corrected-planes-the-dimension-of-the-harmonic-functions-of-linear-growth-and-the-corrector-input-in-dimension-two)).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_of_planarHarmonicApproximation`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarOrderZeroInput.lean) | `PlanarHarmonicApproximationTwo → ArmstrongDarioOrderZeroTwo`; the other inputs it uses (the density of the infinite cluster in cubes and its concentration) are proved. |
| [`exists_planarOrderZeroDecay`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarOrderZero.lean), [`le_of_geometric_step`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarOrderZero.lean) | the Campanato iteration on the lattice balls of `𝒞_∞` that turns the harmonic approximation into the decay of the oscillation of `u`, and its elementary step. |
| [`planarHarmonicApproximationTwo_of_squareEstimates`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationTwo.lean), [`planarHarmonicApproximationAt_of_squareEstimates`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationSquares.lean), [`harmonicApproximation_of_squares`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicApproximationBalls.lean) | Lemma 7.1 in dimension two from the estimates on the squares `□_j`, by the iteration of Step 4 (`le_sum_squareIterCoeff`) and the comparison of the norms on squares and on lattice balls (`componentBallL2_le_squareL2`, `squareL2_le_componentBallL2`). |
| [`mem_clusterVertices_succ`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarClusterInclusions.lean), [`mem_supp_of_mem_clusterVertices`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarClusterInclusions.lean) | the inclusions of the clusters used in the proof: `𝒞_*(□_j) ⊆ 𝒞_∞` for a resolved square meeting `𝒞_∞`, and `𝒞_∞ ∩ □_m ⊆ 𝒞_*(□_{m+1})` when the partition scales on `□_m` are at most `m − 2`. |
| [`clusterRestrictTo_mem_clusterHarmonic`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarClusterRestriction.lean), [`clusterForm_clusterRestrictTo_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarClusterRestriction.lean) | the restriction of a function harmonic on `𝒞_∞` to `𝒞_*(V)`, for a resolved `V` with `𝒞_*(V) ⊆ 𝒞_∞`, is harmonic there, and the Caccioppoli inequality from `□_{n+1}` to `□_n` for it. |
| [`supercriticalBondCorrectorInputTwo_of_orderOne`](Rigidity/Proofs/Regularity/PlanarCorrectorReduction.lean), [`eq_zero_of_slopeAsymptotics_zero`](Rigidity/Proofs/Regularity/PlanarCorrectorReduction.lean) | `ArmstrongDarioOrderZeroTwo → PlanarCorrectedPlaneExistenceTwo → PlanarOrderOneDimensionTwo → SupercriticalBondCorrectorInputTwo`, with the fact that on a cluster with the cap density the zero function determines its slope. |

The nineteen reports for the declarations of this section are in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Departures from Armstrong and Dario:

- **The lattice route.** `Ā` is the space of the lattice harmonic functions on the balls of `ℤ²` (the discrete
  `u_hom` of the Dirichlet problem section, with `ā = σ I`), not the continuum `ā`-harmonic functions; the
  coarsening `[u]_𝒫(x)` is `u` at the anchor of the planar partition cube of `x`, with `u` extended by `0` off the
  cluster.
- **Order zero.** `ArmstrongDarioOrderZeroTwo` is obtained from the lattice form of Lemma 7.2 at `k = 0` by a
  Campanato iteration, and the transfer from `[u]_𝒫` to `u` by the iteration over the radii `A^k s`.

Misprint in the source whose meaning is clear: in the iteration of Step 4 of the proof of Lemma 7.1
(AD18.tex:5292-5316) the squares are `□_{m+3(k+1)}`, with the factor `3^{−k(m + 3(k+1)/2)}`, where
AD18.tex:5137-5146 prints `□_{m+3k}`. It does not affect Lemma 7.3.

## Lemma 7.3 at k = 2 and regularity of order one at the origin in dimension two

AD Lemma 7.3, display (7.18) at `k = 2`, is proved for planar bond percolation
(`ArmstrongDarioMesoscopicDegreeTwoPlanar`, the planar case of `ArmstrongDarioMesoscopicDegreeTwo`) from the
estimates on squares of the proof of Lemma 7.1 (`PlanarSquareEstimatesTwo`). With it,
`Rigidity.External.ArmstrongDarioOrderOneOriginTwo` (AD Theorem 2(iii) at `k = 1`, at the origin, in the plane)
is proved from `PlanarSquareEstimatesTwo`, Theorem 1 of Dario in dimension two (`DarioOptimalCorrectorTwo`),
`PlanarCorrectedPlaneExistenceTwo` and `PlanarOrderOneDimensionTwo`; the estimates on squares are proved
in [Lemma 7.1 and the order-zero regularity in dimension two from Theorem 1](#lemma-71-and-the-order-zero-regularity-in-dimension-two-from-theorem-1), and the last two in
[Corrected planes, the dimension of the harmonic functions of linear growth and the corrector input in dimension two](#corrected-planes-the-dimension-of-the-harmonic-functions-of-linear-growth-and-the-corrector-input-in-dimension-two),
so that only `DarioOptimalCorrectorTwo` is a hypothesis (`armstrongDarioOrderOneOriginTwo_of_dario`,
`armstrongDarioOrderOneOriginTwo_of_darioOptimalCorrector`). The other inputs are proved: the minimal
scales of AD Proposition 2.4 (`Rigidity.Proofs.Cluster.planarMinimalScales_holds`), which also give the
hypothesis `PlanarPartitionSizeScale` of Lemma 7.1, and the density of the infinite cluster in cubes.

The proof follows AD on the lattice. Lemma 7.2 at `k = 2` is applied to the coarsening `[u]_𝒫` on the balls of
`ℤ²`, with the lattice harmonic functions as `Ā`, the lattice harmonic quadratic functions as `Ā₂` and the
lattice harmonic cubic polynomials as `Ā₃`, up to the top scale `T = R/(8A)`; the excesses of `[u]_𝒫` are then
transferred to `u` on the cluster balls (Steps 1 and 2 of the proof of Lemma 7.3, (7.21)–(7.23)).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Regularity.armstrongDarioOrderOneOriginTwo_of_squareEstimates`](Rigidity/Proofs/Regularity/PlanarOrderOneOriginInputs.lean) | `ArmstrongDarioOrderOneOriginTwo` from `PlanarSquareEstimatesTwo`, `DarioOptimalCorrectorTwo`, `PlanarCorrectedPlaneExistenceTwo` and `PlanarOrderOneDimensionTwo`. |
| [`armstrongDarioMesoscopicDegreeTwoPlanar_of_squareEstimates`](Rigidity/Proofs/Regularity/PlanarOrderOneOriginInputs.lean), [`planarHarmonicApproximationTwo_of_squareEstimates_holds`](Rigidity/Proofs/Regularity/PlanarOrderOneOriginInputs.lean) | (7.18) at `k = 2` in the plane, and `PlanarHarmonicApproximationTwo`, from `PlanarSquareEstimatesTwo` alone. |
| [`planarPartCubeMoments_holds`](Rigidity/Proofs/Regularity/PlanarOrderOneOriginInputs.lean), [`planarPartitionSizeScale_of_partCubeMoments`](Rigidity/Proofs/Regularity/PlanarOrderOneOriginInputs.lean), [`planarCoarseHarmonicApproximationTwo_iff`](Rigidity/Proofs/Regularity/PlanarOrderOneOriginInputs.lean) | the moments and the maxima of the sizes of the planar partition cubes on `□_m` above a minimal scale (part of Proposition 2.4), the bound `PlanarPartitionSizeScale` on their scales (with `t = 1`, `α = 1/2`, above `max(M, 81)`), and the identity of the two statements of Lemma 7.1 in dimension two. |
| [`mesoscopicDegreeTwoAt_of_inputs`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicDegreeTwo.lean), [`armstrongDarioMesoscopicDegreeTwoPlanar_of_inputs`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicDegreeTwo.lean), [`armstrongDarioOrderOneOriginTwo_of_inputs`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicDegreeTwo.lean) | (7.18) at `k = 2` almost surely, for one law and for every supercritical law, from Lemma 7.1 (`PlanarCoarseHarmonicApproximationTwo`) and the minimal scales of the partition cubes (`PlanarPartCubeMoments`), with `δ = α/2`; and Theorem 2(iii) at `k = 1` in the plane with the planar corrector inputs. |
| [`mesoscopicDegreeTwo_core`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicTwoMain.lean) | (7.18) at `k = 2` for one configuration, on `[r₀X, R/2]`, from Lemma 7.1 in the form of the proof of Lemma 7.3, partition cubes of side at most `c R^{α/2}` in `B_R` whose sizes have moments of orders one and two at most `K R²`, and the density of the cluster in cubes. |
| [`coarse_top_bounds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicTwoTopBounds.lean), [`harmonicApproximation_error_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarMesoscopicTwoTopBounds.lean) | the excesses of `[u]_𝒫` over the lattice harmonic quadratic functions and over the constants at the top scale `T` bounded by the cluster excesses of `u` on `B_R` and the harmonic-approximation error at `4T`; that error bounded through the crude bound of the coarse oscillation at `R/2`. |
| [`armstrongDario_lemma_7_2_two_latticeHarmonic`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/LatticeKIterationTwo.lean), [`armstrongDario_lemma_7_3_two_latticeHarmonic`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/LatticeKIterationTwo.lean) | AD Lemma 7.2 at `k = 2` and its iteration for the harmonic functions on the balls of `ℤ²`, from the harmonic-approximation hypothesis alone. |
| [`harmonicRegularity_three_latticeHarmonicClass`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/LatticeHarmonicExcessThree.lean), [`polynomialComparison_latticeHarmonicCubic`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/LatticeCubicComparison.lean) | the excess decay of order three of the harmonic functions on the balls of `ℤ²` (harmonic third-order expansion at a corner and fourth differences), and the comparison of the excesses of the lattice harmonic cubic polynomials over the harmonic quadratic functions on two balls (third differences). |
| [`componentBallL2_le_sum_abs_of_latticeHarmonic`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/LatticeHarmonicMeanValue.lean) | the `ℓ^∞`–`ℓ¹` bound `‖g‖_{L̲²(B_ρ)} ≤ C ρ^{−2} Σ_{B_{4ρ}} \|g\|` for `g` lattice harmonic on `B_{4ρ}`, by an absorption over boxes. |
| [`orderOneOrigin_of_mesoscopicDegreeTwoAt`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/OrderOneOriginTwo.lean), [`armstrongDarioOrderOneOriginTwo_of_mesoscopicDegreeTwoPlanar`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/OrderOneOriginTwo.lean) | the reduction of Theorem 2(iii) at `k = 1` to (7.18) at `k = 2` for one dimension and one law, and its planar case. |
| [`armstrongDario_lemma_7_2_two_planar`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicRegularityThree.lean), [`armstrongDario_lemma_7_3_two_planar`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarHarmonicRegularityThree.lean) | AD Lemma 7.2 at `k = 2` and its iteration in the plane for the continuum norms, with the harmonic cubic polynomials as `Ā₃`. |

The twenty-one reports for the declarations of this section are in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean); they depend only on `propext`, `Classical.choice` and
`Quot.sound`.

Departures from Armstrong and Dario:

- **The lattice route.** As for Lemma 7.1, `Ā` is the space of the lattice harmonic functions on the balls of
  `ℤ²`, and `Ā₃` is the space of the lattice harmonic cubic polynomials. The passage from the `L²` excess of
  `[u]_𝒫` to its `L¹` excess (the display after (7.19), from (7.11)) uses the `ℓ^∞`–`ℓ¹` bound of lattice
  harmonic functions.
- **The exponent.** `δ = α′/2` with `α′ = min(α, 1)` and `α` the exponent of Lemma 7.1; the
  harmonic-approximation hypothesis for `α` implies it for `α′` above the scale `1`.
- **The order of the steps.** The Lipschitz bound `D̃_0(s) ≤ C s R^{−1} D̃_0(R)` (the case `k = 0` of the same
  argument) is proved first, by an induction over the scales `s, As, A²s, …`; it bounds the coarsening error
  `K s^{−1} D̃_0(As)` of (7.8) in Step 1, for `k = 0` and `k = 2`.
- **The random scale.** `X = c₀ max(X_{L7.1}, M₁, M₂, M_cube)` with `c₀` deterministic, `M₁`, `M₂` the minimal
  scales of the moments of orders one and two of the sizes of the partition cubes with the exponent `α′/2`, and
  `M_cube` the scale of the density of the cluster in cubes.

A step of the source is repaired. After (7.19), AD18.tex:5525-5528 states
`D_k(cR) ≤ C inf_w ‖[u]_𝒫 − w‖_{L̲¹(B_{cR})}` "using (7.11)"; but (7.11) has a second term, the
harmonic-approximation error `inf_v ‖[u]_𝒫 − v‖_{L̲²}` at the top scale, which is dropped. By (7.2) that error
contains `sup_{s ∈ [Ac′R, R]} D_0([u]_𝒫; s)/s`, and the term `D_0(cR)/(cR)` of (7.19) and (7.20) is not bounded
by `D̃_0(R)/R` in Step 3 either. Here the coarse oscillations at the top scales are bounded crudely through the
largest partition cube in `B_R`, of side at most `c R^{α′/2}` above the minimal scale
(`harmonicApproximation_error_le`); the loss `R^{α′/2}` is absorbed by the factor `(4T)^{−α′}` of the
harmonic-approximation error, which leaves `δ = α′/2` in (7.18).

## Corrected planes, the dimension of the harmonic functions of linear growth and the corrector input in dimension two

For `𝔭_c(2) < 𝔭 < 1` the qualitative corrector input `SupercriticalBondCorrectorInputTwo` (R2) is proved with no further
hypothesis, in [`PercolationClusterHomogenization/Proofs/Regularity/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Regularity/), by the route of Armstrong, Kuusi and
Mourrat (arXiv:1602.00512, called AKM2 here, numbered as in that paper), Proposition 3.1, Steps 3 and 4, which AD18.tex:5658
cites for Theorem 2 (i)–(iii) at `k = 1`.

* **The corrected planes** (`PlanarCorrectedPlaneExistenceTwo`, AD Theorem 2 (ii) at `k = 1`, with the sublinearity in the
  uniform norm of the remark after (1.19), AD18.tex:527-562). From the approximation of affine functions on the balls
  `B_{3^m}` of the cluster by harmonic functions `u_m` with `‖u_m − q·x‖ ≤ K |q|₁ 3^{m(1−δ)}`
  (`PlanarAffineApproximationAeTwo`), the corrector of the slope `q` is the diagonal limit of the `u_m`, by the telescoping
  bound and the Lipschitz estimate at the origin of the order-zero regularity (`exists_harmonic_of_approximations`, Step 3 of
  AKM2 Proposition 3.1). This gives (1.18), `|χ_q|` in `L̲²(𝒞_∞ ∩ B_r)` at most `C |q| r^{1−δ}` above a scale, with the scale
  almost surely finite (`PlanarCorrectorSublinearL2AeTwo`), and then the bound in the uniform norm
  (`abs_corrector_le_at_scale`, `componentSlopeAsymptotics_of_scales`).
* **The approximation of affine functions** (`planarAffineApproximationAeTwo_of_minimalScales`) by the maximizers of `ν`:
  `u_m = q₀ v(·, □_{j+3}, e₀) + q₁ v(·, □_{j+3}, e₁) − c` on `B_{3^{j+1}}`, with the bound on the energy of `ν`
  (`clusterForm_planarNuSolution_le`, `ν ≤ (9/4)|ξ|₁²`), the coarsening errors by Lemma 3.2 with reach scales at most the
  scale `D` (`sum_sq_extend_sub_coarsen_le`), the flatness of the combination (`sum_sq_coarsen_combo_le`), and (5.33)
  (AD18.tex:3413), proved from Lemmas 5.5 and 5.8, in expectation, with the geometric decay of `τ_n` from Lemma 5.10; all are
  proved in the sections on those lemmas above.
* **`dim 𝒜₁ ≤ 3`** (`planarOrderOneDimensionTwo_of_mesoscopic`, AD Theorem 2 (i) at `k = 1`), from (7.18) at `k = 2` of
  Lemma 7.3 (AD18.tex:5490-5497), the density of the cluster in cubes and the existence of the corrected planes: for one
  configuration, every `u ∈ 𝒜₁` is `a + Σᵢ ξᵢ gᵢ` for the corrected planes `gᵢ` of slopes `eᵢ`
  (`eq_clusterLiftMap_of_orderOne`, Step 4 of AKM2 Proposition 3.1), so `𝒜₁` lies in the range of a linear map from
  `ℝ × ℝ²`.
* **The inputs are discharged in dimension two** (`Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean`). The statement
  `MesoscopicDegreeTwoPlanarInput` used for the dimension is `ArmstrongDarioMesoscopicDegreeTwoPlanar` (by `Iff.rfl`,
  `mesoscopicDegreeTwoPlanarInput_iff`), and (7.18) at `k = 2` follows from the estimates on squares
  (`mesoscopicDegreeTwoPlanarInput_holds`, from `planarSquareEstimatesTwo_holds`); the minimal scales are
  `planarMinimalScalesTwo_holds` and the order-zero regularity `armstrongDarioOrderZeroTwo_holds`. Hence
  `planarCorrectedPlaneExistenceTwo_holds`, `planarOrderOneDimensionTwo_holds`, R2 `supercriticalBondCorrectorInputTwo_holds`,
  R6 `supercriticalBondGreenColumnExistenceTwo_holds` (by `supercriticalBondGreenColumnExistenceTwo_of_correctorInput`), and
  R4 `armstrongDarioOrderOneOriginTwo_of_darioOptimalCorrector` from `DarioOptimalCorrectorTwo` alone. There is no circularity: (7.18)
  at `k = 2` uses the estimates on squares, not the corrector estimate.
  `darioOptimalCorrectorTwo_of_oscillation` is Theorem 1 of Dario with R2 and R3 discharged.

| Lean declaration | Statement |
| --- | --- |
| [`exists_planar_all_centres_constant_approximation`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorL2.lean), [`ae_eventually_scale_le_three`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarScaleMaxima.lean) | the order-zero approximation by constants at every centre of the ball, and the almost sure bound of the minimal scales over the triadic boxes at all large scales. |
| [`abs_corrector_le_at_scale`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorSupNorm.lean), [`componentSlopeAsymptotics_of_scales`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorSupNorm.lean), [`planarCorrectedPlaneExistenceTwo_of_sublinearL2`](Rigidity/Proofs/Regularity/PlanarCorrectedPlaneExistence.lean), [`supercriticalBondCorrectorInputTwo_of_sublinearL2`](Rigidity/Proofs/Regularity/PlanarCorrectedPlaneExistence.lean) | the corrector bounded uniformly on a box by powers of the minimal scale, from (1.18) and the Lipschitz estimate; the sublinearity in the uniform norm; the corrected planes and R2 from (1.18) with an almost surely finite scale. |
| [`exists_harmonic_of_approximations`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorConstruction.lean), [`planarCorrectorSublinearL2Two_of_affineApproximation`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorFromApproximation.lean), [`planarCorrectedPlaneExistenceTwo_of_affineApproximation`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorFromApproximation.lean), [`planarCorrectedPlaneExistenceTwo_of_affineApproximationAe`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorFromApproximation.lean) | Step 3 of AKM2 Proposition 3.1: the harmonic function on the cluster from approximations on growing balls, (1.18), and the corrected planes. |
| [`clusterForm_planarNuSolution_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarNuEnergy.lean), [`sum_sq_extend_sub_coarsen_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarNuEnergy.lean), [`sum_sq_coarsen_combo_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarNuEnergy.lean), [`affineApproximation_at_scale`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarAffineApproximationNu.lean), [`radicand_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarAffineApproximationNu.lean) | the energy of the maximizers of `ν` and of their combinations, their coarsening errors, and the approximation of affine functions at one scale. |
| [`ae_eventually_planarNuFlatness_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarNuFlatnessAS.lean), [`planarAffineApproximationAeTwo_of_nuFlatness`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarAffineApproximationNu.lean), [`planarCorrectedPlaneExistenceTwo_of_nuFlatness`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarAffineApproximationNu.lean), [`planarAffineApproximationAeTwo_of_minimalScales`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarAffineApproximationHolds.lean), [`planarCorrectedPlaneExistenceTwo_of_minimalScales`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarAffineApproximationHolds.lean) | the Markov inequality and the Borel–Cantelli lemma for the flatness (5.33) in expectation, giving an almost sure bound at all large scales; the approximation of affine functions with an almost surely finite scale; the corrected planes from the minimal scales and the order-zero regularity. |
| [`eq_clusterLiftMap_of_orderOne`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/OrderOneLift.lean), [`planarOrderOneDimensionTwo_of_mesoscopic`](Rigidity/Proofs/Regularity/PlanarOrderOneDimension.lean), [`planarOrderOneDimensionTwo_of_minimalScales`](Rigidity/Proofs/Regularity/PlanarOrderOneDimension.lean), [`supercriticalBondCorrectorInputTwo_of_mesoscopic`](Rigidity/Proofs/Regularity/PlanarOrderOneDimension.lean) | Step 4: every element of `𝒜₁` is a constant plus a combination of corrected planes; `dim 𝒜₁ ≤ 3`; R2 from (7.18) at `k = 2`, the minimal scales and the order-zero regularity. |
| [`mesoscopicDegreeTwoPlanarInput_iff`](Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean), [`mesoscopicDegreeTwoPlanarInput_holds`](Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean), [`planarCorrectedPlaneExistenceTwo_holds`](Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean), [`planarOrderOneDimensionTwo_holds`](Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean), [`supercriticalBondCorrectorInputTwo_holds`](Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean), [`supercriticalBondGreenColumnExistenceTwo_holds`](Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean), [`armstrongDarioOrderOneOriginTwo_of_darioOptimalCorrector`](Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean), [`darioOptimalCorrectorTwo_of_oscillation`](Rigidity/Proofs/Regularity/PlanarCorrectorHolds.lean) | (7.18) at `k = 2`, the corrected planes, `dim 𝒜₁ ≤ 3`, R2 and R6 in dimension two with no hypothesis beyond `𝔭_c(2) < 𝔭 < 1`; R4 from `DarioOptimalCorrectorTwo` alone; Theorem 1 of Dario from the multiscale Poincaré inequality, the concentration inequality, (1.22) and Lemma 3.3. |

The thirty-two reports for the declarations of this section are in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Departures from Armstrong and Dario and from Armstrong, Kuusi and Mourrat:

- **The scale of (1.18) is almost surely finite, not `O_s`.** The flatness (5.33) is proved in expectation only. The Markov
  inequality gives `P[Φ_n ≥ (|ξ|² + 1) 9ⁿ μⁿ] ≤ C B (n + 1) μⁿ` with `μ = μ₁^{1/2}`
  (`ae_eventually_planarNuFlatness_le`), a scale with a polynomial tail, and the Borel–Cantelli lemma over
  the scales (with `τ_n ≤ K l^n`) gives a scale that is almost surely finite. This is enough for the qualitative statements
  (corrected planes, sublinearity in the uniform norm, `dim 𝒜₁ ≤ 3`) but not for the quantitative statements (1.18) and (1.22)
  with `O_s` scales. These are proved by a second route, with Lemma 5.5 and the subadditivity defect in place of `τ_k`, in
  [The quantitative sublinearity of the correctors in dimension two](#the-quantitative-sublinearity-of-the-correctors-in-dimension-two).
- **Step 4 of AKM2 Proposition 3.1 without orthogonality.** AKM2 uses the orthogonality of the `ā`-harmonic monomials to
  lift `𝒜₁`. Here the endpoint iteration of the order-one regularity gives, for each radius `R`, one lifted affine function
  `ℓ_R` with error `C (t/R)² ‖u‖_R = o(1)` for `u ∈ 𝒜₁`; the sizes of `ℓ_R` are bounded, and a limit point `ℓ` gives
  `u = Lℓ`. Only the qualitative statement that each `eᵢ` has a corrected plane is used, so the scale is almost surely finite.
- **Step 3 of AKM2 Proposition 3.1 and the remark after (1.19).** The Lipschitz estimate is used in the form of the order-zero regularity (`k = 0`) at the
  centre, Borel–Cantelli over the triadic boxes replaces the stochastic integrability, and the sublinearity in the uniform
  norm uses a staircase interpolation on `x + [0, t]²`.
- **The lattice route.** The harmonic functions in the approximation are on the balls of the cluster, and the approximation
  uses the maximizers of `ν` on `□_{j+3}` (AD Lemma 5.8 (5.33) and Lemma 5.10 in place of the energy of the continuum
  corrector), with reach at most `3^{(j+3)/4}` from the minimal scales with `α = 1/4`.

## The quantitative sublinearity of the correctors in dimension two

For `𝔭_c(2) < 𝔭 < 1` the bound (1.18) of Armstrong and Dario (`PlanarCorrectorSublinearL2Two`) and the quantitative
sublinearity (1.22) in the oscillation form (`PlanarCorrectorOscSublinearTwo`, which is the statement
`CorrectorOscSublinearTwo` of [Theorem 1 of Dario in dimension two](#theorem-1-of-dario-in-dimension-two) by `Iff.rfl`,
`planarCorrectorOscSublinearTwo_iff`) are proved with minimal scales of class `O_s` and no further hypothesis, in
[`PercolationClusterHomogenization/Proofs/Regularity/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Regularity/).

* **(5.33) of Lemma 5.8 above a minimal scale of class `O_s`** (`exists_planarNuFlatness_os`), from Proposition 5.2 for
  `ν` in the form `O_s` (`PlanarNuSubaddOsTwo p`). For one configuration, the flatness error of the coarsened maximizer
  of `ν(□_{n+1}, eᵢ)` is bounded by the reach, the subadditivity errors of `ν` and the constant of Lemma 5.5
  (`exists_planarFlatness_le_of_reach`): Lemma 5.5 is applied off its bad event, with the energy of the differences of the
  maximizers bounded by the subadditivity errors in place of `τ` (`planarNuDefect_le_of_errors`), the exceptional vertices
  counted by the reach, and the coarse energy and (4.26) bounded with the reach at most `(3^{n+1})^{1/40}`. This bound is
  at most `2 · 9ⁿ μⁿ` for some `μ < 1` and all large `n` (`exists_flatnessBound_le`). The bad event of Lemma 5.5 lies
  almost surely in a measurable event on the stopping sizes of the coarsely good and reverse Hölder partitions, of
  stretched-exponential probability (`exists_restrictBad_os`); with union bounds over the vertices, the subcubes and the
  scales, the exceptional event at the scale `n` has probability at most `C exp(−c 3^{nσ})`
  (`exists_measure_flatnessBad_le`), and the supremum of the `3ⁿ` on these events is of class `O_s`
  (`exists_isOsBond_of_events`).
* **(1.18) with a minimal scale of class `O_s`** (`planarAffineApproximationTwo_of_subaddOs`,
  `planarCorrectorSublinearL2Two_of_subaddOs`): the approximation of affine functions and the construction of the
  correctors of
  [Corrected planes, the dimension of the harmonic functions of linear growth and the corrector input in dimension two](#corrected-planes-the-dimension-of-the-harmonic-functions-of-linear-growth-and-the-corrector-input-in-dimension-two),
  with (5.33) above this minimal scale.
* **(1.22)** (`planarCorrectorOscSublinearTwo_of_sublinearL2`). The correctors `u₀, u₁` of the slopes `e₀, e₁` are bounded
  on the boxes of side `2N`, `N = 9 · 3^m`, by `C (3^m)^{1−7η}` above a minimal scale of class `O_s`
  (`exists_corrector_sup_os`, with the local minimal scales on the triadic boxes, `exists_isOsBond_scale_le_three`); a
  corrected plane of slope `q` is a constant plus `q₀ u₀ + q₁ u₁`, by the Liouville theorem of order zero
  (`eq_add_of_isCorrectedPlane`); and `Z_R = 2 (C + 1) max(R, 9 max(X, 1))^{1−7η}` is at most
  `18 (C + 1) R^{1−7η} max(X, 1)`, of class `O_s(C R^{1−δ})`.
* **The inputs are discharged** (`Rigidity/Proofs/Regularity/PlanarCorrectorOscHolds.lean`). `PlanarNuSubaddOsTwo p` is
  the part on `ν` of Proposition 5.2 (`planar_subadd_os`, `planarNuSubaddOsTwo_holds`), the minimal scales are
  `planarMinimalScalesTwo_holds` and the order-zero regularity is `armstrongDarioOrderZeroTwo_holds`. Hence
  `planarAffineApproximationTwo_holds`, `planarCorrectorSublinearL2Two_holds` and `planarCorrectorOscSublinearTwo_holds`.
  With (1.22), Lemma 3.2 of Dario holds with no hypothesis (`darioLemmaThreeTwo_holds`, by `darioLemmaThreeTwo_of_osc`, in
  `Rigidity/Proofs/Corrector/DarioLemmaThreeTwoHolds.lean`), and Theorem 1 of Dario in dimension two and the quantitative
  corrector input of Dario and Gu (Proposition 2.12) follow from the multiscale Poincaré inequality, the concentration
  inequality and Lemma 3.3 of Dario (`darioOptimalCorrectorTwo_of_lemmaThreeThree`,
  `correctorQuantitativeInputTwo_of_lemmaThreeThree`). There is no circularity: the route uses Proposition 5.2, the
  minimal scales and the order-zero regularity, not the corrector estimate of Dario.

| Lean declaration | Statement |
| --- | --- |
| [`exists_isOsBond_of_events`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarStretchedScales.lean), [`exists_restrictBad_os`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarRestrictErrorOs.lean), [`planarNuDefect_le_of_errors`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarRestrictErrorOs.lean) | a minimal scale of class `O_s` from events of stretched-exponential probability; the bad event of Lemma 5.5 inside a measurable event of stretched-exponential probability; the energy of the differences of the maximizers of `ν` bounded by the subadditivity errors. |
| [`exists_planarFlatness_le_of_reach`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarFlatnessPathwise.lean), [`exists_flatnessBound_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarFlatnessDecay.lean), [`exists_measure_flatnessBad_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarFlatnessOs.lean), [`exists_planarNuFlatness_os`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarFlatnessOs.lean) | the flatness error (5.33) for one configuration by its reach and the subadditivity errors, its decay, the probability of the exceptional event at each scale, and (5.33) above a minimal scale of class `O_s`. |
| [`planarAffineApproximationTwo_of_subaddOs`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarAffineApproximationOs.lean), [`planarCorrectorSublinearL2Two_of_subaddOs`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarAffineApproximationOs.lean) | the approximation of affine functions and (1.18) with minimal scales of class `O_s`, from Proposition 5.2 for `ν` in the form `O_s`, the minimal scales and the order-zero regularity. |
| [`exists_isOsBond_scale_le_three`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarLocalScalesOs.lean), [`exists_corrector_sup_os`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Regularity/PlanarCorrectorSupOs.lean), [`eq_add_of_isCorrectedPlane`](Rigidity/Proofs/Regularity/PlanarCorrectorOsc.lean), [`planarCorrectorOscSublinearTwo_of_sublinearL2`](Rigidity/Proofs/Regularity/PlanarCorrectorOsc.lean), [`planarCorrectorOscSublinearTwo_of_subaddOs`](Rigidity/Proofs/Regularity/PlanarCorrectorOsc.lean) | the local minimal scales on the triadic boxes, the bound of the correctors on the boxes, the corrected planes as combinations of `u₀, u₁`, and (1.22) from (1.18) and from Proposition 5.2 for `ν` in the form `O_s`. |
| [`planarNuSubaddOsTwo_holds`](Rigidity/Proofs/Regularity/PlanarCorrectorOscHolds.lean), [`planarCorrectorOscSublinearTwo_iff`](Rigidity/Proofs/Regularity/PlanarCorrectorOscHolds.lean), [`planarAffineApproximationTwo_holds`](Rigidity/Proofs/Regularity/PlanarCorrectorOscHolds.lean), [`planarCorrectorSublinearL2Two_holds`](Rigidity/Proofs/Regularity/PlanarCorrectorOscHolds.lean), [`planarCorrectorOscSublinearTwo_holds`](Rigidity/Proofs/Regularity/PlanarCorrectorOscHolds.lean) | Proposition 5.2 for `ν` in the form `O_s`, the identity of the two statements of (1.22), and the approximation of affine functions, (1.18) and (1.22) with no hypothesis beyond `𝔭_c(2) < 𝔭 < 1`. |
| [`Rigidity.Corrector.correctorOscSublinearTwo_holds`](Rigidity/Proofs/Corrector/DarioLemmaThreeTwoHolds.lean), [`darioLemmaThreeTwo_holds`](Rigidity/Proofs/Corrector/DarioLemmaThreeTwoHolds.lean), [`darioOptimalCorrectorTwo_of_lemmaThreeThree`](Rigidity/Proofs/Corrector/DarioLemmaThreeTwoHolds.lean), [`correctorQuantitativeInputTwo_of_lemmaThreeThree`](Rigidity/Proofs/Corrector/DarioLemmaThreeTwoHolds.lean) | (1.22) in the form used by Dario, Lemma 3.2 of Dario with no hypothesis, and Theorem 1 of Dario and Proposition 2.12 of Dario and Gu from the multiscale Poincaré inequality, the concentration inequality and Lemma 3.3. |

The twenty-three reports for the declarations of this section are in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Departures from Armstrong and Dario:

- **(5.33) in the form `O_s`.** Lemma 5.5 and (5.33) of Lemma 5.8 are printed in expectation (AD18.tex:2936-2950,
  AD18.tex:3402-3418). The form above a minimal scale of class `O_s` is assembled from printed ingredients: the pathwise
  inequalities of the proof of Lemma 5.5, Proposition 5.2 in the form `O_s` and the minimal scales of Proposition 2.4. The
  energy of the differences of the maximizers is bounded by the subadditivity errors, not by `τ_k`, and the exceptional
  vertices are counted by the reach.
- **(1.22) from the uniform bound.** The bound in the uniform norm of the remark after (1.19) is proved with a minimal
  scale of class `O_s` by a union bound over the triadic boxes, with the Lipschitz estimate in the form of the order-zero
  regularity at the centre, and the corrected planes of every slope are reduced to those of `e₀, e₁` by the Liouville
  theorem of order zero. The exponent obtained is `R^{1−δ/4}` (`7η = δ/4`, with `δ = min(δ₁, 1)` for the exponent `δ₁`
  of (1.18)), against `r^{1−δ/2}` in the remark after (1.19) (AD18.tex:554-559). This does not affect the statement,
  which asks only for some `δ ∈ (0, 1]`.

## The corrector estimate, the Green column and the Green function estimate in dimension two

Three planar inputs are reduced to named statements of Dario and of Dario and Gu, in
[`Rigidity/Proofs/Corrector/`](Rigidity/Proofs/Corrector/) and [`Rigidity/Proofs/Green/`](Rigidity/Proofs/Green/):

* **R6 in dimension two** (`SupercriticalBondGreenColumnExistenceTwo`) from `SupercriticalBondCorrectorInputTwo`
  alone: the existence of the planar Green columns is proved, and the uniqueness follows from the uniqueness of the
  zero-slope corrected plane (`supercriticalBondGreenColumnExistenceTwo_of_correctorInput`). With R2 proved,
  `supercriticalBondGreenColumnExistenceTwo_holds` is R6 in dimension two with no hypothesis beyond `𝔭_c(2) < 𝔭 < 1`.
* **R5 in dimension two** (`CorrectorQuantitativeInputTwo`, Dario and Gu, Proposition 2.12) from
  `DarioOptimalCorrectorTwo`, Theorem 1 of Dario in dimension two, and `SupercriticalBondCorrectorInputTwo`
  (`correctorQuantitativeInputTwo_of_dario`). `DarioOptimalCorrectorTwo` states: for every `p ∈ (𝔭_c(2), 1)`
  there are `s, C > 0` such that for all `x, y ∈ ℤ²` and every slope `q` there is a measurable `Z` with
  `Z ≤ O_s(C ‖q‖₁ √(log(2 + ‖x − y‖)))` and, almost surely, every corrected plane `ℓ` of slope `q` satisfies
  `|(ℓ(x) − q·x) − (ℓ(y) − q·y)| ≤ Z` for `x, y` in the infinite cluster. It is derived from named inputs in [Theorem 1 of Dario in dimension two](#theorem-1-of-dario-in-dimension-two).
* **R7 in dimension two** (`SupercriticalBondGreenQuantitativeTwo`, Dario and Gu, Theorem 2) from
  `DarioGuHeatKernelTwo`, Theorem 1 of Dario and Gu for the heat kernel `openHeat` of the infinite cluster (for
  `t ≥ 1`), and the Liouville theorem at order zero, which follows from `SupercriticalBondCorrectorInputTwo` or
  from `ArmstrongDarioOrderZeroTwo`
  (`supercriticalBondGreenQuantitativeTwo_of_darioGu_of_correctorInput`, `..._of_orderZero`). The small-time bound
  of the Carne–Varopoulos type is proved for the lazy walk (`lazyPow_le_carneVaropoulos`, `heatSmallTimeTwo`), so
  the hypothesis `CarneVaropoulosTwo` is not used in this reduction.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Green.supercriticalBondGreenColumnExistenceTwo_of_correctorInput`](Rigidity/Proofs/Green/PlanarGreenColumnCorrector.lean), [`sublinearLiouville_two_of_correctorInput`](Rigidity/Proofs/Green/PlanarGreenColumnCorrector.lean) | `SupercriticalBondCorrectorInputTwo → SupercriticalBondGreenColumnExistenceTwo`, and the sublinear Liouville theorem from the corrector input. |
| [`Rigidity.Corrector.correctorQuantitativeInputTwo_of_dario`](Rigidity/Proofs/Corrector/PlanarCorrectorQuantitative.lean), [`isOsBond_triadicScale`](Rigidity/Proofs/Corrector/OsCalculus.lean), [`isOsBond_triadicScale_shift`](Rigidity/Proofs/Corrector/OsCalculus.lean) | `DarioOptimalCorrectorTwo → SupercriticalBondCorrectorInputTwo → CorrectorQuantitativeInputTwo`, and the calculus of stretched exponential bounds for the triadic scales used in it. |
| [`Rigidity.Green.vsrwHeat_le_one`](Rigidity/Proofs/Green/LazyHeatKernel.lean), [`hasDerivAt_vsrwHeat`](Rigidity/Proofs/Green/LazyHeatKernel.lean), [`measurable_openHeat`](Rigidity/Proofs/Green/PlanarHeatKernelInputs.lean) | the heat kernel of the lazy walk and its time derivative, and the measurability of the heat kernel of the infinite cluster. |
| [`Rigidity.Green.frullani`](Rigidity/Proofs/Green/FrullaniGaussian.lean), [`integral_gaussianHeat_sub`](Rigidity/Proofs/Green/FrullaniGaussian.lean), [`integral_rpow_neg_mul_exp_neg_div`](Rigidity/Proofs/Green/FrullaniGaussian.lean) | Frullani's integral, the time integral `∫_0^∞ (p̄(t, z) − p̄(t, e)) dt = −log \|z\| / (π σ)` of the Gaussian kernel, and `∫_0^∞ t^{−β} e^{−a/t} dt = a^{1−β} Γ(β − 1)`. |
| [`Rigidity.Green.HeatBounds.laplacian_timeGreen`](Rigidity/Proofs/Green/PlanarGreenDeterministic.lean), [`abs_timeGreen_sub_le`](Rigidity/Proofs/Green/PlanarGreenQuantitative.lean), [`measurable_greenConstant`](Rigidity/Proofs/Green/PlanarGreenQuantitative.lean) | the Green function as the time integral `∫_0^∞ (p(t, x, y) − p(t, y, y)) dt` of the heat kernel and its Laplacian, the comparison with the homogenized Green function from the heat kernel estimate, and the measurability of the constant. |
| [`lazyPow_le_carneVaropoulos`](Rigidity/Proofs/Green/LazyCarneVaropoulos.lean), [`openHeat_le_exp_of_le_norm`](Rigidity/Proofs/Green/LazyCarneVaropoulos.lean), [`heatSmallTimeTwo`](Rigidity/Proofs/Green/LazyCarneVaropoulos.lean) | the Carne–Varopoulos bound for the lazy walk on an infinite open component of `ℤ²` and the small-time heat kernel bound derived from it, with no hypothesis. |
| [`supercriticalBondGreenQuantitativeTwo_of_darioGu`](Rigidity/Proofs/Green/LazyCarneVaropoulos.lean), [`..._of_darioGu_of_correctorInput`](Rigidity/Proofs/Green/LazyCarneVaropoulos.lean), [`..._of_darioGu_of_orderZero`](Rigidity/Proofs/Green/LazyCarneVaropoulos.lean), [`supercriticalBondGreenQuantitativeTwo_of_heatKernel`](Rigidity/Proofs/Green/PlanarGreenQuantitative.lean), [`supercriticalBondGreenQuantitativeTwo_of_smallTime`](Rigidity/Proofs/Green/PlanarGreenQuantitative.lean) | `SupercriticalBondGreenQuantitativeTwo` from `DarioGuHeatKernelTwo` and the Liouville theorem at order zero (as a hypothesis, from `SupercriticalBondCorrectorInputTwo`, or from `ArmstrongDarioOrderZeroTwo`); the last two take the small-time heat kernel bound as a hypothesis. |

The twenty-seven reports for the declarations of this section are in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean). With the previous section, the three planar inputs
are consequences of `DarioGuHeatKernelTwo` and the inputs `MultiscalePoincareTwo`, `ConcentrationTwo` and `DarioLemmaThreeThree` of [Theorem 1 of Dario in dimension two](#theorem-1-of-dario-in-dimension-two) (Lemma 3.2 of Dario is
proved, `darioLemmaThreeTwo_holds`, and the order-zero regularity
`PlanarHarmonicApproximationTwo` is proved, in
[Lemma 7.1 and the order-zero regularity in dimension two from Theorem 1](#lemma-71-and-the-order-zero-regularity-in-dimension-two-from-theorem-1)).
`DarioGuHeatKernelTwo` is proved from named inputs in [Theorem 1 of Dario and Gu in dimension two](#theorem-1-of-dario-and-gu-in-dimension-two).

Departures from Dario and from Dario and Gu:

- **Pairs of points.** Theorem 1 of Dario is applied to the pairs of points in the ball around `x`, with a union
  bound over the pairs, in the passage to `CorrectorQuantitativeInputTwo`.
- **Time range.** The heat kernel estimate `DarioGuHeatKernelTwo` is stated for `t ≥ 1`; the small times are
  covered by the Carne–Varopoulos bound for the lazy walk.
- **Normalization.** Dario and Gu normalize the time integral of `p̄` by its mean over the unit ball, which
  produces the constant `K₁`; here it is normalized by `p̄(t, e)` with `|e| = 1`, which gives the homogenized Green
  function `ḡ` without a constant.
- **Green function as a time integral.** The identity `g(x, y) = ∫_0^∞ (p(t, x, y) − p(t, y, y)) dt` (DG21.tex:336-338
  and display (5.4)), which the source states without proof, is proved here for planar clusters.

Misprints in the sources whose meaning is clear: Dario18.tex:216 and DG21.tex:1094 print `log^{1/2}|x − y|`, which
vanishes at `|x − y| = 1`, and the Lean statement uses `log^{1/2}(2 + |x − y|)`; AD18.tex:837-848 (the sign of the
exponent of the tail).

## Theorem 1 of Dario in dimension two

Theorem 1 of Dario (*Optimal corrector estimates on percolation clusters*) in `d = 2`, the statement
`DarioOptimalCorrectorTwo` (`|χ_q(x) − χ_q(y)| 1_{x, y ∈ 𝒞_∞} ≤ O_s(C ‖q‖₁ √(log(2 + ‖x − y‖)))`, see
[the corrector estimate, the Green column and the Green function estimate in dimension two](#the-corrector-estimate-the-green-column-and-the-green-function-estimate-in-dimension-two)),
and with it the quantitative corrector input `CorrectorQuantitativeInputTwo` of Dario and Gu are proved from the
following named inputs, in [`Rigidity/Proofs/Corrector/`](Rigidity/Proofs/Corrector/)
([`darioOptimalCorrectorTwo_of_inputs`, `correctorQuantitativeInputTwo_of_inputs`](Rigidity/Proofs/Corrector/PlanarDarioCorrectorHolds.lean)):

* `SupercriticalBondCorrectorInputTwo` (R2), which is proved for `𝔭_c(2) < 𝔭 < 1`
  (`supercriticalBondCorrectorInputTwo_holds`, in
  [Corrected planes, the dimension of the harmonic functions of linear growth and the corrector input in dimension two](#corrected-planes-the-dimension-of-the-harmonic-functions-of-linear-growth-and-the-corrector-input-in-dimension-two)),
  and is no longer a hypothesis of `darioOptimalCorrectorTwo_of_oscillation`;
* `MultiscalePoincareTwo A₀` with some `A₀ > 0`: the multiscale Poincaré inequality of Dario, Proposition 2.19,
  display (2.26), in cube form at `R = 3^m`, with the constant `A₀ q^{3/2}` for `q ≥ 2`, and with the absolute
  convergence of the convolutions `Φ_{r²} * ∇u` required, as the printed statement uses them (the statement is
  proved almost surely for the coarsened corrector, `ae_summable_heat_coarseField`). It is proved on `ℤ²`
  (`Rigidity.Poincare.multiscalePoincareTwo_holds`, see
  [The multiscale Poincaré inequality (2.26) on the square lattice](#the-multiscale-poincaré-inequality-226-on-the-square-lattice));
  Dario proves (2.26) in the continuum, from Proposition D.1 of Armstrong, Kuusi and Mourrat with Remark D.6 and
  Lemma 7.12 and Proposition 9.9 of Gilbarg and Trudinger, and states the version on the lattice by "standard
  arguments". The named input `MultiscalePoincareTwo` remains the hypothesis of the older theorems of this section;
  the bridge theorems of the next paragraph discharge it;
* `ConcentrationTwo`: the concentration inequality of Dario, Proposition 2.17, for integrable variables with
  finite resampling variance almost surely, in the moment-inequality form of Boucheron, Bousquet, Lugosi and Massart. The constant `C` depends on `p` as well as on `β`, where Dario prints `C(d, β)`. It is proved (`Rigidity.Corrector.concentrationTwo_holds`, see
  [The concentration inequality of Proposition 2.17](#the-concentration-inequality-of-proposition-217)); it remains
  a hypothesis of the older theorems of this section;
* `DarioLemmaThreeTwo` and `DarioLemmaThreeThree`: Lemmas 3.2 and 3.3 of Dario for the coarsened correctors at every
  point, `|E[Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)]| ≤ C/r` and `𝕍[Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)] ≤ O_s(C/r²)` for `r ≥ 1`
  (Dario takes `x = 0` by stationarity, which does not hold for the partition `𝒫` itself, so these are the lemmas for the
  translated partitions `𝒫_y`). Proposition 3.1, `|Φ_{r²} * ∇[χ_{e_i}]_𝒫(x)| ≤ O_s(C/r)`, is derived from them and
  from `ConcentrationTwo` by the printed proof (`darioPropThreeOneTwo_of_lemmas`). Lemma 3.2 is proved with no hypothesis
  (`darioLemmaThreeTwo_holds`, see
  [The quantitative sublinearity of the correctors in dimension two](#the-quantitative-sublinearity-of-the-correctors-in-dimension-two)),
  so Theorem 1 of Dario and `CorrectorQuantitativeInputTwo` follow from the multiscale Poincaré inequality, the
  concentration inequality and Lemma 3.3 (`darioOptimalCorrectorTwo_of_lemmaThreeThree`,
  `correctorQuantitativeInputTwo_of_lemmaThreeThree`). With the multiscale Poincaré inequality and the concentration
  inequality proved, Theorem 1 of Dario in `d = 2` follows from `DarioLemmaThreeThree` alone
  (`Rigidity.Poincare.darioOptimalCorrectorTwo_of_threeThree`) and from `DarioFlipSumBound` alone
  (`darioOptimalCorrectorTwo_of_flipSum`); see
  [Lemma 3.3 in flip form and the bridges to Theorem 1](#lemma-33-in-flip-form-and-the-bridges-to-theorem-1).

The order-zero regularity input (R3), which Dario uses in Proposition 2.14, is proved in dimension two
(`armstrongDarioOrderZeroTwo_holds`, see
[Lemma 7.1 and the order-zero regularity in dimension two from Theorem 1](#lemma-71-and-the-order-zero-regularity-in-dimension-two-from-theorem-1)).

The proof is that of Sections 4 and 5 of Dario with the following steps proved:

* **Section 5, Theorem 1 from Theorem 2** (Steps 1 to 6). The moments of the increments of the coarsened corrector,
  from (5.5) (Theorem 2 on the box), the stationarity (2.3) of the translated fields and the comparison (5.7) of the
  translated partitions, grow like `q^{kq} m^{q/2}` (`LinftyIterationData.mom_sub_le`, Steps 1 to 4); the moments give
  a stretched exponential bound (5.1) (`isOsBond_of_moment_le`, Step 5); the coarsening error (5.10) and the
  uniqueness of corrected planes give the bound for the corrector itself (`darioOptimalCorrectorTwo_of_coarsened`,
  Step 6).
* **Section 4, Step 1 of Theorem 2** in moment form: the multiscale Poincaré inequality (2.26), Proposition 3.1 and
  the Lipschitz bound (2.22) give (5.4) and (5.5) (`lintegral_boxOsc_le_of_poincare`).
* **Proposition 2.15 at the origin** from the order-zero regularity (Proposition 2.14) and the local gradient bound
  of the cluster (`lipschitz_correctedPlane_origin`), the measurable planar corrector increments
  (`correctorDiff`), the anchors of the translated partitions (`shiftedAnchor`), the coarsening error (5.10) and the
  comparison (5.7) for the planar partition (`baseCoarseningError`, `baseComparison`), and the bound of the
  heat-kernel averages of the gradient of the coarsened corrector by `O_s(C)`, uniformly in the radius and the point
  (`heatGradient_coarseField_isOsBond`).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Corrector.darioOptimalCorrectorTwo_of_prop31`](Rigidity/Proofs/Corrector/PlanarHeatSmoothing.lean), [`darioPropThreeOneTwo_of_lemmas`](Rigidity/Proofs/Corrector/DarioPropThreeOne.lean), [`darioOptimalCorrectorTwo_of_lemmas`](Rigidity/Proofs/Corrector/DarioPropThreeOne.lean), [`darioOptimalCorrectorTwo_of_inputs`](Rigidity/Proofs/Corrector/PlanarDarioCorrectorHolds.lean) | Dario's Theorem 1 in `d = 2` from R2, R3, `MultiscalePoincareTwo A₀` (`A₀ > 0`) and Proposition 3.1 (`DarioPropThreeOneTwo`); Proposition 3.1 from `ConcentrationTwo` and Lemmas 3.2 and 3.3 (`DarioLemmaThreeTwo`, `DarioLemmaThreeThree`) and R3; and the composition, with R3 discharged by `armstrongDarioOrderZeroTwo_holds`. |
| [`correctorQuantitativeInputTwo_of_inputs`](Rigidity/Proofs/Corrector/PlanarDarioCorrectorHolds.lean) | `CorrectorQuantitativeInputTwo` (R5) from R2, `MultiscalePoincareTwo`, `ConcentrationTwo`, `DarioLemmaThreeTwo` and `DarioLemmaThreeThree`, by `correctorQuantitativeInputTwo_of_dario`. |
| [`darioOptimalCorrectorTwo_of_orderZero`](Rigidity/Proofs/Corrector/PlanarDarioCorrector.lean), [`darioOptimalCorrectorTwo_of_poincareInputs`](Rigidity/Proofs/Corrector/PlanarDarioCorrector.lean), [`darioOptimalCorrectorTwo_of_coarsened`](Rigidity/Proofs/Corrector/DarioOptimalCorrector.lean), [`darioOptimalCorrectorTwo_of_coarsenedOs`](Rigidity/Proofs/Corrector/DarioCoarsenedOs.lean), [`darioOptimalCorrectorTwo_of_poincare`](Rigidity/Proofs/Corrector/DarioPoincareMoments.lean) | the chain of weaker forms: Theorem 1 from Theorem 2 at the origin for the coarsened correctors, from the Poincaré inputs, and from the coarsened corrector data in moment form and in the printed `O_s` form. |
| [`lipschitz_correctedPlane_origin`](Rigidity/Proofs/Corrector/PlanarCorrectorLipschitz.lean) | Dario's Proposition 2.15 at the origin in `d = 2`: `\|ℓ(a) − ℓ(b)\| ≤ L max(X, 2)² Σ \|q_i\|` for every open edge `ab` at the origin, from the order-zero regularity. |
| [`baseCoarseningError`](Rigidity/Proofs/Corrector/PlanarCoarseningError.lean), [`baseComparison`](Rigidity/Proofs/Corrector/PlanarPartitionComparison.lean), [`lintegral_randomBallSum_le`](Rigidity/Proofs/Corrector/RandomBallSums.lean) | the coarsening error (5.10) at every vertex and the comparison (5.7) of the translated partitions for the planar partition, with `O_s` bounds uniform in the vertex, from the Lipschitz bound and the exponential moments of the partition sizes. |
| [`correctorDiff_translation`](Rigidity/Proofs/Corrector/PlanarMeasurableCorrector.lean), [`measurable_guardAnchor`](Rigidity/Proofs/Corrector/PlanarShiftedAnchor.lean), [`infinite_planarCoarseAnchor`](Rigidity/Proofs/Corrector/PlanarShiftedAnchor.lean), [`darioCoarsenedCorrectorTwo_of_base`](Rigidity/Proofs/Corrector/DarioCoarsenedFields.lean) | the measurable corrector increments with the stationarity (2.3), the measurable anchors of the planar partition in the infinite cluster, and the reduction of the coarsened corrector data of Section 5 to its statements at the base point. |
| [`lintegral_boxOsc_le_of_poincare`](Rigidity/Proofs/Corrector/DarioPoincareMoments.lean), [`lintegral_rpow_heatSquare_le`](Rigidity/Proofs/Corrector/DarioPoincareMoments.lean), [`tsum_poincareWeight_le`](Rigidity/Proofs/Corrector/DarioPoincareMoments.lean), [`heatGradient_coarseField_isOsBond`](Rigidity/Proofs/Corrector/PlanarHeatSmoothing.lean), [`tsum_ofReal_vsrwHeat`](Rigidity/Proofs/Green/LazyHeatMass.lean) | Step 1 of Theorem 2 in moment form from (2.26), Proposition 3.1 and (2.22), the moment of the heat-kernel square function at a point, the lattice sum of the weights, the bound of the heat-kernel averages uniform in the radius, and the mass one of the heat kernel of the lazy walk. |
| [`IsOsBond.integral_rpow_le`](Rigidity/Proofs/Corrector/DarioMoments.lean), [`isOsBond_of_moment_le`](Rigidity/Proofs/Corrector/DarioMoments.lean), [`isOsBond_sub_of_linftyIterationData`](Rigidity/Proofs/Corrector/DarioOptimalCorrector.lean), [`LinftyIterationData.mom_sub_le`](Rigidity/Proofs/Corrector/DarioLinftyIteration.lean) | the moments of an `O_s` variable (5.1), the converse of Step 5, Step 5 for the increments of the coarsened corrector, and the moment bound of Steps 1 to 4. |

The thirty-five reports for the declarations of this section are in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Lemma 3.3 of Dario rests on steps that Dario only sketches and that are part of the
named input `DarioLemmaThreeThree`: Lemma 3.5 on resampling the partition, which is proved for the planar
partition of the repository in the section on Steps 1 and 2 below, and the Green gradient bounds of Propositions 2.11 and 2.12, which Dario proves by
"standard arguments" and which are proved here (see
[Lemma 3.3 in flip form and the bridges to Theorem 1](#lemma-33-in-flip-form-and-the-bridges-to-theorem-1)). Lemma 3.2 does not use them: it
follows from (1.22) (`CorrectorOscSublinearTwo`), which is proved. The estimate (3.3) for the
stationary partitions, which Dario proves "similarly to Proposition 2.1 (iv) of Armstrong and Dario", is proved
(`dario_errorstatpart`): the stationary partition is the planar partition capped at the scale `k`, which exists
deterministically and is stationary under the translations by `3^k ℤ²`
(`Rigidity/Proofs/Corrector/DarioStationaryPartition.lean`), and `P[∃ x ∈ □, □_𝒫(x) ≠ □_{𝒫_stat^k}(x)] ≤ C exp(−c 3^k)` for
every triadic cube `□` of scale `k` follows from the localization of the planar partition. Step 3 of the proof of
Lemma 3.2 is proved as well (`abs_tsum_openHeat_mul_periodic_le_exp`, `Rigidity/Proofs/Corrector/PeriodicHeatDecay.lean`):
for a `3^k`-periodic function `f` of sum zero over a period and `9^k ≤ r`, `|Φ_{r²} * f(x)| ≤ e^{−16 r} Σ_{period} |f|`, by the
discrete Fourier transform. Steps 1 and 2 of the proof of Lemma 3.2 are proved from the quantitative sublinearity (1.22) of
Armstrong and Dario in its `O_s` form (`CorrectorOscSublinearTwo`): the expected discrepancy between the coarsened
correctors of the planar and of the stationary partitions is at most `K (1 + C 9^k)⁴ e^{−c 3^k/2}`
(`exists_lintegral_abs_statDiscrepancy_le`, Step 1), the expected increment of the stationary coarsened corrector along a
segment of length `N` is at most `C N^{1−δ} + C` (`exists_lintegral_abs_statSegment_le`), and the mean of its gradient is periodic
under `3^k ℤ²` with sum zero over a period (`sum_statMean_period_eq_zero`, Step 2). With them `darioLemmaThreeTwo_of_osc`
derives `DarioLemmaThreeTwo` for `r ≥ 1`, with `k = log₉ ⌊r⌋`, from (1.22) and the order-zero regularity, and
`darioOptimalCorrectorTwo_of_osc` is Theorem 1 of Dario from the multiscale Poincaré inequality, the concentration
inequality, (1.22) and `DarioLemmaThreeThree`. The statement (1.22) is proved in dimension two with no hypothesis
(`correctorOscSublinearTwo_holds`, see
[The quantitative sublinearity of the correctors in dimension two](#the-quantitative-sublinearity-of-the-correctors-in-dimension-two)),
so `darioLemmaThreeTwo_holds` is Lemma 3.2 with no hypothesis.
The seven reports for these declarations are in [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean). Lemma 3.3 is
reduced to the named input `DarioFlipSumBound`, the estimate (3.13) in flip form; its proof is reduced to Lemma 3.5 for
the planar partition and the Step 2 sum in
[Steps 1 and 2 of Lemma 3.3 in flip form and Lemma 3.5 for the planar partition](#steps-1-and-2-of-lemma-33-in-flip-form-and-lemma-35-for-the-planar-partition).

Departures from Dario:

- **Lemma 3.2: the anchor order.** The stationary anchor `z̄_stat` is the first point of `𝒞_∞` in the anchor order of the
  partition (distance in `ℓ∞` to the centre, then lexicographic order), where Dario takes the point of `𝒞_∞`
  nearest to `□` with lexicographic ties (Dario18.tex:976-982).
- **Lemma 3.2, Step 2 along lines.** The increments are telescoped along lines in each coordinate direction
  (`exists_lintegral_abs_statSegment_le`, `sum_statMean_line_eq_zero`) in place of the Stokes formula on `□_{nk}`.
- **Lemma 3.2, Step 1 at every vertex.** The discrepancy is bounded vertex by vertex through the anchor discrepancy, with
  second moments and the inequality of the arithmetic and geometric means, in place of the sets `U`, the `O_s` bound
  and the Cauchy–Schwarz inequality.

- **Moments in place of the `O_s` calculus.** The averaging of `O_s` variables, (1.12) and (1.14), is replaced by
  moment bounds: Jensen's inequality in `r` for the measure `min(r, 1/r) dr`, Tonelli's theorem and lattice sums of
  exponential weights (`DarioMoments`, `DarioPoincareMoments`, `RandomBallSums`); the sums over balls of random
  radius of (2.24), (5.7) and (5.10) are bounded by `lintegral_randomBallSum_le`. The exponent of the moments is
  `k = 3/2 + 1/s`, and the exponential moment (5.1) is proved with the factor `e^{−q/s}`, where (5.1) prints
  `e^{q/s}`, which is weaker.
- **The multiscale Poincaré inequality in cube form.** Proposition 2.19 is stated for balls `B_R`, with the lattice version left to standard arguments; it is used on
  the cubes of side `R = 3^m`, the form in which (5.4) is applied, and the exponents `1 ≤ q < 2` are reduced to
  `q = 2` by Jensen's inequality.
- **Proposition 2.15 at the origin.** The Lipschitz bound is `L max(X, 2)²`, where Dario has `X^{d/2}`, because the
  cluster ball `B_{4r}` is bounded by the lattice ball `B_{5r}`; it is again `O_{s/2}(C)`.
- **Step 6 in pair form.** The coarsening error (5.10) is stated for the increment between two points.
- **The translated partitions.** The partition `𝒫_y = y + 𝒫(τ_{−y} a)` is built from the anchors of the planar
  partition of the repository, and the bounds of the partition sizes are those of the planar partition.
- **The logarithm.** Theorem 1 is stated with `log^{1/2}(2 + |x − y|)`, as in the section on the corrector estimate.

## The concentration inequality of Proposition 2.17

Proposition 2.17 of Dario, `ConcentrationTwo`, is proved in `d = 2` (`Rigidity.Corrector.concentrationTwo_holds`,
[`ConcentrationTwoHolds.lean`](Rigidity/Proofs/Corrector/ConcentrationTwoHolds.lean)): for `p ∈ (0, 1)`, `β ∈ (0, 2)` and an integrable `X` of the bond
configuration with `𝕍[X] < ∞` almost surely, `𝔼[exp(|X − 𝔼X|^β)] ≤ C 𝔼[exp((C 𝕍[X])^{β/(2−β)})]^{(2−β)/β}` with `C = C(p, β)`. The proof is
in [`Rigidity/Proofs/Probability/`](Rigidity/Proofs/Probability/) (eight files) and the two files `ConcentrationTwoHolds` and `DarioCorrectorConcentration` of `Rigidity/Proofs/Corrector/`.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Probability.lintegral_abs_sub_rpow_le_vertSum`](Rigidity/Proofs/Probability/BernoulliMoments.lean), [`cubeExp_abs_sub_rpow_le`](Rigidity/Proofs/Probability/CubeMomentBound.lean) | the moment inequality `𝔼\|X − 𝔼X\|^q ≤ 2 (3q/c)^{q/2} 𝔼[𝕍[X]^{q/2}]` for `q ≥ 2` and `c = min(p, 1 − p)`: on the finite cube, then for the infinitely many bonds by conditioning on finitely many of them. |
| [`rpowEntropy_le_sum_coordEntropy`](Rigidity/Proofs/Probability/BernoulliCube.lean), [`bregmanRpow_convex`](Rigidity/Proofs/Probability/BregmanConvex.lean) | the tensorization of the `φ`-entropy for `φ(x) = x^r`, `1 ≤ r ≤ 2`, and the joint convexity of the Bregman divergence of `x^r` on the closed quadrant. |
| [`condExp_allExcept_ae_eq`](Rigidity/Proofs/Probability/BernoulliProduct.lean), [`vertical_condExp_ae_eq`](Rigidity/Proofs/Probability/BernoulliProduct.lean) | the conditional expectation given all bonds but one is the two-point average, and the vertical derivative of `𝔼[X \| ℱ_S]` is the conditional expectation of the vertical derivative. |
| [`lintegral_exp_rpow_le_of_moments`](Rigidity/Proofs/Probability/StretchedExponential.lean) | the stretched exponential bound from the moment inequality, by expansion of `exp(\|Z\|^β)` in powers. |

The nine reports for the declarations of this section are in [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Departures:

- **The source.** Dario cites the proposition to Armstrong and Lin (*Optimal quantitative estimates in stochastic homogenization for
  elliptic equations in nondivergence form*, ARMA 225 (2017), Proposition 2.2, with the proof of its Appendix A); it is not a result of Armstrong, Kuusi and Mourrat.
- **The moment inequality.** Armstrong and Lin cite the moment inequality of Boucheron, Bousquet, Lugosi and Massart with the variance proxy
  defined through conditional expectations; Boucheron, Bousquet, Lugosi and Massart (Ann. Probab. 33 (2005), Theorem 2)
  prove it with the resampled quantity `V⁺`. For Bernoulli bonds `(X − X'_e)² ≥ min(p, 1 − p)² (X(ω^{e,1}) − X(ω^{e,0}))²`, and their argument
  (tensorization of `φ`-entropies, the two-point bound, induction on the moments) is carried out with the flip differences directly, with the factor
  `min(p, 1 − p)`; the constant `C` depends on `p` and `β`, where Dario has `C(d, β)`.
- **The combining step.** Armstrong and Lin sketch the passage from the moments to the exponential ("Combining ... yields"), which leaves
  `exp(𝔼[V]^{β/2})` to be absorbed. It is written out: the terms of the series with `βn < 2` are bounded through the second moment (`|Z|^{βn} ≤ 1 + Z²`),
  the others by Young's inequality termwise, and the exponent `(2 − β)/β < 1` for `β > 1` by Jensen's inequality, in place of Hölder's inequality across the series.
- **Degenerate laws and infinitely many bonds.** For `p ∈ {0, 1}` the law is a point mass and the inequality holds with `C = 1`. The Efron–Stein
  and moment inequalities on infinitely many bonds are obtained from the finite cube through `𝔼[X | ℱ_S]`, the Lévy upward theorem and Fatou's lemma.

## The multiscale Poincaré inequality (2.26) on the square lattice

The multiscale Poincaré inequality of Dario, Proposition 2.19, display (2.26), in the cube form of `MultiscalePoincareTwo A₀`
(`‖u − (u)_□‖` in `L^q` of the cube of side `R = 3^m` bounded by `A₀ q^{3/2}` times the weighted `ℓ^q` sum of the
square function `(∫₀^{2R} r |Φ_{r²} * ∇u(x)|² dr)^{1/2}`), is proved on `ℤ²` in
[`Rigidity/Proofs/Poincare/`](Rigidity/Proofs/Poincare/) (nineteen files, `LatticeHeatKernel` to `MultiscalePoincareHolds`). The eight reports for the declarations of this section and of `DarioCorrectorPoincare` are in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Poincare.multiscalePoincareTwo_holds`](Rigidity/Proofs/Poincare/MultiscalePoincareHolds.lean) | `∃ A₀, 0 < A₀ ∧ MultiscalePoincareTwo A₀`, the statement as `MultiscalePoincareTwo` has it, with the constant of order `q` (so at most `A₀ q^{3/2}`). |
| [`Rigidity.Poincare.exists_multiscalePoincare_box`](Rigidity/Proofs/Poincare/MultiscalePoincareHolds.lean), [`exists_steinSigned`](Rigidity/Proofs/Poincare/SteinSigned.lean), [`exists_steinWeighted`](Rigidity/Proofs/Poincare/SteinFinal.lean), [`tsum_mul_eq_add_integral`](Rigidity/Proofs/Poincare/HeatDuality.lean) | the box form, the weighted Littlewood–Paley bound for signed and for nonnegative data (Stein's argument), and the duality identity between the pairing of a function with a divergence and the heat averages of its gradient. |
| [`tsum_boxMax_rpow_le`](Rigidity/Proofs/Poincare/BoxMaximal.lean), [`exists_heat_le_boxMax`](Rigidity/Proofs/Poincare/HeatMaximal.lean), [`openHeat_allOpen_eq_lineKernel`](Rigidity/Proofs/Poincare/LatticeHeatKernel.lean), [`exists_openHeat_mul_exp_le`](Rigidity/Proofs/Poincare/HeatKernelBounds.lean) | the strong type `(p, p)` bound of the centred box maximal function (Vitali covering, layer cake), the domination of the tilted heat semigroup by it, the heat kernel of the lattice as a product of one-dimensional continuous-time kernels, and the bound of its exponentially tilted version. |

Departure from Dario: Dario proves (2.26) in the continuum in Appendix A, from the estimate of Proposition D.1 of Armstrong,
Kuusi and Mourrat (with Remark D.6) on the dual norm `W^{−1,q}` through the Nečas inequality (Bogovskii operator,
Newtonian potential and the Calderón–Zygmund estimate) and a rescaling. The lattice statement is proved
directly by the duality argument of Proposition D.1: the `L^q` oscillation of `u` on the cube is paired with an extremal
test function of mean zero, the pairing is written through the heat flow of the test function and one summation by
parts, the bilinear term is bounded by Hölder's inequality with weights, and the weighted square function of the dual
data by Stein's argument and the maximal function. The weight `e^{|x|/2R}` is handled by the product of the
hyperbolic cosines of the coordinates, an eigenfunction of the heat semigroup. The Nečas inequality and the
Calderón–Zygmund theory are not used.

## Lemma 3.3 in flip form and the bridges to Theorem 1

Lemma 3.3 of Dario (`𝕍[Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)] ≤ O_s(C/r²)`) in `d = 2` is reduced to the named input
`DarioFlipSumBound` (the estimate (3.13) in flip form), and the Green function estimates and Cases 1 to 3 of Step 2 of its proof
are proved, in [`Rigidity/Proofs/Corrector/`](Rigidity/Proofs/Corrector/) (thirteen files `DarioBondResampling`,
`DarioLemmaThreeThreeFlip`, `DarioClusterGreen`, `DarioCoarseHeatField`, `DarioFiniteEnergyGrowth`,
`DarioFiniteEnergySublinear`, `DarioCaseThree*`, `DarioFlipCluster`, `DarioCaseOneTwo`). `DarioFlipSumBound` is the statement that, for every
direction, component, radius `r ≥ 1` and point, the sum over bonds `e` of the squared flip differences
`(X(ω^{e,1}) − X(ω^{e,0}))²` of `X = Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)` is at most `O_s(C/r²)`. Lemma 3.5 (the partition of the
resampled configuration agrees with 𝒫 away from a ball around the resampled bond) is proved for the planar
partition of the repository (`darioResamplePartitionTwo_holds`). Step 1 of the proof of Lemma 3.3 is proved from Lemma 3.5, and the sum of Step 2 (H2), the hypothesis `hTwo` of `darioFlipSumBound_of_resample`, is proved (`darioStepTwoSumBound_holds`), in [Steps 1 and 2 of Lemma 3.3 in flip form and Lemma 3.5 for the planar partition](#steps-1-and-2-of-lemma-33-in-flip-form-and-lemma-35-for-the-planar-partition).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Corrector.darioLemmaThreeThree_of_flipSum`](Rigidity/Proofs/Corrector/DarioLemmaThreeThreeFlip.lean), [`ae_resampleVar_le_tsum_bondFlipDiff`](Rigidity/Proofs/Corrector/DarioBondResampling.lean), [`condExp_bondsExcept_ae_eq`](Rigidity/Proofs/Corrector/DarioBondResampling.lean), [`IsOsBond.comp_setBond`](Rigidity/Proofs/Corrector/DarioBondResampling.lean) | Lemma 3.3 from `DarioFlipSumBound`: for the Bernoulli law the conditional expectation given all other bonds is the two-point average, so the resampling variance is at most the sum of the squared flip differences, and `O_s` bounds are kept when one bond is forced (the form of (3.12)). |
| [`greenProj`](Rigidity/Proofs/Corrector/DarioClusterGreen.lean), [`edgeDiv_greenProj`](Rigidity/Proofs/Corrector/DarioClusterGreen.lean), [`eq_greenProj_of_edgeDiv_eq`](Rigidity/Proofs/Corrector/DarioClusterGreen.lean), [`exists_isGradOf_greenProj`](Rigidity/Proofs/Corrector/DarioClusterGreen.lean) | Propositions 2.11 and 2.12 for bond percolation in `d = 2`: the gradient of the finite-energy solution of the divergence-form equation is the orthogonal projection `P` onto the closed span of the gradients of point masses in `ℓ²(edges)`; it solves the equation, is the only solution in that span, and has a potential. |
| [`norm_greenProj_le`](Rigidity/Proofs/Corrector/DarioClusterGreen.lean), [`inner_greenProj_comm`](Rigidity/Proofs/Corrector/DarioClusterGreen.lean), [`greenProj_apply_eq_tsum`](Rigidity/Proofs/Corrector/DarioClusterGreen.lean) | (2.14) with `C = 1`, the symmetry (2.15) and the representation formula (2.17). |
| [`heatComp_coarse_eq_inner`](Rigidity/Proofs/Corrector/DarioCoarseHeatField.lean), [`abs_coarseHeatField_apply_le`](Rigidity/Proofs/Corrector/DarioCoarseHeatField.lean) | (3.26) and (3.27) for the planar partition: the heat average of a coarsened gradient is the pairing of the gradient with the field of the paths between the anchors of neighbouring partition cubes, and this field is bounded by the heat kernel at the points whose ninefold square contains the edge. |
| [`abs_sub_coarseAnchor_zero_le`](Rigidity/Proofs/Corrector/DarioFiniteEnergyGrowth.lean), [`ae_abs_sub_coarseAnchor_le_of_finiteEnergy`](Rigidity/Proofs/Corrector/DarioFiniteEnergySublinear.lean) | growth of a function of finite energy on the infinite cluster: at most `400 s^{3/2} (R+1)^{1/2} E^{1/2}` when the partition cubes of the square of half-side `R` have side at most `s`, and almost surely sublinear, from the minimal scales of the planar partition. |
| [`edgeGrad_eq_smul_greenProj_of_div`](Rigidity/Proofs/Corrector/DarioCaseThree.lean), [`ae_edgeGrad_eq_smul_greenProj_of_div`](Rigidity/Proofs/Corrector/DarioCaseThreeAe.lean), [`ae_edgeGrad_eq_smul_greenProj`](Rigidity/Proofs/Corrector/DarioCaseThreeAe.lean), [`ae_sublinearOn_of_isGradOf`](Rigidity/Proofs/Corrector/DarioCaseThreeAe.lean) | (3.22): almost surely a sublinear function whose Laplacian on the cluster is `c` times the dipole of a source with divergence `δ_x − δ_y` has gradient `c P` of the source, by the planar Liouville theorem. |
| [`ae_correctedPlane_sub_eq_smul_greenProj`](Rigidity/Proofs/Corrector/DarioCaseThreeCorrector.lean), [`ae_correctedPlane_sub_eq_smul_greenProj_closed`](Rigidity/Proofs/Corrector/DarioCaseThreeClosed.lean), [`edgeDiv_pathField`](Rigidity/Proofs/Corrector/DarioCaseThreeClosed.lean) | Case 3 of Step 2 (both endpoints in the infinite cluster with the bond closed): the corrected planes with the bond open and closed differ by a function with gradient the increment across the bond times `P` of the bond (open base configuration) or of the field of an open path (closed base configuration). |
| [`heatComp_coarse_eq_smul_greenProj`](Rigidity/Proofs/Corrector/DarioCaseThreePairing.lean), [`ae_heatComp_coarse_sub_eq_smul_greenProj`](Rigidity/Proofs/Corrector/DarioCaseThreePairing.lean), [`ae_heatComp_coarse_sub_eq_walkSum_closed`](Rigidity/Proofs/Corrector/DarioCaseThreeClosed.lean), [`abs_sub_le_two_mul_edgeVariation`](Rigidity/Proofs/Corrector/DarioCaseThreePairing.lean) | (3.26) paired with (3.22) and (2.15): in Case 3 the heat average of the coarsened change of the corrected planes is the increment across the bond times the pairing of `P` with the anchor-path field (for the closed bond, the sum along the path); and the (3.24) form of the increment across a bond by the total variations on the partition squares at its endpoints. |
| [`ae_exists_correctedPlane_eq_add_const`](Rigidity/Proofs/Corrector/DarioCaseOneTwo.lean), [`isCorrectedPlane_of_harmonic`](Rigidity/Proofs/Corrector/DarioCaseOneTwo.lean), [`le_of_finite_piece`](Rigidity/Proofs/Corrector/DarioCaseOneTwo.lean) | Cases 1 and 2 of Step 2: almost surely, when the endpoints of the bond are not both in the infinite cluster with the bond closed, the corrected planes with the bond open and closed differ by a constant on that cluster (maximum principle on the finite piece cut off by the bond, and uniqueness of corrected planes). |
| [`edgeDiv_edgeGrad_setBond`](Rigidity/Proofs/Corrector/DarioFlipCluster.lean), [`ae_setBond`](Rigidity/Proofs/Corrector/DarioFlipCluster.lean) | the comparison of the configurations with one bond opened and closed: the Laplacians differ by the dipole of the bond times the increment across it, almost sure properties hold for both, and in Case 3 the two infinite clusters have the same vertices. |

The following theorems compose the results above with the proved multiscale Poincaré inequality, concentration inequality,
qualitative corrector input, order-zero regularity and (1.22) (`correctorOscSublinearTwo_holds`), in
[`Rigidity/Proofs/Poincare/DarioCorrectorBridges.lean`](Rigidity/Proofs/Poincare/DarioCorrectorBridges.lean).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Poincare.darioOptimalCorrectorTwo_of_threeThree`](Rigidity/Proofs/Poincare/DarioCorrectorBridges.lean), [`darioOptimalCorrectorTwo_of_flipSum`](Rigidity/Proofs/Poincare/DarioCorrectorBridges.lean) | Theorem 1 of Dario in `d = 2` (`DarioOptimalCorrectorTwo`) from `DarioLemmaThreeThree` alone, and from `DarioFlipSumBound` alone, by `darioLemmaThreeThree_of_flipSum`. |
| [`correctorQuantitativeInputTwo_of_threeThree`](Rigidity/Proofs/Poincare/DarioCorrectorBridges.lean), [`correctorQuantitativeInputTwo_of_flipSum`](Rigidity/Proofs/Poincare/DarioCorrectorBridges.lean) | `CorrectorQuantitativeInputTwo` (R5) from `DarioLemmaThreeThree` alone, and from `DarioFlipSumBound` alone. |
| [`armstrongDarioOrderOneOriginTwo_of_threeThree`](Rigidity/Proofs/Poincare/DarioCorrectorBridges.lean), [`armstrongDarioOrderOneOriginTwo_of_flipSum`](Rigidity/Proofs/Poincare/DarioCorrectorBridges.lean) | `ArmstrongDarioOrderOneOriginTwo` (R4) from `DarioLemmaThreeThree` alone, and from `DarioFlipSumBound` alone. |
| [`darioGuHeatKernelTwo_of_reduced_threeThree`](Rigidity/Proofs/Poincare/DarioCorrectorBridges.lean), [`darioGuHeatKernelTwo_of_reduced_flipSum`](Rigidity/Proofs/Poincare/DarioCorrectorBridges.lean) | `DarioGuHeatKernelTwo` (Dario and Gu, Theorem 1) from `DarioLemmaThreeThree`, respectively `DarioFlipSumBound`, and the named inputs of `darioGuHeatKernelTwo_of_reduced_dario` that do not concern Dario's Theorem 1: `hSec` (for each `p`, a `σ > 0` with `DarioGuApproxLemmaTwo`, `DarioGuTwoScaleErrorTwo` and `DarioGuDensityGaussianTwo`), `BarlowGaussianUpperBoundTwo` and `CarneVaropoulosTwo`. |

The thirty-five reports for the first table of this section and the eight reports for the bridges are in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Exactly the following named inputs remain for these results. Theorem 1 of Dario, R5 and R4: `DarioFlipSumBound` (or `DarioLemmaThreeThree`),
and nothing else; by [Steps 1 and 2 of Lemma 3.3 in flip form and Lemma 3.5 for the planar partition](#steps-1-and-2-of-lemma-33-in-flip-form-and-lemma-35-for-the-planar-partition),
`DarioFlipSumBound` follows from Lemma 3.5 in the adapted form `DarioResamplePartitionTwo`, which is proved, and the Step 2 sum (H2), so that Theorem 1 of Dario, R4 and R5 in `d = 2`
rest on (H2) alone (`DarioStepTwoSumBound`, `darioOptimalCorrectorTwo_of_stepTwo`); (H2) is proved (`darioStepTwoSumBound_holds`), so Theorem 1 of Dario, R5 and R4 in `d = 2` hold (`darioOptimalCorrectorTwo_holds`, `correctorQuantitativeInputTwo_holds`, `armstrongDarioOrderOneOriginTwo_holds`). Dario and Gu, Theorem 1: `DarioFlipSumBound` (or `DarioLemmaThreeThree`), `hSec`, `BarlowGaussianUpperBoundTwo` and
`CarneVaropoulosTwo`; the last has since been proved, and the inputs of Theorem 1 of Dario and Gu are given in
[Proposition A.7, Proposition 2.15, Lemma 4.1 and the weak Poincaré inequality](#proposition-a7-proposition-215-lemma-41-and-the-weak-poincaré-inequality).
The module [`DarioCorrectorPoincare`](Rigidity/Proofs/Poincare/DarioCorrectorPoincare.lean) states Theorem 1
from `ConcentrationTwo`, `CorrectorOscSublinearTwo` and `DarioLemmaThreeThree`, and
[`DarioCorrectorConcentration`](Rigidity/Proofs/Corrector/DarioCorrectorConcentration.lean) from the multiscale Poincaré inequality,
`CorrectorOscSublinearTwo` and `DarioLemmaThreeThree`; the bridges above discharge the remaining hypotheses.
Lemma 3.2 and (1.22) were proved before these files and are not restated by them.

Departures from Dario:

- **Flips in place of a doubled probability space.** For the Bernoulli law the variable `a_e` takes the values 0 and 1, so the conditional
  expectation given the other bonds is a two-point average, and the resampled configuration of (3.11)–(3.13) is replaced by the
  configurations `ω^{e,1}` and `ω^{e,0}` with the bond `e` open and closed: `𝕍[X] ≤ Σ_e (D_e X)²` with `D_e X = X(ω^{e,1}) − X(ω^{e,0})`.
- **Propositions 2.11 and 2.12 as an orthogonal projection.** The gradient of the Green function is the orthogonal projection onto the closed span of the gradients of
  point masses, which gives (2.14) with `C = 1`, (2.15) and (2.17) at once; potentials are built by sums along walks from the roots of the components.
- **The paths of (3.26).** The paths `γ_r` joining the anchors of neighbouring partition cubes are taken in the ninefold square of the smaller cube
  (`reachIn_planarAnchor_of_near`), in place of `□_𝒫(z) ∪ □_𝒫(z')`.
- **(3.22) in flip form.** It is proved for the corrected planes of `ω^{e,1}` and `ω^{e,0}`, the sublinear growth of the potential of the gradient of the Green function
  from the partition chains and the minimal scales with exponent `1/16`, and the increment (3.24) through the partition of `ω^{e,0}` without Lemma 3.5.

## Steps 1 and 2 of Lemma 3.3 in flip form and Lemma 3.5 for the planar partition

The estimate (3.13) in flip form, `DarioFlipSumBound`, is reduced to two statements, in
[`Rigidity/Proofs/Corrector/`](Rigidity/Proofs/Corrector/) (sixteen files `DarioHeatSquareSum`, `DarioResamplePartition`,
`DarioStepOneLocal`, `DarioFlipSplit`, `DarioStepTwoCases`, `DarioFlipSumTerms`, `DarioFlipSumReduce`, `DarioStepRegionSummable`,
`DarioFlipTermTwoSummable`, `DarioStepOneLipschitz`, `DarioStepOneMoments`, `DarioStepOneBound`, `DarioStepOneSum`,
`DarioStepOneGrowth`, `DarioStepOneW`, `DarioStepOneHolds`):

* Lemma 3.5 for the planar partition, in the adapted form `DarioResamplePartitionTwo` below, which is proved
  (`DarioResamplePartitionHolds`);
* the Step 2 sum (H2): for the conull sets `G` of the measurable corrector, for some `s, C > 0`, all `i, j`, `r ≥ 1` and `x`, the sum
  `flipSumTwo` over the bonds `e` of the squares `T₂(e)²` of the change-of-corrector terms of (3.15) is almost surely finite and
  `≤ O_s(C/r²)`.

`darioFlipSumBound_of_resample` is the implication from these two statements to `DarioFlipSumBound`. Hence Theorem 1 of Dario in
`d = 2`, `CorrectorQuantitativeInputTwo` (R5) and `ArmstrongDarioOrderOneOriginTwo` (R4) rest on the Step 2 sum (H2) alone
([`DarioStepTwoBridges`](Rigidity/Proofs/Poincare/DarioStepTwoBridges.lean)), and on nothing else of Lemma 3.3. The Step 2 sum (H2) is proved
([`DarioStepTwoHolds`](Rigidity/Proofs/Poincare/DarioStepTwoHolds.lean)). Dario derives it from Proposition 3.6 (the Meyers estimate with a divergence
source with the same exponent on the source and the gradient, of which Dario gives only a sketch in Appendix B), Lemma 3.7 and
Definition 3.8; that form of Proposition 3.6 fails on Bernoulli clusters, and the proof here uses the Meyers estimate with a divergence
source in the form of estimate (2) (`meyers_source`), summed over the almost sure partition into cubes whose children carry the
Meyers estimate and whose weights `W` of the Step 2 sum are bounded on average (`exists_stepTwoGood_partition`), the role of
Lemma 3.7 and Definition 3.8. In Step 2, Cases 1 and 2
are proved (the term vanishes) and Case 3 is the pairing of the table of
[Lemma 3.3 in flip form and the bridges to Theorem 1](#lemma-33-in-flip-form-and-the-bridges-to-theorem-1).

`DarioResamplePartitionTwo` is the statement that there are `C₀ > 0` and `C` such that, for each bond `e`, configurations `ω, ω'` on which
the planar partition is defined and which are equal off `e`, each endpoint `x` of `e` and each `z`: if `|z − x|_∞ < C₀ size(□_{𝒫(ω)}(x))`,
then `size(□_{𝒫(ω')}(z)) ≤ C size(□_{𝒫(ω)}(x))`; otherwise `□_{𝒫(ω')}(z) = □_{𝒫(ω)}(z)` and the anchors of this cube for `ω` and `ω'` agree.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Corrector.exists_tsum_latticeHeat_sq_le`](Rigidity/Proofs/Corrector/DarioHeatSquareSum.lean) | the square sum of the heat kernel of `ℤ²`: `Σ_y Φ_{r²}(x, y)² ≤ C/r²` for `r ≥ 1`, the form in `d = 2` of the bound on `Σ_y ζ_r(y)²` in the proof of Lemma 3.3. |
| [`Rigidity.Corrector.ResamplePartitionBound`](Rigidity/Proofs/Corrector/DarioResamplePartition.lean), [`DarioResamplePartitionTwo`](Rigidity/Proofs/Corrector/DarioResamplePartition.lean) | Lemma 3.5 for the planar partition with the anchors, as defined above (hypothesis, not proved). |
| [`Rigidity.Percolation.TriadicCube.planarAnchor_eq_of_agree_off`](Rigidity/Proofs/Corrector/DarioResamplePartition.lean), [`Rigidity.Corrector.planarPartCube_eq_and_anchor_eq_of_resample`](Rigidity/Proofs/Corrector/DarioResamplePartition.lean) | the anchor of a triadic cube depends only on the bonds inside its square of side nine times its own, and the two clauses of `ResamplePartitionBound` for the configurations `ω^{e,1}` and `ω^{e,0}`. |
| [`Rigidity.Corrector.resampleLocal_of_bound`](Rigidity/Proofs/Corrector/DarioStepOneLocal.lean), [`sq_tsum_partitionChange_le`](Rigidity/Proofs/Corrector/DarioStepOneLocal.lean) | Step 1, (3.16) in flip form: from Lemma 3.5 the change of partition is local (`ResampleLocal` with radius `C₀ s₀` and size `C s₀`), and the square of the sum of the weights times the change of the coarse gradient is at most the number of points of the box times the square sum of the weights over the box times the square of the total variation over a larger box. |
| [`Rigidity.Corrector.bondFlipDiff_heatCoarseComp_eq`](Rigidity/Proofs/Corrector/DarioFlipSplit.lean), [`sq_bondFlipDiff_heatCoarseComp_le`](Rigidity/Proofs/Corrector/DarioFlipSplit.lean) | the split (3.15) in flip form: the flip difference is the change of partition for the corrector with the bond open plus the change of corrector for the partition with the bond closed, and the square of the sum is at most twice the sum of the squares. |
| [`Rigidity.Corrector.ae_heatComp_coarse_sub_eq_zero`](Rigidity/Proofs/Corrector/DarioStepTwoCases.lean) | Step 2, Cases 1 and 2: almost surely, when the endpoints of the bond are not both in the infinite cluster with the bond closed, the change-of-corrector term (ii) of (3.15) is zero. |
| [`Rigidity.Corrector.bondFlipDiff_eq_flipTermOne_add_flipTermTwo`](Rigidity/Proofs/Corrector/DarioFlipSumTerms.lean), [`flipTermOne_eq_tsum_partitionChange`](Rigidity/Proofs/Corrector/DarioFlipSumTerms.lean), [`darioFlipSumBound_of_terms`](Rigidity/Proofs/Corrector/DarioFlipSumTerms.lean) | the terms `T₁, T₂` of (3.15), `D_e X = T₁ + T₂`, the sums `flipSumOne`, `flipSumTwo`, and `DarioFlipSumBound` from the bounds of the two sums. |
| [`Rigidity.Corrector.ae_flipSeries_summable`](Rigidity/Proofs/Corrector/DarioFlipSumReduce.lean), [`darioFlipSumBound_of_sums`](Rigidity/Proofs/Corrector/DarioFlipSumReduce.lean), [`ae_summable_heat_stepRegion`](Rigidity/Proofs/Corrector/DarioStepRegionSummable.lean), [`summable_heat_coarse_of_le`](Rigidity/Proofs/Corrector/DarioFlipTermTwoSummable.lean), [`ae_flipTermTwoSummable`](Rigidity/Proofs/Corrector/DarioFlipTermTwoSummable.lean) | the summability of the series of (3.15): the heat series over the anchor regions converge almost surely for the flips, by the second moments of the partition sizes, so that the series defining the terms are summable. |
| [`Rigidity.Corrector.darioFlipSumBound_of_stepSums`](Rigidity/Proofs/Corrector/DarioFlipTermTwoSummable.lean) | `DarioFlipSumBound` from the bounds `≤ O_s(C/r²)` of the two sums (H1) `flipSumOne` and (H2) `flipSumTwo`, with the finiteness. |
| [`Rigidity.Corrector.flipTermOne_sq_le`](Rigidity/Proofs/Corrector/DarioStepOneLipschitz.lean), [`flipTermOne_sq_le_of_bound`](Rigidity/Proofs/Corrector/DarioStepOneBound.lean), [`isOsBond_heatSqSum_of_moments`](Rigidity/Proofs/Corrector/DarioStepOneMoments.lean) | Step 1: `T₁(e)²` is bounded by Cauchy-Schwarz over the box and the Lipschitz bounds of the corrector, and a sum `Σ_y Φ_{r²}(x, y)² W(y)` with `E[W(y)^q] ≤ (A q^k)^q` uniformly in `y` is `O_s(C/r²)`. |
| [`Rigidity.Corrector.ae_flipSumOne_le`](Rigidity/Proofs/Corrector/DarioStepOneSum.lean), [`flipSumOne_isOsBond_of_moments`](Rigidity/Proofs/Corrector/DarioStepOneSum.lean) | the sums (3.18) `W(y) = Σ_e 1{y ∈ B_e} F_e` (`stepOneW`), `flipSumOne` almost surely at most the square sum against `W`, and (H1) from the moments of `W`. |
| [`Rigidity.Corrector.lintegral_tsum_rpow_le_of_decay`](Rigidity/Proofs/Corrector/DarioStepOneGrowth.lean), [`tsum_exp_neg_norm_bondBase_le`](Rigidity/Proofs/Corrector/DarioStepOneGrowth.lean), [`measure_le_mul_stoppingSize_le`](Rigidity/Proofs/Corrector/DarioStepOneGrowth.lean), [`lintegral_indicator_rpow_le`](Rigidity/Proofs/Corrector/DarioStepOneGrowth.lean), [`lintegral_randomBallSum_rpow_le_of_growth`](Rigidity/Proofs/Corrector/DarioStepOneGrowth.lean) | the moment tools of Step 1: Jensen's inequality over a countable family with exponentially decaying moments, the sum of the weights over the bonds, the tail of a multiple of the partition size, Cauchy-Schwarz on an event, and moments of sums over balls of random radius in growth form. |
| [`Rigidity.Corrector.stepOne_lipschitz_data`](Rigidity/Proofs/Corrector/DarioStepOneW.lean), [`stepOneFactor_eq_self`](Rigidity/Proofs/Corrector/DarioStepOneW.lean), [`measurable_stepOneFactorSelf`](Rigidity/Proofs/Corrector/DarioStepOneW.lean), [`stepOneFactorSelf_le`](Rigidity/Proofs/Corrector/DarioStepOneW.lean) | the Lipschitz bounds `Λ` of the corrector with `E[(1 + Λ)^q] ≤ (B q^κ)^q`, the local factor of Step 1 as a function of the configuration itself, and its bound on the partition event by the indicator of an event of exponentially small probability times the cube of a sum of `1 + Λ` over a ball. |
| [`Rigidity.Corrector.stepOneW_moments`](Rigidity/Proofs/Corrector/DarioStepOneHolds.lean) | `E[W(y)^q] ≤ (A q^k)^q` uniformly in `y`, for `k = 3(κ + 2) + 2`, for any `C₀` and `C`, with the hypothesis `ArmstrongDarioOrderZeroTwo`; it does not use `ResamplePartitionBound`. |
| [`Rigidity.Corrector.flipSumOne_isOsBond_of_resample`](Rigidity/Proofs/Corrector/DarioStepOneHolds.lean) | (H1): `flipSumOne` is almost surely finite and `O_s(C/r²)`, from `ResamplePartitionBound` alone. |
| [`Rigidity.Corrector.darioFlipSumBound_of_resample`](Rigidity/Proofs/Corrector/DarioStepOneHolds.lean) | `DarioFlipSumBound` from `DarioResamplePartitionTwo` and the Step 2 sum (H2). |
| [`Rigidity.Corrector.resamplePartitionBound_holds`](Rigidity/Proofs/Corrector/DarioResamplePartitionHolds.lean), [`darioResamplePartitionTwo_holds`](Rigidity/Proofs/Corrector/DarioResamplePartitionHolds.lean) | Lemma 3.5 for the planar partition: `ResamplePartitionBound 4747 14244`, from the planar resampling results of Percolation-Cluster-Homogenization (`meshedFlipBound_of_flip`, `planarPartCube_eq_of_meshedFlipBound`, `side_planarPartCube_le_of_meshedFlipBound`, `TriadicCube.planarAnchor_eq_of_adj_iff_vertices`). |
| [`Rigidity.Corrector.stepTwoWeight_le_weightMajorant`](Rigidity/Proofs/Corrector/DarioStepTwoWeightBound.lean), [`growthMoments_weightMajorant`](Rigidity/Proofs/Corrector/DarioStepTwoWeightMoments.lean), [`finiteWeight`](Rigidity/Proofs/Corrector/DarioStepTwoFiniteWeight.lean), [`stepTwoWeight_le_finiteWeight`](Rigidity/Proofs/Corrector/DarioStepTwoFiniteWeight.lean), [`cappedSide`](Rigidity/Proofs/Corrector/DarioStepTwoCapped.lean), [`siteGrad`](Rigidity/Proofs/Corrector/DarioStepTwoSiteGrad.lean) | the weight `W` of the Step 2 sum is at most `Σ_a 1{|a - u| ≤ 6κ σ(a)} T(a)⁹` with `T(a)` a ball sum of `1 + Λ` of radius `6κ σ(a)`, whose moments are `(A q^k)^q` uniformly in `u` when those of `1 + Λ` are; its finite-range version `W_R(u) = Σ_{v ∈ B(u, R)} 1{u ∈ B(v, 3κ cs(v))} 2 T_R(v)⁹`, built from the side of the planar partition capped at scale `⌊log₃ R⌋` and the local gradient bounds at the sites, is bounded by a power of `R`, depends only on the bonds inside `B(u, (3κ + 9)R + 1)` and dominates `W(u)` when no far edge reaches `u`, the capped sides are the sides near `u` and the local gradient bounds dominate the plane gradient bound near `u`. |
| [`Rigidity.Corrector.exists_lintegral_finiteWeight_rpow_le`](Rigidity/Proofs/Corrector/DarioStepTwoFiniteMoments.lean), [`measure_not_farGood_le`](Rigidity/Proofs/Corrector/DarioStepTwoFiniteProb.lean), [`measure_not_sideGood_le`](Rigidity/Proofs/Corrector/DarioStepTwoFiniteProb.lean), [`measure_not_gradGood_le`](Rigidity/Proofs/Corrector/DarioStepTwoFiniteProb.lean), [`measureReal_sum_cube_gt_le`](Rigidity/Proofs/Corrector/DarioStepTwoBlocks.lean), [`measurableSet_mem_stepTwoGood`](Rigidity/Proofs/Corrector/DarioStepTwoWeightMeas.lean) | the events on which the finite-range weight dominates the weight of the Step 2 sum fail with probability `8 (1 + 24κθ)² e^{-R/(12κθ)}`, `(2R + 1)² C e^{-c 3^{⌊log₃ R⌋}}` and `(2(R + 3κR) + 1)²` times the failure probability of the local gradient bound; `E[W_R(u)^q] ≤ M₀` uniformly in `R ≥ 1` and `u`; for variables in `[0, A]` with means at most `ε` depending on the bonds inside `B(u, ρ)`, `2ρ + 1 ≤ 3^m`, `P[|Q| t < Σ_Q X] ≤ 9^m exp(-9^j (t - (e - 1) ε)/A)` on `Q = ⟨m + j, c⟩`; the weight and the good cubes of the summation of estimate (2) are measurable. |
| [`Rigidity.Corrector.GrowthMoments.mul`](Rigidity/Proofs/Corrector/DarioGrowthMomentsOps.lean), [`growthMoments_of_exp_moment`](Rigidity/Proofs/Corrector/DarioGrowthMomentsOps.lean), [`pathWeight_le_ballSum`](Rigidity/Proofs/Corrector/DarioStepTwoPathBound.lean), [`planeGrad_le_of_lipschitz`](Rigidity/Proofs/Corrector/DarioStepTwoPathBound.lean), [`growthMoments_planarBallSum`](Rigidity/Proofs/Corrector/DarioStepTwoFinalMoments.lean) | moments `E[Y^q] ≤ (B q^κ)^q` pass to sums, multiples and products (Cauchy–Schwarz) and follow from `E[exp((X/θ)^s)] ≤ 2`; the path weight is at most `81σ(y)²` times a sum over the ball of radius `12σ(y)` of `c'(z) N'(z)`, `N'` the majorant of the weighted number of anchor regions; the plane gradient bound is at most `1 + 4Λ` under the bound `Λ` of the corrector increments; sums over balls of radius `12σ(y)` keep moments of polynomial growth. |
| [`Rigidity.Corrector.exists_stepTwoGood_partition`](Rigidity/Proofs/Corrector/DarioStepTwoPartition.lean), [`exists_measure_not_mem_stepTwoGood_le`](Rigidity/Proofs/Corrector/DarioStepTwoPartition.lean), [`exists_measure_not_weightGood_le`](Rigidity/Proofs/Corrector/DarioStepTwoWeightScale.lean), [`measure_not_domGood_le`](Rigidity/Proofs/Corrector/DarioStepTwoDomination.lean) | a vertex fails the domination of the Step 2 weight by its finite-range version with probability `C R⁴ e^{-c R^σ}`; with `R = 3^{⌊n/D⌋}`, `D = ⌈3 + 29q⌉` and residue classes modulo `3^{⌊n/D⌋ + 6κ + 21}`, a cube of scale `n` fails the weight bound `Σ_Q W^q ≤ M |Q|` with probability `C₁ e^{-c (3ⁿ)^{s₀}}`; together with the Meyers failure bound (Armstrong and Dario (3.17)) this is (2.2) for the good cubes of the summation of estimate (2), and Proposition 2.1 of Armstrong and Dario gives the almost sure partition into maximal good cubes with stretched exponential moments of the sizes. |
| [`Rigidity.Corrector.localGrad`](Rigidity/Proofs/Corrector/DarioLocalGradient.lean), [`planeGrad_le_localGrad`](Rigidity/Proofs/Corrector/DarioLocalGradientProb.lean), [`measure_not_localGradGood_le`](Rigidity/Proofs/Corrector/DarioLocalGradientProb.lean), [`ae_localGrad_le`](Rigidity/Proofs/Corrector/DarioLocalGradientMoments.lean), [`growthMoments_localGrad`](Rigidity/Proofs/Corrector/DarioLocalGradientMoments.lean) | a finite-range bound for the gradient of the corrector: the supremum, over the functions harmonic on the local cluster of `B(0, R)` (the points joined to the boundary of `B(0, 2R)` inside it) and within `3R` of a constant there, of their increments along the edges at the origin; it is at most `6R`, depends only on the open edges of `B(0, 2R + 1)`, dominates the corrector at the origin except with probability `(2R + 1)² C e^{-c √(R + 1)} + 2 e^{-(R/θ_R)^s}` (finite clusters and the quantitative sublinearity of the corrector), and is at most `L max(X, 2)² + 6R 1{finite cluster of at least R + 1 points at 0}` with `X` the minimal scale of the order-zero regularity, so that its moments are bounded uniformly in `R`. |
| [`Rigidity.Corrector.flipSumTwo_le_of_partition`](Rigidity/Proofs/Corrector/DarioStepTwoReduce.lean), [`tsum_weight_energy_le`](Rigidity/Proofs/Corrector/DarioCellSum.lean), [`sum_weight_energy_le_of_meyersCube`](Rigidity/Proofs/Corrector/DarioCellSum.lean), [`IsCellScale.le_of_mem_enl`](Rigidity/Proofs/Corrector/DarioCellGeometry.lean), [`tsum_clusterOpenEnergy_le`](Rigidity/Proofs/Corrector/DarioCellEnergy.lean), [`tsum_mul_edgeSq_le`](Rigidity/Proofs/Corrector/DarioStepTwoPaths.lean) | the summation of estimate (2) over a partition: on a cube with the Meyers estimate and `Σ W^q ≤ M |□|` (`q` conjugate to `p = 1 + ε/2`), `Σ_□ W E_v ≤ K (Σ_{3□} E_v + |□|^{1-1/p} Σ_{3□} Γ)` (Hölder and `meyers_source`); over a partition into triadic cubes with comparable neighbours (the collar of a cell meets cells of scale within one, overlap at most 48), `Σ_u W E_v ≤ K (Σ E_v + Σ_z (9^{n(z)})^{1-1/p} Γ(z))`; with `Σ E_v ≤ 2 Σ Γ` and the path count of the anchor paths, the Step 2 sum is at most `Σ_y Φ_{r²}(x, y)² K₀ (W(y) + 12 K |R(y)| Σ_{z ∈ R(y)} c(z) N(z))` whenever the cubes carrying the Meyers estimate on their children and the bound of the weight partition the lattice. |
| [`Rigidity.Corrector.ae_flipSumTwo_le`](Rigidity/Proofs/Corrector/DarioStepTwoSum.lean), [`ae_flipTermTwo_sq_le_closed`](Rigidity/Proofs/Corrector/DarioStepTwoWeight.lean), [`ae_flipTermTwo_sq_le_open`](Rigidity/Proofs/Corrector/DarioStepTwoOpenBound.lean), [`ae_dipoleCoeff_eq`](Rigidity/Proofs/Corrector/DarioStepTwoElectric.lean), [`ae_flipTermTwo_eq_open`](Rigidity/Proofs/Corrector/DarioStepTwoOpen.lean), [`ae_flipTermTwo_eq_walkSum`](Rigidity/Proofs/Corrector/DarioStepTwoSplit.lean) | the Step 2 sum of the proof of Lemma 3.3 of Dario bounded by a weighted energy: almost surely `Σ_e T₂(e)² ≤ K₀ (Σ_u W(u) E_v(u) + Σ_y W(y) Φ_{r²}(x, y)²)`, with `v` the potential of `P_ω γ_ω` on the infinite cluster, `E_v` its energy at a vertex and `W(u) = Σ_a 1{u ∈ B_a} R_a¹⁴ (Σ_{B_a} G)²` built from the sides of the partition cubes at the endpoints of the edges and a bound `G` for the gradient of the corrected plane of the actual configuration; through Case 3 per bond (the bond closed: `T₂ = (ℓ₁(x) - ℓ₁(y))(v(y) - v(x))`; the bond open: `(ℓ₀(x) - ℓ₀(y))((Pγ)(a) + Δ)` with `Δ` local by Lemma 3.5) and the relation `ℓ₀(x) - ℓ₀(y) = (1 + R)(ℓ₁(x) - ℓ₁(y))` by the effective resistance `R` of the configuration with the bond closed. |
| [`Rigidity.Corrector.meyers_source`](Rigidity/Proofs/Corrector/DarioMeyersSource.lean), [`openLaplacian_sub_eq_zero`](Rigidity/Proofs/Corrector/DarioMeyersSource.lean), [`sum_clusterEnergy_localSolution_le`](Rigidity/Proofs/Corrector/DarioMeyersSource.lean), [`greenProj_apply_of_not_open`](Rigidity/Proofs/Corrector/DarioMeyersSource.lean) | the Meyers estimate with a divergence source, used in place of Proposition 3.6 (which does not hold as printed, with the same exponent on the source and on the gradient): on a cube with the homogeneous Meyers estimate (`MeyersCube`), for `v` with `∇·∇v = ∇·ξ` inside `U₀ ⊆ 3□`, `avg_□ |∇v|^{2p} ≤ K ((avg_{3□} |∇v|²)^p + (S/|3□|)^p + S^p/|□|)`, `S` the squared norm of `ξ` on the open edges inside `U₀`; the local part is the Green projection of the configuration restricted to `U₀`. |
| [`Rigidity.Poincare.darioStepTwoSumBound_holds`](Rigidity/Proofs/Poincare/DarioStepTwoHolds.lean), [`darioOptimalCorrectorTwo_holds`](Rigidity/Proofs/Poincare/DarioStepTwoHolds.lean), [`correctorQuantitativeInputTwo_holds`](Rigidity/Proofs/Poincare/DarioStepTwoHolds.lean), [`armstrongDarioOrderOneOriginTwo_holds`](Rigidity/Proofs/Poincare/DarioStepTwoHolds.lean), [`exists_stepTwo_weight_data`](Rigidity/Proofs/Poincare/DarioStepTwoHolds.lean), [`darioGuHeatKernelTwo_of_sections_barlow`](Rigidity/Proofs/Poincare/DarioStepTwoHolds.lean), [`darioGuHeatKernelTwo_of_flux_gradient_barlow`](Rigidity/Proofs/Poincare/DarioStepTwoHolds.lean) | the Step 2 sum (H2) holds: almost surely `Σ_e T₂(e)² ≤ Σ_y Φ_{r²}(x, y)² W(y)` with `W(y)` built from the majorant of the Step 2 weight (from the corrector increments of Step 1) and a ball sum of the squared sizes of the good cubes times the weighted numbers of anchor regions, all with moments of polynomial growth uniform in `y`, so `Σ_e T₂(e)² = O_s(C/r²)`; hence Theorem 1 of Dario, R5 and R4 in dimension two, and Theorem 1 of Dario and Gu from `hSec` and the Gaussian upper bound of Barlow alone, or from Proposition 2.13, Theorem 3 and that bound. Dario's route through Proposition 3.6 with equal exponents is replaced by estimate (2). |
| [`Rigidity.Assembly.WithPlanarInputs.fast_decay_of_greenQuantitative`](Rigidity/Proofs/Assembly/PlanarDarioGu.lean), [`fast_decay_of_darioGu`](Rigidity/Proofs/Assembly/PlanarDarioGu.lean), [`fast_decay_of_sections_barlow`](Rigidity/Proofs/Assembly/PlanarDarioGu.lean), [`fast_decay_of_flux_gradient_barlow`](Rigidity/Proofs/Assembly/PlanarDarioGu.lean) | Theorem 1.3 in dimension two from `SupercriticalBondGreenQuantitativeTwo` alone, from `DarioGuHeatKernelTwo` alone, from `hSec` and `BarlowGaussianUpperBoundTwo`, or from `DarioGuFluxWeakNormTwo`, `DarioGuGradientBoundTwo` and `BarlowGaussianUpperBoundTwo`: of the five planar inputs of `fast_decay_of_planar_estimates`, the corrector inputs R2 and R5 and the regularity of orders zero and one are proved. |
| [`Rigidity.Poincare.DarioStepTwoSumBound`](Rigidity/Proofs/Poincare/DarioStepTwoBridges.lean), [`darioFlipSumBound_of_stepTwo`](Rigidity/Proofs/Poincare/DarioStepTwoBridges.lean), [`darioOptimalCorrectorTwo_of_stepTwo`](Rigidity/Proofs/Poincare/DarioStepTwoBridges.lean), [`correctorQuantitativeInputTwo_of_stepTwo`](Rigidity/Proofs/Poincare/DarioStepTwoBridges.lean), [`armstrongDarioOrderOneOriginTwo_of_stepTwo`](Rigidity/Proofs/Poincare/DarioStepTwoBridges.lean), [`darioGuHeatKernelTwo_of_reduced_stepTwo`](Rigidity/Proofs/Poincare/DarioStepTwoBridges.lean), [`darioGuHeatKernelTwo_of_flux_gradient_barlow_stepTwo`](Rigidity/Proofs/Poincare/DarioStepTwoBridges.lean) | the Step 2 sum (H2) as a named statement, and `DarioFlipSumBound`, Theorem 1 of Dario (`DarioOptimalCorrectorTwo`), R5, R4 and Theorem 1 of Dario and Gu (with its further inputs) from it. |

The reports for the declarations of this section, for Lemma 3.5 and for the bridges from (H2) are in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Departures from Dario:

- **Flips.** As in the section above, the configurations `ω^{e,1}` and `ω^{e,0}` replace the doubled probability space; Step 1 and the split (3.15)
  are proved for them, and the expectation under a flip is bounded by `p^{-1}` times the expectation (the form of (3.12)).
- **Moments in place of `ζ_r`.** The bounds (3.17) to (3.19) by the supremum and infimum of the weights `ζ_r` and the calculus of the random
  radii `O_s` are replaced by the moments of the sums (3.18): the Lipschitz bounds of the corrector, with `E[(1 + Λ)^q] ≤ (B q^κ)^q`, a bound of
  the local factor by the cube of a sum over a ball, Jensen's inequality over the bonds with weights decaying exponentially in the distance, and
  moments of order `q` of the sums over balls. Only the bound `Σ_y Φ_{r²}(x, y)² ≤ C/r²` of the weights is used.
- **Cauchy-Schwarz over the box.** In Step 1 the square of the sum over the box of radius `C₀ s₀` is bounded by Cauchy-Schwarz, by the number
  of points of the box times the sum of the squares; the ball `B(x, r)` is the box in the supremum norm.
- **Lemma 3.5 with the anchors.** The anchors of the planar partition depend on the bonds of the square of side nine times the side of the cube, so
  `DarioResamplePartitionTwo` states the second clause for the cube and for its anchor. For a meshed partition cube of side at least 1000 the anchor
  depends only on the bonds inside the cube, so `DarioResamplePartitionTwo` is equivalent to Lemma 3.5 as Dario prints it, for this partition.
- **The proof of Lemma 3.5.** Dario's proof uses large cubes crossable by clusters avoiding a cube, which the strip meshes of this partition do not
  provide. Here, with `s` the side of the partition cube of an endpoint `x` of the bond, the square of side `s` around `x` is tested in the mesh of that
  cube; by planar duality a change of a crossing of a strip of width at least `s + 2` would give a walk of faces through closed edges from the bond
  leaving that square, which its outer strip crossings block. So the meshed cubes change only for cubes of side below `101 s` near `x`, the stopping
  cubes only near `x`, and the partition cubes agree at distance at least `4747 s` and have side at most `14244 s` closer to `x`; the constants are
  explicit.

## Theorem 1 of Dario and Gu in dimension two

Theorem 1 of Dario and Gu (quantitative local limit theorem for the heat kernel of the infinite cluster), in the form
`DarioGuHeatKernelTwo` (`d = 2`, for `t ≥ 1`, with a diffusivity `σ > 0`), is proved in
[`Rigidity/Proofs/Green/`](Rigidity/Proofs/Green/) by the induction of Section 4.3 over the exponents of (4.43)
([`darioGuHeatKernelTwo_of_reduced`, `darioGuHeatKernelTwo_of_reduced_dario`](Rigidity/Proofs/Green/DarioGuTheoremOneReduced.lean)),
from the following named inputs, for each `𝔭_c(2) < p < 1` and some `σ > 0`:

* Lemma 4.1 (`DarioGuApproxLemmaTwo p σ`, in the form of the iteration step used at (4.45)), Proposition 4.3
  (`DarioGuTwoScaleErrorTwo p σ`) and Proposition A.7 (`DarioGuDensityGaussianTwo p σ`, the Gaussian mass of the
  infinite cluster), which Dario and Gu prove from Sections 3 and 4.1–4.2 and Appendix A. The second part (A.13) of
  Proposition A.7 is proved, and Lemma 4.1 is proved from Theorem 3 (Remark 1.3) and Theorem 4
  ([Proposition A.7, Proposition 2.15, Lemma 4.1 and the weak Poincaré inequality](#proposition-a7-proposition-215-lemma-41-and-the-weak-poincaré-inequality));
  Proposition 4.3 is proved from the flux estimate of Proposition 2.13 (`DarioGuFluxWeakNormTwo p σ`, proved, see
  [Proposition 2.13 of Dario and Gu in dimension two](#proposition-213-of-dario-and-gu-in-dimension-two)) and the
  quantitative corrector estimate, in
  [Proposition 4.3 of Dario and Gu in dimension two](#proposition-43-of-dario-and-gu-in-dimension-two);
* the Gaussian upper bound of Barlow, Theorem 4 (`BarlowGaussianUpperBoundTwo`, cited by Dario and Gu, proved in
  [The Gaussian upper bound of Barlow in dimension two](#the-gaussian-upper-bound-of-barlow-in-dimension-two)), and the
  Carne–Varopoulos bound of Proposition 2.15 (`CarneVaropoulosTwo`, proved, see the same section);
* the qualitative corrector input `SupercriticalBondCorrectorInputTwo` (R2) and the quantitative corrector estimate
  of Proposition 2.12 (`CorrectorQuantitativeInputTwo`, R5), the latter by `correctorQuantitativeInputTwo_of_inputs` of
  [Theorem 1 of Dario in dimension two](#theorem-1-of-dario-in-dimension-two) or from `DarioOptimalCorrectorTwo`
  (`darioGuHeatKernelTwo_of_reduced_dario`).

Lemma 3.11 (Lemma 8.9 of Armstrong, Kuusi and Mourrat, `AKMLemmaEightNineTwo`) is stated, since it is used in the
proof of Proposition 3.9, which is a named statement; Theorem 3 is proved from Proposition 3.9 and Theorem 4 in
[Theorem 3 of Dario and Gu in dimension two from Proposition 3.9](#theorem-3-of-dario-and-gu-in-dimension-two-from-proposition-39).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Green.darioGuHeatKernelTwo_of_sections`](Rigidity/Proofs/Green/DarioGuTheoremOne.lean), [`darioGuHeatKernelTwo_of_reduced`](Rigidity/Proofs/Green/DarioGuTheoremOneReduced.lean), [`darioGuHeatKernelTwo_of_reduced_dario`](Rigidity/Proofs/Green/DarioGuTheoremOneReduced.lean) | Theorem 1 of Dario and Gu in `d = 2` from `DarioGuSectionFourTwo p σ` (all five statements of Section 4), and from Lemma 4.1, Proposition 4.3 and Proposition A.7 with the inputs above. |
| [`darioGuCorrectorLemmaTwo_of_inputs`](Rigidity/Proofs/Green/DarioGuCorrectorLemma.lean) | Lemma 4.2 of Dario and Gu in `d = 2`, `\|v(t, x, τ, y)\| ≤ C τ^{−1/2+α/2} Φ_C(t, x − y)`, from Proposition 2.12, Theorem 4 at the points near `y`, Proposition 2.15 at the far points and the semigroup property (3.2) of `Φ_C`. |
| [`darioGuTwoScaleInitialTwo_of_correctorQuantitative`](Rigidity/Proofs/Green/DarioGuTwoScaleInitial.lean) | the estimate of the two-scale initial error `h − p̄/θ` of Section 4.3 (the term of (4.47) that the source leaves to the reader) from Proposition 2.12. |
| [`heatLevel_step`](Rigidity/Proofs/Green/DarioGuStep.lean), [`pointwise_of_weightedL2`](Rigidity/Proofs/Green/DarioGuPointwise.lean) | the iteration step of Section 4.3: the statement (4.45) at an exponent `k ≤ 1/2 − δ` implies it at `min((1 − κ) k + κ/2, 1/2 − δ)`, through the weighted `L²` estimate (4.49) and the pointwise estimate (4.48). |
| [`hasSum_vsrwHeat_mul`](Rigidity/Proofs/Green/OpenHeatSemigroup.lean), [`sum_dgPhi_mul_dgPhi_le`](Rigidity/Proofs/Green/DarioGuPhiConvolution.lean), [`hasTail_latticeSup`](Rigidity/Proofs/Green/DarioGuLatticeSup.lean) | the semigroup property of the heat kernel of the variable speed random walk, the semigroup bound (3.2) of `Φ_C`, and the tail of the lattice minimal time of a family of minimal times with a uniform stretched exponential tail (3.52), (4.44). |

The ten reports for the declarations of this section are in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Departures from Dario and Gu:

- The functions `q` and `v` are defined by the semigroup formula, and the corrector is normalized by `χ(y) = 0` for
  `y ∈ 𝒞_∞`.
- Lemma 4.1 is used in the input form of the proof of the induction at (4.7) (DG21.tex:2618): `ε Φ_C(τ, ·)` is replaced
  by `C(ε (τ/t)^{1/2} + τ^{−1/2+α}) Φ_C(t, ·)`.
- The minimal times of the three propositions are merged into one `M` with `τ ≥ M` and `t ≥ 3τ`; the sequence `κ_n`
  starts at `k₀ = 0`, with `k₁` the exponent `κ₀` of Dario and Gu; the scale `T_par` of (4.44) is the lattice supremum of
  the point times (`hasTail_latticeSup`); and the statement is proved for `t ≥ 8`.
- Proposition A.7, printed for lattice centres `y ∈ ℤ^d`, is used at the centre `(x + z)/2` of (4.48) (DG21.tex:2602);
  here the centre is rounded to a lattice point and the Lipschitz bound of the Gaussian kernel summed over the lattice
  is used (`DarioGuGaussian`).

Points in the source that are not detailed, and an issue of normalization, with their numbers in the compiled source:

- the estimate of the term `h − p̄/θ` in the proof of (4.47) (DG21.tex:2556-2562) is left to the reader, as are details
  of Proposition 4.3 (DG21.tex:2274, :2411) and the proofs of Propositions 2.9 and 2.11 (DG21.tex:1018, :1053);
- Theorem 4, stated for the constant speed random walk with conductances `0` or `1`, is used for the variable speed
  walk (DG21.tex:1252);
- the weighted `L²` bounds (4.3), (4.24), (4.46) and (4.49), with the weight `exp(Ψ_C)`, `Ψ_C = −ln Φ_C` (3.3), carry
  the normalization `t^{d/2}` differently from the Gaussian factor `exp(|x|²/(Ct))` used in (4.48); the Lean weight is
  `exp(dgExponent)`;
- the decomposition (4.47) has `+w` where `w := h − v − q` gives `−w` (compare DG21.tex:1944-1948).

## Proposition A.7, Proposition 2.15, Lemma 4.1 and the weak Poincaré inequality

Four inputs of the induction of Section 4.3 of Dario and Gu are proved in dimension two, in
[`Rigidity/Proofs/Green/`](Rigidity/Proofs/Green/), for each `𝔭_c(2) < p < 1`:

* **Proposition A.7, second part (A.13)** (`darioGuDensityGaussianTwo_holds`, `DarioGuDensityGaussianTwo p σ` for every
  `σ > 0`): for every `α > 0` and `t > T_dense,α(y)`, the sum over the whole infinite cluster of the Gaussian kernel is within
  `C t^{−(1/2 − α)}` of `θ(p)`. The first part (A.12) is not formalized. The proof starts from
  the concentration of the density of Proposition A.1 (`cluster_density_concentration`): the Gaussian kernel is telescoped
  over the averages on the triadic cubes of the scales `3^k ≤ √t` (`abs_sum_mul_le_multiscale`); the scales below `t^α`
  are bounded trivially, the larger ones by a union bound over the cubes with Proposition A.1 and Markov's inequality
  (`exists_minimalScale_of_summable`); the oscillation of the Gaussian kernel and its lattice sums are bounded directly,
  and the mass of the Gaussian kernel on the lattice is within `C t^{−1/2}` of 1, for `t ≥ 1`, through the Poisson summation formula
  (`Real.tsum_exp_neg_mul_int_sq`).
* **Proposition 2.15** (`carneVaropoulosTwo_holds`, `CarneVaropoulosTwo`, with `C = 200`): for `|x − y| ≤ t` the lazy
  Carne bound (`lazyPow_le_carneVaropoulos`) for the steps `n` below `16t + 2^{−16t} e^{4t}`, for `t ≤ r ≤ 256t` the
  bound `openHeat_le_exp_of_le_norm`, and for `r > 256t` the finite speed of propagation with the Poisson tail
  `θ^{−r} e^{4t(θ−1)}`, `θ = r/(4t)`.
* **Proposition 2.7, weak form, for `p = 2`** (`clusterPoincareTwo_holds`, `ClusterPoincareTwo`): for the ball `B_R(y)` of
  the infinite cluster and `u` on the cluster,
  `‖u − (u)‖_{L̲²(B_R)} ≤ C R ‖∇u‖_{L̲²(𝒞_∞ ∩ B_{24R}(y))}`, with the gradient on the ball of radius `24R` and the constant
  `C` and the dilation `24` separate. It is proved from the Sobolev inequality of Armstrong and Dario, Proposition 3.4,
  on resolved triple cubes, the concentration of the stopping sizes of the partition into coarsely good cubes through a
  minimal scale, and the lower bound on the volume of the cluster in balls from Proposition A.1.
* **Lemma 4.1** (`darioGuApproxLemmaTwo_of_gradient`, `DarioGuApproxLemmaTwo p σ` for every `σ > 0`): from Theorem 3 in the
  form of Remark 1.3 (`DarioGuGradientBoundTwo`, with the gradient on the edges inside the ball) and Theorem 4 (Barlow),
  with Proposition 2.15, the weak Poincaré inequality and Proposition A.7 proved
  (`darioGuApproxLemmaTwo_of_inputs` takes the weak Poincaré inequality and Proposition 2.15 as hypotheses).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Green.darioGuDensityGaussianTwo_holds`](Rigidity/Proofs/Green/DarioGuDensityGaussian.lean) | Proposition A.7, second part (A.13), of Dario and Gu in `d = 2`, for `t > T_dense(y)`, as a sum over the whole cluster. |
| [`Rigidity.Green.carneVaropoulosTwo_holds`](Rigidity/Proofs/Green/PlanarCarneVaropoulos.lean) | `CarneVaropoulosTwo`, Proposition 2.15 of Dario and Gu in `d = 2`. |
| [`Rigidity.Green.clusterPoincareTwo_holds`](Rigidity/Proofs/Green/DarioGuPoincareHolds.lean) | `ClusterPoincareTwo`, Proposition 2.7 of Dario and Gu for `p = 2` in `d = 2` with the gradient on the larger ball. |
| [`Rigidity.Green.darioGuApproxLemmaTwo_of_inputs`](Rigidity/Proofs/Green/DarioGuApproxLemma.lean), [`Rigidity.Green.darioGuApproxLemmaTwo_of_gradient`](Rigidity/Proofs/Green/DarioGuTheoremOnePoincare.lean) | Lemma 4.1 of Dario and Gu in `d = 2` from Theorem 3 (Remark 1.3), the Poincaré inequality, Theorem 4 and Proposition 2.15, and from Theorem 3 and Theorem 4 alone. |
| [`Rigidity.Green.darioGuHeatKernelTwo_of_approx_twoScale`](Rigidity/Proofs/Green/DarioGuTheoremOneDensity.lean), [`darioGuHeatKernelTwo_of_twoScale_gradient`](Rigidity/Proofs/Green/DarioGuTheoremOneApprox.lean), [`darioGuHeatKernelTwo_of_twoScale_gradient_barlow`](Rigidity/Proofs/Green/DarioGuTheoremOneCarne.lean), [`darioGuHeatKernelTwo_of_twoScale_gradient_barlow_poincare`](Rigidity/Proofs/Green/DarioGuTheoremOnePoincare.lean) and the variants `_dario` | Theorem 1 of Dario and Gu in `d = 2` with Proposition A.7 proved and Lemma 4.1 replaced by Theorem 3, then with the Poincaré inequality and Proposition 2.15 proved as well; the variants with `_dario` take `DarioOptimalCorrectorTwo` in place of `CorrectorQuantitativeInputTwo`. |
| [`Rigidity.Poincare.darioGuHeatKernelTwo_of_twoScale_gradient_barlow_threeThree`](Rigidity/Proofs/Poincare/DarioGuBridges.lean), [`darioGuHeatKernelTwo_of_twoScale_gradient_barlow_flipSum`](Rigidity/Proofs/Poincare/DarioGuBridges.lean) | Theorem 1 of Dario and Gu in `d = 2` from `DarioLemmaThreeThree`, respectively `DarioFlipSumBound`, and the three inputs below. |

The fifteen reports for the declarations of this section are in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Exactly the following named inputs remain for Theorem 1 of Dario and Gu in `d = 2`
(`darioGuHeatKernelTwo_of_twoScale_gradient_barlow_threeThree`; with Proposition 4.3 proved, see
[Proposition 4.3 of Dario and Gu in dimension two](#proposition-43-of-dario-and-gu-in-dimension-two) for the shorter list): Proposition 4.3, for each `𝔭_c(2) < p < 1` and some
`σ > 0` (`DarioGuTwoScaleErrorTwo p σ`); Theorem 3 in the form of Remark 1.3 (`DarioGuGradientBoundTwo`); Theorem 4 of
Barlow (`BarlowGaussianUpperBoundTwo`, cited); and `DarioLemmaThreeThree` (Lemma 3.3 of Dario), or `DarioFlipSumBound` in its place
(`darioGuHeatKernelTwo_of_twoScale_gradient_barlow_flipSum`). The qualitative corrector input is proved, and Proposition 2.15, Proposition A.7,
Lemma 4.1 and the Poincaré inequality are no longer inputs.

Departures from Dario and Gu:

- **Proposition A.7**: only the second part (A.13) is formalized, as printed; the first part (A.12), which is stated for every
  `t > 0` and holds for `t ≥ 1`, is not. The route is the telescoping over triadic averages from Proposition A.1 described above, in place of the exponential
  Efron–Stein inequality (Proposition A.3, cited) with (A.5), (A.6) and Lemma A.4; the exponent is `α s₀/2`, `s₀ = 2/15`, with
  `α > 1/4` reduced to `1/4`, and the scale `T_dense = max(81, M^{1/α})`.
- **Proposition 2.7** is proved in a weak form with the gradient on the larger ball,
  `‖u − (u)‖_{L̲²(B_R)} ≤ C R ‖∇u‖_{L̲²(𝒞_∞ ∩ B_{24R}(y))}`, in place of the gradient on the edges inside `B_R(y)`; the constant `C` and
  the dilation `24` are separate. It is proved for `p = 2`, the case used.
- **Proposition 2.15** is proved for the lazy walk with `C = 200`, by finite speed and a Poisson tail at large distances,
  in place of the argument of Davies cited by Dario and Gu.
- **Lemma 4.1** is proved from Theorem 3 in the form of Remark 1.3 (the gradient on the edges inside the ball), used at the
  radius `24R` of the weak Poincaré inequality. The lower bound on the volume of the cluster in balls at the scale `√τ` comes
  from Proposition A.1, and for `|x − y| > t − τ`, where Theorem 3 does not apply, `Φ_C(t, r) ≤ C t^{−1/2} Φ_{2C}(t, r)` is
  used. The minimal time is `T = max(M_reg², M_P², M_dens², 2 max(T_dense, 1), T'_NA, 1)` in place of `max(M_reg², T_dense)`.

## Proposition 4.3 of Dario and Gu in dimension two

Proposition 4.3 of Dario and Gu (the two-scale error bound, `DarioGuTwoScaleErrorTwo p σ`) is proved in
[`Rigidity/Proofs/Green/`](Rigidity/Proofs/Green/) from two statements: the estimate of the flux in the weak norm, Proposition 2.13
(`DarioGuFluxWeakNormTwo p σ`, proved in
[Proposition 2.13 of Dario and Gu in dimension two](#proposition-213-of-dario-and-gu-in-dimension-two), the estimate (1.33) of
`Rigidity.Green.WeakNormLe` for the centered flux on the balls
of the infinite cluster), and the quantitative corrector estimate of Proposition 2.12 (`CorrectorQuantitativeInputTwo`, R5, which
follows from Lemma 3.3 of Dario). The witness is `σ = σ̄²`, where `σ̄` is the constant that Proposition 2.13 defines through (B.5).
The proof follows Steps 1 to 5 of the source (DG21.tex, proof of Proposition 4.3): the heat flow of the two-scale expansion and its
equation (Step 1), the weighted energy inequality (Step 2), the source terms (Steps 3 and 4), the two Gronwall passes (Step 5, bound
(4.40)), and the assembly on the cluster with the truncated weights.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Green.DarioGuFluxWeakNormTwo`](Rigidity/Proofs/Green/DarioGuFluxInput.lean), [`WeakNormLe`](Rigidity/Proofs/Green/DarioGuFluxInput.lean), [`centeredFlux`](Rigidity/Proofs/Green/DarioGuFluxInput.lean) | Proposition 2.13: the weak norm of the centered flux of the corrector on the balls of the cluster at all scales above a random minimal scale (proved, `darioGuFluxWeakNormTwo_holds`). |
| [`weakNormLe_translatedFlux`](Rigidity/Proofs/Green/DarioGuFluxTranslate.lean), [`darioGuTranslatedFluxTwo_of_inputs`](Rigidity/Proofs/Green/DarioGuFluxTranslateHolds.lean) | Remark B.3: the weak norm bound of the translated flux of the source from the bound for the centered flux. |
| [`dgWeight_bound`](Rigidity/Proofs/Green/DarioGuTwoScaleWeight.lean), [`dgWeightTrunc_edgeKappa_bound`](Rigidity/Proofs/Green/DarioGuTwoScaleWeightTrunc.lean) | the weight `exp(dgExponent)` and its truncation: the discrete product rule and the pointwise bound replacing (4.27) and (4.41). |
| [`openLaplacian_twoScale`](Rigidity/Proofs/Green/DarioGuTwoScaleStepOne.lean), [`openLaplacian_twoScale_of_corrector`](Rigidity/Proofs/Green/DarioGuTwoScaleCorrectorEq.lean), [`hasDerivAt_dgTwoScale_eq`](Rigidity/Proofs/Green/DarioGuTwoScaleHeatEq.lean) | Step 1, (4.26): the equation of the two-scale expansion with the flux of the corrector as source. |
| [`tsum_energy_deriv_le`](Rigidity/Proofs/Green/DarioGuTwoScaleStepTwo.lean), [`energy_first_pass`](Rigidity/Proofs/Green/DarioGuTwoScaleStepFive.lean), [`energy_second_pass`](Rigidity/Proofs/Green/DarioGuTwoScaleStepFive.lean) | Step 2 (the weighted energy inequality) and Step 5: the bound (4.40) in two Gronwall passes. |
| [`abs_fwdDiff_fwdDiff_latticeGaussian_le`](Rigidity/Proofs/Green/DarioGuGaussianLatticeDiff.lean), [`abs_fwdDiff_latticeGaussianTimeDeriv_le`](Rigidity/Proofs/Green/DarioGuGaussianLatticeDiff.lean), [`abs_fwdDiff_fwdDiff_fwdDiff_latticeGaussian_le`](Rigidity/Proofs/Green/DarioGuGaussianLatticeThird.lean) | the discrete derivatives of the lattice Gaussian: `\|D_iD_kP\| ≤ K r^{-2}Φ`, `\|D_k∂P\| ≤ K r^{-5/2}Φ` and the third differences. |
| [`tsum_weightGauss_le`](Rigidity/Proofs/Green/DarioGuTwoScaleMomentSum.lean), [`tsum_sq_clusterF_le`](Rigidity/Proofs/Green/DarioGuTwoScaleStepFour.lean), [`tsum_sq_clusterFlux_le`](Rigidity/Proofs/Green/DarioGuTwoScaleStepFour.lean) | Step 4: the Gaussian moment sum and the bounds `Σ(ψ f)² ≤ Q r^{β-4}` of the field `f`, and `r^{β-3}`, `r^{β-4}` for the field `F`. |
| [`neg_sum_le_of_weakNormLe`](Rigidity/Proofs/Green/DarioGuTwoScaleFluxDuality.lean), [`neg_tsum_le_of_weakNormLe_coeff`](Rigidity/Proofs/Green/DarioGuTwoScaleFluxScale.lean), [`neg_tsum_le_of_pieces`](Rigidity/Proofs/Green/DarioGuTwoScaleFluxSum.lean), [`neg_tsum_flux_le`](Rigidity/Proofs/Green/DarioGuTwoScaleFluxBound.lean) | Step 3, (4.32) and (4.33)-(4.35): duality of the weak norm, one dyadic scale with the product rule, the truncated sum over the scales with dominated convergence, and the bound for each component of the flux. |
| [`tsum_source_le_of_split`](Rigidity/Proofs/Green/DarioGuTwoScaleSourceSplit.lean), [`darioGuTwoScaleSourceBoundTwo_of_fluxTerm`](Rigidity/Proofs/Green/DarioGuTwoScaleSourceBound.lean) | the bound of the source of the equation by the split into the flux term and the terms of Step 4. |
| [`clusterW_first_pass`](Rigidity/Proofs/Green/DarioGuTwoScaleAssembly.lean), [`clusterW_second_pass`](Rigidity/Proofs/Green/DarioGuTwoScaleAssembly.lean), [`dgW_weightedL2Le_of_sourceBound`](Rigidity/Proofs/Green/DarioGuTwoScaleAssembly.lean), [`darioGuTwoScaleErrorTwo_of_sourceBound`](Rigidity/Proofs/Green/DarioGuTwoScaleErrorFromSource.lean), [`darioGuTwoScaleErrorTwo_of_fluxTerm`](Rigidity/Proofs/Green/DarioGuTwoScaleSourceBound.lean) | the assembly on the cluster: the weighted `L²` bound from the source bound, and `DarioGuTwoScaleErrorTwo` from it. |
| [`darioGuTwoScaleFluxTermTwo_of_inputs`](Rigidity/Proofs/Green/DarioGuTwoScaleFluxTerm.lean), [`darioGuTwoScaleErrorTwo_of_inputs`](Rigidity/Proofs/Green/DarioGuTwoScaleFluxTerm.lean) | Step 3 and Proposition 4.3 from `CorrectorQuantitativeInputTwo` and `DarioGuFluxWeakNormTwo p σ`. |
| [`exists_darioGuTwoScaleErrorTwo_of_inputs`](Rigidity/Proofs/Green/DarioGuTwoScaleFluxTerm.lean) | Proposition 4.3 in the form `hP43` of Theorem 1 of Dario and Gu: at every `𝔭_c(2) < p < 1` some `σ > 0` satisfies `DarioGuTwoScaleErrorTwo p σ`, from `CorrectorQuantitativeInputTwo` and `DarioGuFluxWeakNormTwo p σ` at some `σ > 0`. |
| [`Rigidity.Poincare.darioGuHeatKernelTwo_of_flux_gradient_barlow_threeThree`](Rigidity/Proofs/Poincare/DarioGuFluxBridges.lean), [`darioGuHeatKernelTwo_of_flux_gradient_barlow_flipSum`](Rigidity/Proofs/Poincare/DarioGuFluxBridges.lean), [`darioGuHeatKernelTwo_of_flux_gradient_barlow_resample`](Rigidity/Proofs/Poincare/DarioGuFluxBridges.lean) | Theorem 1 of Dario and Gu in `d = 2` from the inputs listed below. |

The thirty-three reports for the declarations of this section are in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

The following named inputs were the hypotheses of Theorem 1 of Dario and Gu in `d = 2`
(`darioGuHeatKernelTwo_of_flux_gradient_barlow_threeThree`): Proposition 2.13, for each `𝔭_c(2) < p < 1` and some `σ > 0`
(`DarioGuFluxWeakNormTwo p σ`, now proved, `darioGuFluxWeakNormTwo_holds`, so that Theorem 1 of Dario and Gu follows from Theorem 3 and
Theorem 4 alone, `darioGuHeatKernelTwo_of_gradient_barlow`); Theorem 3 in the form of Remark 1.3 (`DarioGuGradientBoundTwo`); Theorem 4 of Barlow
(`BarlowGaussianUpperBoundTwo`, cited); and `DarioLemmaThreeThree` (Lemma 3.3 of Dario), or `DarioFlipSumBound` in its place
(`darioGuHeatKernelTwo_of_flux_gradient_barlow_flipSum`), or Lemma 3.5 for the planar partition (`DarioResamplePartitionTwo`)
together with the Step 2 sum (H2) (`darioGuHeatKernelTwo_of_flux_gradient_barlow_resample`, by `darioFlipSumBound_of_resample`).
Proposition 4.3 and the quantitative corrector estimate are no longer inputs.

Departures from Dario and Gu:

- **The centered flux in place of the translated flux.** Step 3 uses the centered flux of the corrector, paired with the forward
  second differences `D_iD_kP` of the heat kernel, in place of the translated flux and the backward differences of the source;
  Remark B.3 (the translated flux, `darioGuTranslatedFluxTwo_of_inputs`) is proved, so the bound for the translated flux follows from Proposition 2.13.
- **The weight (4.27) by the edge identity.** The comparison (4.27) of the gradient of the weight at neighbouring points, with a constant
  `C̃`, does not hold for the weight `exp(Ψ_C)` at distances `r ≫ t`. It is replaced by the discrete product rule
  `(q²b − p²a)(b − a) = (qb − pa)² − (q − p)²ab` on the edges and the pointwise bound `ψ²(∂_t g/C + A/t) + K max_{|r'−r|≤1}(ψ(r') − ψ(r))² ≤ C₁/t`
  for `t ≥ 1` and `C ≥ C₀(K)`, which gives (4.41). The weight is `exp(dgExponent C t r)`, the exponent of `Φ_C` alone, without the factor `t^{d/2}/C` of `Ψ_C`,
  with which (4.41) fails because of the term `ψ²/t`.
- **Steps written out.** The source leaves to the reader the details of (4.26), of the term `Ξ₂` of Step 3 (the bounds of `D³p̄ ψ` and `D²p̄ Dψ`)
  and of the term `F` of Step 4, whose proof the source skips (DG21.tex:2274, :2411, :2446); they are written out (`StepOne`, `FluxCoeff`, `FluxPieces`, `StepFour`).
- **Minimal times and the sum over scales.** The times satisfy `τ ≥ M` with `M ≥ max(M_flux², M_corr², 1)` and `t ≥ 3τ`, since Step 5 integrates over `[τ, t]`;
  the scale sum of Step 3 is bounded by `Σ_m sup · ‖·‖` without Cauchy-Schwarz, with piecewise linear cutoffs on the balls of radius `2^{m+2}√r`, and the truncations
  are removed by dominated convergence. The bound (4.40) is proved for its square root.
- **The statement for one `σ`.** `DarioGuTwoScaleErrorTwo p σ` is proved for the `σ` of Proposition 2.13 (`σ = σ̄²`); Theorem 1 uses it for some `σ > 0`.

## Proposition 2.13 of Dario and Gu in dimension two

Proposition 2.13 of Dario and Gu (Proposition B.1, DG21.tex:2974-2986: the weak norm of the centered flux of the corrector on the
balls of the infinite cluster), in the form `DarioGuFluxWeakNormTwo p σ` (`d = 2`), is proved in
[`Rigidity/Proofs/Green/`](Rigidity/Proofs/Green/) for every `𝔭_c(2) < p < 1` with the diffusivity `σ = σ̄² = 2 θ(p)^{-1} ā` of (B.5),
where `ā` is the mean of the flux of the corrected planes
([`darioGuFluxWeakNormTwo_holds`](Rigidity/Proofs/Green/DarioGuFluxWeakNormHolds.lean)). The proof follows Appendix B of the source:
the decay (B.8) of the spatial averages of the flux (Gu, *An efficient algorithm for solving elliptic problems on percolation clusters*,
arXiv:1907.13571, Proposition 1.1, proved here in dimension two), the estimate (eq.gsmallH-1) of the weak norm of the flux of `ℤ²`, the
estimate (eq:DensityWeakNorm) of the density of the cluster (Step 2), the coarsening of the test functions (Step 1) and the minimal scale
(Step 3).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Green.exists_fluxMean_two`](Rigidity/Proofs/Green/DarioGuFluxMean.lean) | the mean of the flux of the corrected plane of slope `e_k` along `e_i` is `ā δ_{ik}` with `ā > 0`, by stationarity and the symmetries of the lattice. |
| [`fluxFlipSum_isOsBond`](Rigidity/Proofs/Green/DarioGuFluxFlipMoments.lean), [`ae_fluxFlip_sq_le_open`](Rigidity/Proofs/Green/DarioGuFluxOpenBound.lean), [`ae_fluxFlip_sq_le_closed`](Rigidity/Proofs/Green/DarioGuFluxClosedBound.lean) | Gu's Steps 1-4 in flip form: the sum over the bonds of the squared flip differences of the heat average of the flux is `O_s(C/r²)`. |
| [`exists_fluxSpatialAverage_two`](Rigidity/Proofs/Green/DarioGuFluxSpatialAverage.lean) | **Gu, Proposition 1.1** ((B.8)) in dimension two with the heat kernel `Φ_{r²}` of `ℤ²`: `\|Φ_{r²} ⋆ g(x)\| ≤ O_s(C/r)` for `r ≥ 1`. |
| [`exists_tsum_ofReal_abs_openHeat_grad_le`](Rigidity/Proofs/Green/DarioGuFluxKernelGradient.lean), [`ofReal_abs_heatF_sub_le`](Rigidity/Proofs/Green/DarioGuFluxHeatDifference.lean), [`sum_heatAvg_sub_mul_eq`](Rigidity/Proofs/Green/DarioGuFluxHeatDifference.lean), [`ofReal_abs_sum_mul_le_dyadic`](Rigidity/Proofs/Green/DarioGuFluxDyadic.lean) | the `ℓ¹` norm `C/√t` of the gradient of the heat kernel of `ℤ²` (from the local limit theorem of Lattice-Probability), the time increments of the heat flow of a test function through its gradient, the duality with the heat averages, and the dyadic heat decomposition of a pairing. |
| [`exists_fluxWeakNormBox`](Rigidity/Proofs/Green/DarioGuFluxWeakNormBox.lean) | (eq.gsmallH-1): `\|Σ_S g w\| ≤ Y ‖w‖_{ℓ²(S)} + Z ‖∇w‖_{ℓ²(T)}` with `E[Y^q]^{1/q} ≲ q^κ √\|S\| 2^{-J}` and `E[Z^q]^{1/q} ≲ q^κ (J + 1) √\|T\|`. |
| [`exists_densityWeakNorm`](Rigidity/Proofs/Green/DarioGuDensityWeakNorm.lean) | Step 2, (eq:DensityWeakNorm): the same bound for `1_{𝒞_∞} − θ(p)` on unions of triadic cubes of scale `K`, from Proposition A.1 and the Poincaré inequality on triadic cubes. |
| [`coarseTest`](Rigidity/Proofs/Green/DarioGuFluxCoarsening.lean), [`sum_sq_coarseTest_le`](Rigidity/Proofs/Green/DarioGuFluxCoarsening.lean), [`sum_sq_grad_coarseTest_le`](Rigidity/Proofs/Green/DarioGuFluxCoarsening.lean), [`card_mul_le_card_dgClusterBall`](Rigidity/Proofs/Green/DarioGuFluxCoarsening.lean) | Step 1: the coarsened test function (def.coarsenu), its `ℓ²` norm (eq:estcoarseminusu), its gradient (est.nablacoarsenL2), and the size of `𝒞_∞ ∩ B_r(y)`. |
| [`weakNormLe_of_scale_bounds`](Rigidity/Proofs/Green/DarioGuFluxWeakNormScale.lean) | Steps 1 and 3 at a scale `r ∈ [3^n, 3^{n+1})`: the weak norm of the centered flux on `𝒞_∞ ∩ B_r(y)` from the bounds of the flux and the density and the sizes of the partition cubes near `y`. |
| [`exists_summable_badBound`](Rigidity/Proofs/Green/DarioGuFluxWeakNormBad.lean), [`darioGuFluxWeakNormTwo_of_bounds`](Rigidity/Proofs/Green/DarioGuFluxWeakNormHolds.lean), [`darioGuFluxWeakNormTwo_holds`](Rigidity/Proofs/Green/DarioGuFluxWeakNormHolds.lean) | Step 3: the bad scales and their probabilities, the minimal scale, and **Proposition 2.13** in dimension two. |
| [`Rigidity.Assembly.ProvedFluxWeakNorm`](Rigidity/Proofs/Assembly/ProvedFluxWeakNorm.lean): `exists_darioGuTwoScaleErrorTwo_holds`, `exists_darioGuTranslatedFluxTwo_holds`, `darioGuHeatKernelTwo_of_gradient_barlow` (and its variants `_threeThree`, `_flipSum`, `_resample`, `_stepTwo`), `supercriticalBondGreenQuantitativeTwo_of_gradient_barlow`, `fast_decay_of_gradient_barlow`, `fast_decay_of_gradient_veryGood`, `darioGuHeatKernelTwo_of_gradient`, `supercriticalBondGreenQuantitativeTwo_of_gradient`, `fast_decay_of_gradient`, `darioGuHeatKernelTwo_holds`, `supercriticalBondGreenQuantitativeTwo_holds`, `fast_decay_holds` | the results that took Proposition 2.13 as the hypothesis `hflux`, without it: Proposition 4.3 and Remark B.3 with no hypothesis; Theorem 1 of Dario and Gu, Theorem 2 of Dario and Gu (R7) and Theorem 1.3 in dimension two from Theorem 3 (`DarioGuGradientBoundTwo`) and the Gaussian upper bound of Barlow (`BarlowGaussianUpperBoundTwo`), or the very good balls of the cluster, and, that bound being proved, from Theorem 3 alone; Theorem 3 being proved too, Theorems 1 and 2 of Dario and Gu and Theorem 1.3 in dimension two with no hypothesis. |

The thirty-four reports for the declarations of this section are in [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Departures from Dario and Gu:

- **Lattice heat kernel and dyadic times.** (eq.gsmallH-1) is proved from the heat averages of the flux of `ℤ²` at the dyadic times
  `4^j ≥ 1` against the time increments of the heat flow of the test function (DG21.tex:3046-3080 use the continuous multiscale Poincaré
  inequality (D.28) of Armstrong, Kuusi and Mourrat and the heat averages at all times `t ∈ (0, 1]`); the times below `2` are handled by
  the moments of the flux itself, the Lipschitz bound of the corrector (eq:lip.corr), which is (fluxbounded.est).
- **Gu's Proposition 1.1 in the lattice form.** (B.8) is used, and proved, with the heat kernel of `ℤ²` on the lattice points in place of
  a continuous kernel against the piecewise constant extension `[g]`.
- **The weak norms on `ℤ²` in the form of the test functions.** The bounds of the flux and of the density on `ℤ²` are stated for test
  functions vanishing off a finite set `S`, as `Y ‖w‖ + Z ‖∇w‖` with explicit moments, which is what the coarsened test functions need;
  the source writes them as `‖·‖_{H̲^{-1}(ℤ^d ∩ B_r)}` with the normalization `r^{-1} ‖φ‖_{L̲²}`.
- **The coarsening and the minimal scale of the partition.** The coarsened function takes `v` (extended by zero off `𝒞_∞ ∩ B_r(y)`) at the
  anchor of the partition cube of the planar partition of the good cubes off the cluster (the source chooses the point of `𝒞_*(□)`
  closest to the centre). The minimal scale `M_q(𝒫)` of (eq:Mt) is replaced by the event that every partition cube within `2·3^{n+2} + 2`
  of `y` has side at most `⌊3^{αn/4}⌋`, and the bound of `\|ℤ^d ∩ B_r\|/\|𝒞_∞ ∩ B_r\|` used in Step 1 by
  `\|𝒞_∞ ∩ B_r(y)\| ≥ (2·3^{n-1} + 1)²/L²` (`card_mul_le_card_dgClusterBall`).
- **Step 2 on unions of triadic cubes.** The density bound is proved on the `3 × 3` triadic cubes of scale `n + 2` around the cube of `y`,
  with the Poincaré inequality on the triadic cubes of Percolation-Cluster-Homogenization (`multiscalePoincare_holds`) in the multiscale
  decomposition; the source passes from `B_r` to the cube `□_m ⊇ B_r`.
- **Lemma 1.5.** The minimal scale is the first triadic scale after which every scale is good (`exists_minimalScale_of_summable`), with
  `E[exp(M^s)]` bounded uniformly in `y`; for `α > 1` the bound for `min(α, 1)` is used.
- **Componentwise.** The bound is stated for each component `[g̃_{e_k}]_i`, as in `DarioGuFluxWeakNormTwo`.

## Theorem 3 of Dario and Gu in dimension two from Proposition 3.9

Theorem 3 of Dario and Gu in the form of Remark 1.3 (the gradient bound on the heat kernel, `DarioGuGradientBoundTwo`) is
proved in [`Rigidity/Proofs/Green/`](Rigidity/Proofs/Green/) from two statements: the large-scale `C^{0,1}` estimate for caloric
functions on the infinite cluster, Proposition 3.9 (`DarioGuLipschitzTwo`, a named statement, in the range `2r ≤ R`), and the
Gaussian upper bound of Barlow (Theorem 4, `BarlowGaussianUpperBoundTwo`, cited). The proof is that of the source
(DG21.tex, proof of Theorem 3): Proposition 3.9 applied to the heat kernel on a cylinder of radius of order `√t`, its right
side bounded by Barlow's bound at the poles near the centre, after the minimal time `T'_NA` of (3.52). The parabolic
Caccioppoli inequality (Proposition 2.9) and the time-slice estimate (Lemma 2.10), used in the proof of Proposition 3.9, are
proved, the latter in its unnormalized form.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Green.DarioGuLipschitzTwo`](Rigidity/Proofs/Green/DarioGuParabolicInputs.lean), [`IsClusterCaloric`](Rigidity/Proofs/Green/DarioGuParabolicInputs.lean), [`coarsenPar`](Rigidity/Proofs/Green/DarioGuParabolicInputs.lean) | Proposition 3.9 as a named statement: `sup_{t ∈ I_r} ‖∇u(t)‖_{L̲²(𝒞_∞ ∩ B_r(y))} ≤ (C/R) ‖[u]_𝒫 - ([u]_𝒫)_{I_R × B_R(y)}‖_{L̲²(I_R × B_R(y))}` for `M(y) ≤ r`, `2r ≤ R`, `u` caloric on `I_R × (𝒞_∞ ∩ B_R(y))`, with the coarsening `[u]_𝒫` through the anchors of the planar partition. |
| [`darioGuGradientBoundTwo_of_lipschitz`](Rigidity/Proofs/Green/DarioGuGradientFromLipschitz.lean), [`goodTimes_anchorDist`](Rigidity/Proofs/Green/DarioGuGradientFromLipschitz.lean), [`abs_coarsenPar_openHeat_le`](Rigidity/Proofs/Green/DarioGuGradientFromLipschitz.lean) | Theorem 3 (Remark 1.3) from Proposition 3.9 and Theorem 4; the tail of the distance to the anchors of the partition cubes; the bound of the coarsened heat kernel on the cylinder. |
| [`darioGuCaccioppoliTwo_holds`](Rigidity/Proofs/Green/DarioGuParabolicCaccioppoli.lean), [`parabolic_caccioppoli_of_cutoff`](Rigidity/Proofs/Green/DarioGuParabolicCaccioppoli.lean) | Proposition 2.9 (parabolic Caccioppoli inequality, `DarioGuCaccioppoliTwo`), for every open component, with `C = 128`. |
| [`darioGuTimesliceTwo_holds`](Rigidity/Proofs/Green/DarioGuParabolicTimeslice.lean), [`timeslice_of_cutoff`](Rigidity/Proofs/Green/DarioGuParabolicTimeslice.lean) | Lemma 2.10 (the `L^∞ L²` gradient estimate in time slices, `DarioGuTimesliceTwo`) in the unnormalized form, for every open component, with `C = 4096`. |

The seven reports for the declarations of this section are in [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Departures from Dario and Gu:

- **The range of Proposition 3.9.** As printed (lines 1699-1702, `r ∈ [M, R]`) the inequality fails at `r = R`: a
  time-independent `u`, harmonic at the interior vertices of `𝒞_∞ ∩ B_R(y)` with values `±1` at the boundary vertices of
  opposite signs along about `cR` open edges between them, has `‖∇u‖²_{L̲²(𝒞_∞ ∩ B_R(y))}` of order `R^{-1}` while the square
  of the right side is at most of order `R^{-2}`. The proof of the source gives the estimate at the radius `r/2` for `r ∈ [M, R]`
  (Step 4: "with the radius `r/2` instead of `r`"), that is for `2r ≤ R`, the range of `DarioGuLipschitzTwo`.
- **The cylinder in the proof of Theorem 3.** With `2r ≤ R` and `t ≥ 4r²` the cylinder of the source (`R = √t/2`, top time
  `t + 1`) is replaced by the cylinder of top time `t + r²/2` and radius `(7t/8 + r²/2)^{1/2}`, on which the times lie in
  `[t/8, 9t/8]`; `t` is its time `-r²/2 ∈ I_r`.
- **The gradient.** The gradient on the left of Theorem 3 and Proposition 3.9 is over the open edges inside the ball, as in
  `DarioGuGradientBoundTwo`; the caloric functions are functions on `ℝ × ℤ²` constrained on `𝒞_∞ ∩ B_R(y)`, since the
  coarsening on `B_R(y)` reads them at anchors which may lie outside the ball; they are continuous in time at the
  vertices of the ball and solve the equation pointwise in time at its interior vertices (`IsClusterCaloric`), a
  classical form of the weak solutions in `H_par`, whose boundary values need only be square integrable in time.
- **Lemma 2.10 unnormalized.** With the normalized norms and a constant independent of the configuration the printed
  inequality (lines 1023-1032) fails: if `𝒞_∞ ∩ B_{R/2}(y)` is a path of length of order `R` joining two large clusters of the
  annulus, a time-independent caloric `u` close to `0` on one and to `1` on the other has the square of the left side of order `R^{-2}` and
  the square of the right side of order `R^{-3}`. `DarioGuTimesliceTwo` is the unnormalized form,
  `sup_{t ∈ I_{R/2}} ‖∇u(t)‖²_{L²(𝒞_∞ ∩ B_{R/2})} ≤ C R^{-2} ‖∇u‖²_{L²(I_R × (𝒞_∞ ∩ B_R))}`, which gives the printed one where the
  volumes of `𝒞_∞ ∩ B_R(y)` and `𝒞_∞ ∩ B_{R/2}(y)` are comparable.
- **Proofs written out.** The source omits the proofs of Proposition 2.9 and Lemma 2.10 (lines 1017-1019 and 1021, the
  latter by reference to Lemma 8.2 of Armstrong, Kuusi and Mourrat); they are the standard energy arguments with a spatial
  cutoff, by summation by parts on the cluster, and a time cutoff (Proposition 2.9) or an average over the initial time
  (Lemma 2.10).

Proposition 3.9 remains a named statement: its proof in the source goes through Theorem 5 (homogenization of the parabolic
Dirichlet problem), whose printed estimate has no term in the time derivative of the boundary condition.

## The subadditive quantities of Armstrong and Dario in every dimension: Lemmas 5.3 and 5.4, (5.21) to (5.24) and Step 1 of Lemma 5.10

For every `d ≥ 2` and `𝔭_c(d) < p < 1`, the following are proved in [`PercolationClusterHomogenization/Proofs/Cluster/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Cluster/)
(namespace `Rigidity.Percolation`; the files `GeneralSlopeQuadratic`, `GeneralMinimalSet`, `GeneralMuEnergyDefect`,
`GeneralTauIncrements` and `GeneralFiniteVolumeMatrix`), with the quadratic forms in the slope handled by the polarization
identity (`IsSlopeQuadratic`) and by the cube quantities `cubeMu`, `cubeNu` and `cubeAhom` of the previous sections.

| Lean declaration | Statement |
| --- | --- |
| [`abs_slopeQuadratic_sub_half_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralSlopeQuadratic.lean), [`IsSlopeQuadratic.le_of_nonneg`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralSlopeQuadratic.lean), [`IsSlopeQuadratic.comp_mulVec`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralSlopeQuadratic.lean) | the deterministic gradient step behind Lemma 5.3, and the closure of slope quadratic forms under sums and linear changes of the slope. |
| [`sum_mul_le_neg_cubeMu_add_cubeNu_add_mul`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMinimalSet.lean) | the homogeneous form of Corollary 4.6, (4.29): `q · ξ ≤ −μ(U, q) + ν(U, ξ) + \|q\|₁ \|ξ\|₁ Y(U)`, with `Y(U) = cubeComparisonError`. |
| [`cube_minimalset`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMinimalSet.lean) | AD Lemma 5.3, (5.6), on resolved cubes, in every dimension. |
| [`exists_lintegral_cubeMuDefect_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuEnergyDefect.lean) | AD Lemma 5.4, (5.10), for `μ`, before summing the increments: `E[D^μ_n(U)] ≤ \|U\| (E[−μ(W)] − E[−μ(U)] + C \|q\|₁² (3^{−n/4} + exp(−c 3ⁿ)))`, `W` of scale `n ≤` that of `U`. |
| [`exists_lintegral_cubeMuDefect_le_tau`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralTauIncrements.lean), [`exists_lintegral_cubeNuDefect_le_tau`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralTauIncrements.lean) | AD Lemma 5.4, (5.10), for `μ` and for `ν`: `E[D_n(□_m)]/\|□_m\| ≤ C \|q\|² (∑_{k=n}^{m−1} τ_k + 3^{−n/4})`. |
| [`exists_cubeMuIncrement_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralTauIncrements.lean), [`exists_cubeNuIncrement_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralTauIncrements.lean), [`summable_cubeTau`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean) | the increments (5.9) for `μ` and for `ν`, and the summability of `τ_k`. |
| [`cubeAhomInvFinite`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean), [`half_sum_mul_cubeAhomInvFinite_eq`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean) | the matrix `ā_n^{−1}` of (5.21) and its defining identity. |
| [`exists_cubeAhomInvFinite_bounds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean) | the bounds (5.22): for `n` at least some `N`, `c \|q\|² ≤ ½ q · ā_n^{−1} q ≤ C \|q\|²`. |
| [`integral_cubeCoarsePairing_cubeMuMinimizer`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean), [`cubeCoarsePairing_cubeMuMinimizer_div`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean) | (5.23): the expectation of the pairing of the coarse gradient at `q'` with the minimizer at `q`, divided by the volume, on the resolved cube of scale `n`, is `q' · ā_n^{−1} q`. |
| [`exists_abs_cubeMuMean_sub_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean), [`exists_abs_cubeAhomInvFinite_sub_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean), [`exists_abs_cubeAhomInvLimit_sub_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean), [`tendsto_cubeAhomInvFinite`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean) | (5.24): `\|E[−μ(□_n, q)] − E[−μ(□_m, q)]\| ≤ C \|q\|² (∑_{k=n}^{m−1} τ_k + 3^{−n/4})`, the same bound entrywise for `ā_n^{−1}` and `ā_m^{−1}`, and for `ā_n^{−1}` and its limit with `∑_{k ≥ n} τ_k`. |
| [`exists_cubeAhomInvFinite_mul_cubeAhomFinite`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean), [`cubeMuMean_cubeAhomFinite_sub_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean), [`cubeOmegaD_succ_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralFiniteVolumeMatrix.lean) | `ā_n^{−1}` is invertible from some scale on, `x ↦ E[−μ(□_n, x)] − ξ · x` is minimal at `x = ā_n ξ`, and the first part of Step 1 of Lemma 5.10: `D_{n+1} ≤ D_n` minus the increments of `E[ν]` at the unit vectors and of `E[−μ]` at `ā_n e_i`. |

The thirty-five reports for the declarations of this section are in [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).
The second part of Step 1 of Lemma 5.10 and the rest of Lemma 5.10, Lemmas 5.5, 5.7, 5.8, 5.9 and 5.11 and Proposition 5.2
are not yet proved in every dimension; in dimension two they are proved in the planar sections above.

Departures from Armstrong and Dario:

- **Lemma 5.3** is stated deterministically on resolved cubes, with a gradient step in place of the minimizer `q₀` (no
  `k(□)`), and the random factor `√(Λ + 1)` on `ρ^{1/2}`, as in dimension two; the tails of `Y` and `Λ` are not part of the statement.
- **(4.29)** is used with Young's parameter chosen for each slope, giving the error `|p|₁ |q|₁ Y(U)`.
- **Lemma 5.4**: the forms with `τ_k` are stated for the cube at the origin only.
- **Lemma 5.4** for `ν` is stated at the slopes `ā^{−1} q` (Armstrong and Dario state it for every slope; the two are equivalent
  since `ā = σ I` with `σ > 0`). For `μ` the energy is on the clusters `𝒞_*(V)`, as in dimension two, with the rate `3^{−n/4}` of
  (4.32) in expectation and the term `exp(−c 3ⁿ)` from the approximate stationarity of `E[−μ]`.

## Section 3 and the isotropy of the homogenized matrix in every dimension

For every `d ≥ 2` and `𝔭_c(d) < p < 1`, with no further hypothesis, the partition `𝓡` of Definition 3.7 of Armstrong and
Dario, the Meyers estimate of Proposition 3.8 above it, and the isotropy of the homogenized matrix are proved, in
[`PercolationClusterHomogenization/Proofs/Cluster/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Cluster/) (namespace `Rigidity.Proofs.Cluster.GeneralDim` for
`GeneralRHLocal`, `GeneralRHEvent`, `GeneralRHProb`, `GeneralRHPartition` and `GeneralRHMeyers`, and
`Rigidity.Percolation` for `GeneralRHExit`, `GeneralReachDomination` and `GeneralAhomIsotropic`). The construction is that of the planar section
[Lemmas 5.5 and 5.7 in dimension two](#lemmas-55-and-57-in-dimension-two) in every dimension: Propositions 2.1 and 2.4 are
applied to a local family of cubes, the cubes on whose children the reverse Hölder inequality holds, whose failure is
bounded through the partition into good cubes.

* **The local family** (`rhGood`, from `RHCube`, the reverse Hölder inequality with exponent `2d/(d+1)` for every set of
  the triple closed under the open edges and every function harmonic on it): its failure events are determined by the open
  edges of the threefold enlargement, the hypothesis (2.1) of Proposition 2.1 (`measurableSet_not_mem_rhGood_local`).
* **Lemma 3.6, deterministic part** (`rhCube_of_scales`): a cube whose triple has partition cubes of scale at most `k − 2`
  and `∑_{3□} partitionReach^{2d(d+2)} ≤ C_G 3^{(k+1)d}` is a reverse Hölder cube. A vertex joined by an open path to the
  boundary of the box of its partition cube is joined to its anchor inside the parent of the partition cube and the box
  (`reachable_partitionAnchor_of_exit`, `mem_partitionBoxCluster_of_exit`), and a part of a closed set that no open edge
  leaves carries no energy (`clusterGradSq_eq_zero_of_closed`).
* **The failure bound (2.2)** (`rhFailureBound_holds`): the scale tail of the partition cubes, the stretched exponential
  concentration of the reach on a triple (`exists_measure_sum_reach_enl_gt_le`, with the exponent `1/(2(d + 2d(d+2) + 1))`),
  and Lemma 3.6. The reach of the partition is dominated by the stopping size of the partition into coarsely good cubes,
  whose failure events are local and of probability at most `C exp(−c 3^n)`
  (`partitionReach_le_stoppingSize_coarseGood`, `exists_measure_not_mem_coarseGood_le`, Lemma 2.7).
* **The partition `𝓡`** (`rhPartition_holds`): the maximal stopping cubes of the local family form almost surely a partition
  with comparable neighbours, every predecessor of a cell is in the local family, and for every exponent the moments of the
  sizes of the cells over a triadic cube are at most `K |□|` off an event of probability `C 3^{−Bk}`
  (`rhPartition_of_failureBound`).
* **Proposition 3.8 above `𝓡`** (`meyers_rh_uniform`): the Meyers estimate with exponents `ε, t` depending only on the
  reverse Hölder constant, for every set `U₀` closed under the open edges inside the triple `3□`
  (`avg_clusterEnergy_le_of_rhGood`, with the constant `3^{d+1} max(1, A₀)`).
* **Isotropy** (`exists_cubeAhom_eq_smul_one`, `Rigidity.Percolation`): `ā = σ I` with `σ > 0`, for `d ≥ 2` and
  `𝔭_c(d) < p < 1` (the remark after (5.22) of Armstrong and Dario). The signed permutations of `ℤ^d` carry crossing
  clusters to crossing clusters and leave `ν`, its expectations on the cube at the origin and their limit invariant
  (`cubeNu_signedPerm`, `cubeNuLimit_signedPermSlope`); only the crossing cluster is used, since the rounded three-quarter
  cubes of the good cubes are not reflection-symmetric, so no goodness is needed.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Cluster.GeneralDim.measurableSet_not_mem_rhGood_local`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralRHLocal.lean) | the failure event of a cube of the local family `rhGood` is determined by the open edges of the threefold enlargement, as the hypothesis (2.1) of Proposition 2.1 requires. |
| [`rhCube_of_scales`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralRHEvent.lean), [`mem_partitionBoxCluster_of_exit`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralRHEvent.lean), [`Rigidity.Percolation.reachable_partitionAnchor_of_exit`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralRHExit.lean) | AD Lemma 3.6, deterministic part, in every dimension, in the form of a reverse Hölder cube for every closed set of the triple, with the exit lemma that joins a vertex to its anchor. |
| [`Rigidity.Percolation.partitionReach_le_stoppingSize_coarseGood`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralReachDomination.lean), [`exists_measure_not_mem_coarseGood_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralReachDomination.lean), [`Rigidity.Proofs.Cluster.GeneralDim.exists_measure_sum_reach_enl_gt_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralRHProb.lean) | the reach of the partition into good cubes is at most the stopping size of the partition into coarsely good cubes, the failure bound of the coarsely good cubes (Lemma 2.7), and the concentration of the sums of the powers of the reach on a triple. |
| [`rhFailureBound_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralRHProb.lean), [`rhPartition_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralRHPartition.lean) | the failure bound (2.2) of the local family and the partition `𝓡` of Definition 3.7 with its minimal scales (Propositions 2.1 and 2.4), `d ≥ 2`, `p > 𝔭_c(d)`. |
| [`meyers_rh_uniform`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralRHMeyers.lean) | AD Proposition 3.8 above the partition `𝓡`, in every dimension, with `ε` and `t` depending only on the reverse Hölder constant. |
| [`Rigidity.Percolation.cubeNu_signedPerm`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralAhomIsotropic.lean), [`cubeNuLimit_signedPermSlope`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralAhomIsotropic.lean), [`exists_cubeAhom_eq_smul_one`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralAhomIsotropic.lean) | the invariance of `ν` and of the limit of its expectations under the signed permutations of the coordinates, and `ā = σ I` with `σ > 0` in every dimension `d ≥ 2`. |

The thirteen reports for the declarations of this section are in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean). Definition 3.9 (the partition `𝓠_a` for the Meyers
estimate) and the localization of `μ` are proved in
[Localization, stationarity and the limit of μ, and Definition 3.9, in every dimension](#localization-stationarity-and-the-limit-of-μ-and-definition-39-in-every-dimension).

Departures from Armstrong and Dario: the good cubes of the local family ask the reverse Hölder inequality for all sets of
the triple of each child closed under the open edges and all functions harmonic on them, not only for `𝒞_max(3□)` with the
numerator `𝒞_*(□)`; the failure probability is bounded through the partition into good cubes with polynomial rates in
place of the stretched exponentials of the tails of `𝓡`, as in the planar section.

## Localization, stationarity and the limit of μ, and Definition 3.9, in every dimension

For every `d ≥ 2` and `𝔭_c(d) < p < 1`, the localization of the partition and of `μ` (Propositions 4.9 and 4.10),
the locality (4.39) and stationarity (4.40), the subadditivity error (4.32) in expectation, the approximate
monotonicity (4.48) and the limit of `E[−μ(□_m, q)]`, with the duality inequality and the bounds (5.1) for `μ`, and the
partition `𝓠_a` of Definition 3.9 with its minimal scales, are proved in
[`PercolationClusterHomogenization/Proofs/Cluster/`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/tree/main/PercolationClusterHomogenization/Proofs/Cluster/) (the eleven files `GeneralMu*.lean` and
`GeneralMeyersPartition.lean`; namespace `Rigidity.Percolation`, and `Rigidity.Proofs.Cluster.GeneralDim` for the last
file). They continue the section
[The subadditive quantities on the clusters of triadic cubes of Z^d](#the-subadditive-quantities-on-the-clusters-of-triadic-cubes-of-zd)
and
[Section 3 and the isotropy of the homogenized matrix in every dimension](#section-3-and-the-isotropy-of-the-homogenized-matrix-in-every-dimension).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.exists_measure_ne_cappedCube_goodCubes_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuLocal.lean), [`Rigidity.Percolation.exists_measure_cubeCappedDiscrepancy_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuLocal.lean) | AD Proposition 4.9 in every dimension `d ≥ 2`: the partition into good cubes differs at some vertex of a triadic cube `A` of scale `m` from the partition capped at the scale `n` with probability at most `C (2·3^{m−n} + 29)^d exp(−c 3ⁿ)`; the second form is for `n` the scale of the cube `V` on which the discrepancy is read. |
| [`Rigidity.Percolation.measurable_cubeMuLoc_localBondSigma`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuLocal.lean), [`Rigidity.Percolation.indepFun_cubeMuLoc`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuLocal.lean), [`Rigidity.Percolation.measurable_cubeNu_localBondSigma`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuLocal.lean), [`Rigidity.Percolation.indepFun_cubeNu`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuLocal.lean) | AD (4.39), every `d ≥ 2`: the local version of `−μ(V, q)` is measurable for the bonds inside the local region of `V` (the cube of side `14·3ⁿ + 1` around it), `ν(V, ξ)` for the bonds inside `V`, and the versions on two cubes with disjoint regions are independent (pairs of cubes only). |
| [`Rigidity.Percolation.exists_cubeMuLoc_localization`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuLocal.lean) | AD Proposition 4.10 for `μ`, every `d ≥ 2`: the expectations of the local version and of `1{𝒫, V res}(−μ(V, q))` differ by at most `C \|q\|₁² exp(−c 3ⁿ)`, `n` the scale of `V`. For `ν` no localization is needed, because `ν` is local (`measurable_cubeNu_localBondSigma`). |
| [`Rigidity.Percolation.map_cubeMuStat_shift`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuStationary.lean), [`Rigidity.Percolation.exists_cubeMuStat_localization`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuStationary.lean), [`Rigidity.Percolation.exists_lintegral_neg_cubeMu_le_of_scale_eq`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuStationary.lean) | AD (4.40), every `d ≥ 2`: the law of the stationary local version of `−μ(z + V, q)` does not depend on `z ∈ 3ⁿ ℤ^d`; the same localization error for the stationary version; hence `E[−μ]` is stationary up to `C \|q\|₁² exp(−c 3ⁿ)`. |
| [`Rigidity.Percolation.exists_lintegral_sum_cubeMu_subcubes_sub_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuSubadditiveMoments.lean), [`Rigidity.Percolation.sum_cubeMu_subcubes_sub_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuSubadditiveError.lean), [`Rigidity.Percolation.exceptionalEdgeCount_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuSubadditiveError.lean) | AD (4.32) in expectation, every `d ≥ 2`: the error of the subadditivity of `μ` over the subcubes is at most `C \|q\|₁² \|U\| 3^{−n/4}` in expectation, from a deterministic bound by the number of exceptional edges. |
| [`Rigidity.Percolation.exists_lintegral_neg_cubeMu_le_of_scale_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuConvergence.lean) | AD (4.48), every `d ≥ 2`: for triadic cubes `V`, `U` with the scale `n` of `V` at most that of `U`, `E[−μ(U, q); 𝒫, U res] ≤ E[−μ(V, q); 𝒫, V res] + C \|q\|₁² (3^{−n/4} + exp(−c 3ⁿ))`. |
| [`Rigidity.Percolation.exists_tendsto_cubeMuMean`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuConvergence.lean), [`Rigidity.Percolation.tendsto_lintegral_neg_cubeMu_of_scale`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuConvergence.lean), [`Rigidity.Percolation.tendsto_lintegral_cubeMuLoc_of_scale`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuConvergence.lean), [`Rigidity.Percolation.tendsto_lintegral_cubeMuStat_of_scale`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuConvergence.lean) | The limit `lim E[−μ(□_m, q)]` exists, lies between `0` and `C \|q\|₁²`, and is the limit of `E[−μ(V_m, q)]` for every sequence of cubes of scales `m`, and of the expectations of the local and stationary local versions. |
| [`Rigidity.Percolation.cubeMuLimit_smul_add_smul`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuQuadratic.lean), [`Rigidity.Percolation.exists_cubeMuLimit_bounds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuQuadratic.lean) | The limit of `E[−μ(□_m, q)]` is a quadratic form in `q`, bounded above by `C \|q\|₁²`. |
| [`Rigidity.Percolation.sum_mul_le_neg_cubeMu_add_cubeNu`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuDuality.lean), [`Rigidity.Percolation.sum_mul_le_cubeMuLimit_add_cubeNuLimit`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuDuality.lean) | AD Corollary 4.6 with its face errors, and the duality inequality between the limits, every `d ≥ 2`: `q · ξ ≤ lim E[−μ(□_m, q)] + lim E[ν(□_m, ξ)]`. |
| [`Rigidity.Percolation.exists_cubeMuLimit_two_sided`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMuDuality.lean) | The bounds (5.1) for `μ`, every `d ≥ 2`: `c \|q\|² ≤ lim E[−μ(□_m, q)] ≤ C \|q\|₁²`, from the duality inequality and `ā = σ I`. |
| [`Rigidity.Proofs.Cluster.GeneralDim.exists_meyersFailureBound`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMeyersPartition.lean), [`Rigidity.Proofs.Cluster.GeneralDim.exists_measure_stoppingScale_large_le`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMeyersPartition.lean) | AD (3.17) as the failure bound (2.2) for the good cubes of the Meyers estimate, `C₁ exp(−c 3^{ns})` for a cube of scale `n`, and the tail bound of the minimal scales of a local family (Propositions 2.1 and 2.4). |
| [`Rigidity.Proofs.Cluster.GeneralDim.meyersPartition_holds`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/PercolationClusterHomogenization/Proofs/Cluster/GeneralMeyersPartition.lean) | AD Definition 3.9, every `d ≥ 2` and `p > 𝔭_c(d)`: the partition `𝓠_a` with minimal scales whose tails `P[cells near □_k too large, or Σ size^t > K \|□_k\|] ≤ C exp(−c 3^{kr})` are stretched exponential, for every `t > 0`. |

The forty-three reports for the declarations of this section, which include the supporting declarations named in the
source files, are in [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean). Lemma 4.11 and the estimate (4.44) of Proposition 4.10 are not proved: Armstrong and
Dario use them only for (5.31) in the proof of Lemma 5.7, and the planar proof of that lemma replaces them by the local
version of the planar section [Lemmas 5.5 and 5.7 in dimension two](#lemmas-55-and-57-in-dimension-two).

Departures from Armstrong and Dario:

- **Localization.** Proposition 4.10 is proved in expectation, and the local version agrees with `μ` exactly off a small
  event (`cubeMuLoc_eq_of_good`). `μ` is localized, as in dimension two, through the partition capped at the scale of `V` on the
  region of side `14·3ⁿ + 1` around `V`, in place of `𝒫_loc^{(n)}(□)` and `𝒞_*^{(n)}(□)`; the error is
  `exp(−c 3ⁿ)`. The exact stationarity (4.40) holds for the stationary local versions `cubeMuStat`; for `E[−μ]` it holds
  up to `C \|q\|₁² exp(−c 3ⁿ)`.
- **Subadditivity error (4.32).** The error in expectation is bounded through the exceptional edges (those that leave
  the subcube or are unresolved), counted at exceptional vertices, with Young's inequality at the parameter
  `3^{−n/4}`; the rate in (4.48) is `3^{−n/4}`, as printed.
- **Definition 3.9.** `meyersGood` asks the Meyers estimate on each child, for every set of the triple closed under its
  open edges and every function harmonic on it, as `rhGood` does for `𝓡`, in place of the estimate `ME_ε(□)` with
  `𝒞_max(3□)`. The printed family has `ME_ε(□_m) ≤ C` where `ME_ε(□) ≤ C` is meant. The minimal scales have the
  stretched exponential tails stated in the table.

## Proposition 2.7 and Steps 1, 2, 3 and 5 of the proof of Theorem 5 of Dario and Gu in dimension two

The second part of Proposition 2.7 of Dario and Gu (the Poincaré inequality for functions vanishing on the boundary of a ball of
the infinite cluster, `p = 2`) is proved, and the following steps of the proof of Theorem 5 (the homogenization of the parabolic
Dirichlet problem, DG21.tex:1280-1684) are proved in the forms stated in the table, for unit conductances on the open edges of
the planar cluster. Theorem 5 itself is not formalized: as printed, the right side of (3.11) contains no time
derivative of the boundary values `f`, and for `f(t, x) = t` (so `∇f = 0`) the solution `u` differs from `ū` at the
points of `int_a V` with an open neighbour in `∂_a V`. The global Meyers estimate (3.19), used in Lemma 3.7 and Step 4,
fails for the same data.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Green.clusterDirichletPoincareTwo_holds`](Rigidity/Proofs/Green/ClusterDirichletPoincare.lean), [`sum_sq_le_of_weakPoincare`](Rigidity/Proofs/Green/ClusterDirichletPoincare.lean) | `ClusterDirichletPoincareTwo`, Proposition 2.7, second part, `p = 2`, `d = 2`: `Σ_V u² ≤ (C R)² E_V(u)` on `V = 𝒞_∞ ∩ B_R(y)` for `R ≥ M(y) ≤ O_s(C)` and `u` vanishing on `∂_a V`; from the weak Poincaré inequality on `𝒞_∞ ∩ B_{KR}(y)` and Proposition A.1. |
| [`sum_neg_openLaplacian_mul`](Rigidity/Proofs/Green/ClusterParabolicEnergy.lean), [`sum_mul_le_of_weakNormLe`](Rigidity/Proofs/Green/ClusterParabolicEnergy.lean), [`integral_sum_sq_le_of_energy`](Rigidity/Proofs/Green/ClusterParabolicEnergy.lean), [`integral_sum_sq_le_of_dirichletPoincare`](Rigidity/Proofs/Green/DarioGuDirichletSteps.lean) | Step 2: the integration by parts (1.29), the duality (1.33), and `∫ Σ_V v² ≤ 64 P² (P + \|V\|^{1/2})² ∫ B²` for `v` vanishing on `∂_a V` and at the initial time with `‖(∂_t − Δ) v‖_{H̲^{−1}(V)} ≤ B`, given `Σ_V v² ≤ P² Σ_V \|∇v\|²`. |
| [`weakNormLe_sqrt_sum_sq`](Rigidity/Proofs/Green/ClusterWeakNorm.lean), [`WeakNormLe.mul_right`](Rigidity/Proofs/Green/ClusterWeakNorm.lean), [`weakNormLe_sum_antisymm`](Rigidity/Proofs/Green/ClusterWeakNorm.lean) | (3.27), (3.26) and the divergence form of the weak norm on a finite set of the cluster. |
| [`openLaplacian_cutoffTwoScale`](Rigidity/Proofs/Green/ClusterTwoScaleDecomposition.lean), [`openLaplacian_cutoffTwoScale_of_corrector`](Rigidity/Proofs/Green/ClusterTwoScaleDecomposition.lean), [`timeDeriv_sub_openLaplacian_cutoffTwoScale`](Rigidity/Proofs/Green/ClusterTwoScaleDecomposition.lean) | Step 3, (3.23) to (3.25): the equation of the two-scale expansion `U + Σ_k F_k χ_k` at a point of the cluster, from the corrector equation. |
| [`weakNormLe_div_field`](Rigidity/Proofs/Green/ClusterTwoScaleTerms.lean), [`weakNormLe_time_term`](Rigidity/Proofs/Green/ClusterTwoScaleTerms.lean), [`weakNormLe_flux_term`](Rigidity/Proofs/Green/ClusterTwoScaleTerms.lean), [`weakNormLe_twoScale_equation`](Rigidity/Proofs/Green/ClusterTwoScaleTerms.lean), [`abs_discrete_div_sub_le`](Rigidity/Proofs/Green/DarioGuDiscreteDivergence.lean), [`weakNormLe_term_a`](Rigidity/Proofs/Green/DarioGuDiscreteDivergence.lean) | Step 3, first lines of (3.28) to (3.32): the weak norms of the terms a, b, c1, d and e in terms of bounds on their coefficients, and the bound of the weak norm of `(∂_t − Δ) w` by their sum. |
| [`sum_sq_twoScale_sub_le`](Rigidity/Proofs/Green/DarioGuDirichletSteps.lean), [`dgStepFive`](Rigidity/Proofs/Green/DarioGuDirichletSteps.lean) | Step 1 (the corrector term of the two-scale expansion) and Step 5 (the choice `β = 1/16`, `q = 48(4 + 2δ')/δ'`, `α = δ'/(128(2 + δ'))` gives `𝓔(r, β, q) ≤ C r^{−α}`). |

The twenty reports for the declarations of this section are in [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Departures from Dario and Gu:

- **The boundary in Proposition 2.7.** The function vanishes on `∂_a V`, the points of `V` with an open edge leaving `V`, a
  subset of the boundary `∂(ℤ² ∩ B_R(y)) ∩ 𝒞_∞` of the source; the statement implies the printed one and is the form used for
  the functions of `C_0^a(V)` in Step 2.
- **Step 2.** The function `w − u` is assumed to vanish on `∂_a V`. The source asserts this at line 1420, but `w` equals
  `ū` there, not `f`, at the points of `∂(ℤ² ∩ B_r)` inside the convex hull.
- **Forward differences and the centered flux.** The decomposition pairs the centered flux `g̃` (not the translated flux `g̃*`)
  with the forward differences `D_i F_k`, the divergence field carries the corrector at the base point of each edge and the
  extra field `−a_i D_i F_i`, and the discrete divergence is `Σ_k D_k F_k`. The left side of (3.25) is printed with `∂_t − D^*·aD`;
  the computation (3.23) is for `∂_t + D^*·aD`.
- **Constants.** (3.26) and (3.27) carry `|V|^{1/2}` in place of `r`; the term a is bounded by the derivatives of `Υ` and of `ū`
  along the lattice lines separately, in place of `‖∇²(Υ∇ū)‖_{L^∞}`.

## Theorem 3 of Dario and Gu in dimension two from Theorem 4, and Theorems 1 and 2 from Proposition 2.13 and Theorem 4

Theorem 3 of Dario and Gu in the form of Remark 1.3 (`DarioGuGradientBoundTwo`) is proved from the Gaussian upper bound of
Barlow (Theorem 4, `BarlowGaussianUpperBoundTwo`, cited) alone, with the order-zero regularity of Armstrong and Dario and
Proposition A.1, which are proved, by an elliptic estimate for the time slices of the heat kernel. Neither Theorem 5 nor
Proposition 3.9 of the source is used, so the reduction to Proposition 3.9 of the section
[Theorem 3 of Dario and Gu in dimension two from Proposition 3.9](#theorem-3-of-dario-and-gu-in-dimension-two-from-proposition-39)
is no longer needed. With it, Theorem 1 of Dario and Gu (`DarioGuHeatKernelTwo`), their Theorem 2 (the quantitative Green
estimate `SupercriticalBondGreenQuantitativeTwo`, with the random additive constant of the plane) and Theorem 1.3 of the paper
follow from Proposition 2.13 of Dario and Gu (`DarioGuFluxWeakNormTwo`) and Theorem 4. Theorem 4 being proved
(`barlowGaussianUpperBoundTwo_holds`), Theorem 3 holds with no hypothesis (`darioGuGradientBoundTwo_holds`), and
Theorems 1 and 2 and Theorem 1.3 follow from Proposition 2.13 alone.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Green.heatDeriv`](Rigidity/Proofs/Green/HeatTimeDerivBounds.lean), [`hasSum_heatDeriv_mul`](Rigidity/Proofs/Green/HeatTimeDerivBounds.lean), [`abs_heatDeriv_two_le`](Rigidity/Proofs/Green/HeatTimeDerivBounds.lean) | On a graph of bounded degree, the time derivatives of the heat kernel, `Σ_w ∂^i p_a(x, w) ∂^j p_b(w, y) = ∂^{i+j} p_{a+b}(x, y)`, and `\|∂_s² p_s(z, x)\| ≤ 8 s^{-2} (p_{s/4}(z, z) p_{s/4}(x, x))^{1/2}`. |
| [`exists_dirichlet`](Rigidity/Proofs/Green/HarmonicReplacement.lean), [`exists_exitFunction`](Rigidity/Proofs/Green/HarmonicReplacement.lean), [`abs_sub_le_mul_exitFunction`](Rigidity/Proofs/Green/HarmonicReplacement.lean), [`exitFunction_le_two_mul`](Rigidity/Proofs/Green/HarmonicReplacement.lean) | On a finite set `A` of a graph: the harmonic replacement, the exit-time function `e` (`Δe = −1` on `A`), `\|g − h\| ≤ F e` when `\|Δg\| ≤ F` on `A`, and `e ≤ 2τ` when `Σ_{w ∈ A} p_τ(z, w) ≤ 1/2` on `A`. |
| [`exists_nL2_sub_le_of_laplacian`](Rigidity/Proofs/Green/EllipticSliceEstimate.lean) | The oscillation estimate `‖v − c‖_{L̲²(B_r)} ≤ C r (U/R + R F)` for `\|v\| ≤ U` on `B_R` and `\|Δv\| ≤ F` on its interior, from the order-zero estimate and the exit-time hypothesis, by harmonic replacement on the balls of radii `R/2^k`. |
| [`pairEnergy_le_of_laplacian`](Rigidity/Proofs/Green/EllipticCaccioppoliSource.lean), [`gradEnergyOn_le`](Rigidity/Proofs/Green/EllipticCaccioppoliSource.lean) | The Caccioppoli inequality with a bounded source on graph balls. |
| [`exists_orderZero_clusterBall`](Rigidity/Proofs/Green/OrderZeroClusterBall.lean), [`orderZero_nL2`](Rigidity/Proofs/Green/OrderZeroClusterBall.lean) | The order-zero estimate of Armstrong and Dario at every centre of the plane, on the balls `𝒞_∞ ∩ B_r(z)` and for functions on the lattice. |
| [`sqrt_gradEnergy_openHeat_le`](Rigidity/Proofs/Green/DarioGuGradientDirect.lean), [`darioGuGradientBoundTwo_of_barlow`](Rigidity/Proofs/Green/DarioGuGradientDirect.lean) | The gradient bound at one time slice (deterministic form), and Theorem 3 (Remark 1.3) from Theorem 4. |
| [`Rigidity.Assembly.WithPlanarInputs.darioGuHeatKernelTwo_of_flux_barlow`](Rigidity/Proofs/Assembly/PlanarDarioGuDirect.lean), [`supercriticalBondGreenQuantitativeTwo_of_flux_barlow`](Rigidity/Proofs/Assembly/PlanarDarioGuDirect.lean), [`fast_decay_of_flux_barlow`](Rigidity/Proofs/Assembly/PlanarDarioGuDirect.lean) | Theorems 1 and 2 of Dario and Gu and Theorem 1.3 of the paper in dimension two from `DarioGuFluxWeakNormTwo` and `BarlowGaussianUpperBoundTwo`. |
| [`Rigidity.Green.darioGuGradientBoundTwo_holds`](Rigidity/Proofs/Green/DarioGuGradientHolds.lean), [`Rigidity.Assembly.WithProvedBarlow.darioGuHeatKernelTwo_of_flux`](Rigidity/Proofs/Assembly/ProvedGradient.lean), [`supercriticalBondGreenQuantitativeTwo_of_flux`](Rigidity/Proofs/Assembly/ProvedGradient.lean), [`fast_decay_of_flux`](Rigidity/Proofs/Assembly/ProvedGradient.lean) | Theorem 3 with no hypothesis, and Theorems 1 and 2 of Dario and Gu and Theorem 1.3 in dimension two from `DarioGuFluxWeakNormTwo` alone. |

The fifteen reports for the declarations of this section are in [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Departures from Dario and Gu:

- **The route to Theorem 3.** The source proves Theorem 3 from Proposition 3.9, whose proof goes through Theorem 5. Theorem 5
  does not hold as printed: with all conductances equal to one and `f(t, x) = t`, the right side of (3.11) vanishes while the
  solutions `u` and `ū` differ at every large radius; the global Meyers estimate (3.19) fails for the same data; the
  rectangular interior estimate (3.13) fails when the radii `r₁` and `r₂` are not comparable; and the lattice points in the
  interior of the convex hull of `ℤ^d ∩ B_r` need not be at distance at least `1/√2` from its boundary, as stated in Step 4.1
  (line 1586; `r² = 26`, `x = (4, 2)`), nor at any positive uniform distance. None of these is used here. With `D = |x − y| ≤ t`
  and `r ≤ √t/2`, the time slice `v = p(t, x, ·)` is bounded by `U = C t^{-1} e^{-D²/(C t)}` on `B_{3√t}(y)` by Theorem 4, and its
  Laplacian `∂_t p(t, ·, x)` by `F = C t^{-2} e^{-D²/(C t)}`, by Taylor's formula with the step `t e^{-D²/(C t)}` and the bound on
  the second time derivative; the oscillation estimate at the radius `3r` with `R = 3√t` and the Caccioppoli inequality at the
  radius `r` then give `‖∇v‖_{L̲²(𝒞_∞ ∩ B_r(y))} ≤ C (U/R + R F) ≤ C t^{-3/2} e^{-D²/(C t)}`.
- **The second time derivative.** The bound `‖Δ² P_{s/2}‖_{2→2} ≤ C s^{-2}` of the spectral theorem is replaced by the signs of
  `r ↦ p_r(z, z)` and of its first three derivatives, which give `∂_r² p_r(z, z) ≤ 8 r^{-2} p_{r/4}(z, z)`, and the Cauchy–Schwarz
  inequality in `p_s = P_{s/2} P_{s/2}`.
- **Exit times.** The bound `sup_z E_z τ_ρ ≤ C ρ²`, obtained in probability by iterating `P_z(τ_ρ > Aρ²) ≤ 1/2`, is proved for
  the exit-time function through the monotonicity of `s ↦ Σ_{w ∈ A} p_s(z, w) e(w) + s`, and `|v − h| ≤ F e` (Dynkin's formula)
  through the minimum principle.

## Theorem 2 of Dario and Gu for d ≥ 3 from Theorem 1, and in every dimension

The part `d ≥ 3` of the quantitative Green estimate `LatticeProb.External.SupercriticalBondGreenQuantitative` (Dario and
Gu, Theorem 2, (1.10)) is the statement `SupercriticalBondGreenQuantitativeThree`, and the whole input follows from it and its
planar case (`supercriticalBondGreenQuantitative_of_two_of_three`). It is proved from Theorem 1 of Dario and Gu in dimension
`d` (`DarioGuHeatKernelD d`, a named statement for the heat kernel `vsrwHeat (openGraph ω) (2d)` of the variable speed walk)
and the small-time bound `p(t, x, y) ≤ C e^{-|x - y|/C}` for `t ≤ |x - y|` (`OpenHeatSmallTimeD d`, a consequence of the
Carne–Varopoulos bound, Proposition 2.15), along §5 of the source: the Green column with pole `y` is the time integral
`∫_0^∞ p(t, ·, y) dt` (it solves `−Δg = δ_y` and tends to zero; Green columns for `d ≥ 3` are unique), the homogenized Green
function is `θ^{-1} ∫_0^∞ p̄(t, ·) dt = Γ(d/2 − 1) |z|^{2−d} / (2 π^{d/2} σ θ)`, and the time integral of the error of Theorem 1,
split at `t = |x − y|`, is at most `C |x − y|^{1 − d + δ}`. With the planar case proved from Proposition 2.13 (previous
section), the input in every dimension follows from Proposition 2.13 in dimension two and `DarioGuHeatKernelD d`,
`OpenHeatSmallTimeD d` for `d ≥ 3` (`supercriticalBondGreenQuantitative_of_flux_heatKernel`). The small-time bound is
proved: `openHeatD` is `bondHeat` and `‖edzD x y‖` is the Euclidean distance `latticeDist x y`, both by definition, so
`OpenHeatSmallTimeD d` is `HeatSmallTimeD d` (`openHeatSmallTimeD_holds`, from `heatSmallTimeD_holds`; see
[The heat kernel and the Gaussian upper bound of Barlow in every dimension](#the-heat-kernel-and-the-gaussian-upper-bound-of-barlow-in-every-dimension)).
Proposition 2.13 is proved too (`darioGuFluxWeakNormTwo_holds`), so only Theorem 1 of Dario and Gu in dimension `d`
remains for `d ≥ 3` (`ProvedFluxWeakNorm.supercriticalBondGreenQuantitative_of_heatKernel`).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Green.SupercriticalBondGreenQuantitativeThree`](Rigidity/Proofs/Green/GreenQuantitativeAllDim.lean), [`supercriticalBondGreenQuantitative_of_two_of_three`](Rigidity/Proofs/Green/GreenQuantitativeAllDim.lean) | The part `d ≥ 3` of the input, and the input from its planar part and its part `d ≥ 3`. |
| [`gaussianHeatD`](Rigidity/Proofs/Green/GaussianTimeIntegral.lean), [`integral_gaussianHeatD`](Rigidity/Proofs/Green/GaussianTimeIntegral.lean), [`inv_mul_integral_gaussianHeatD_eq`](Rigidity/Proofs/Green/GaussianTimeIntegral.lean) | The Gaussian kernel of `ℝ^d`, its time integral, and `θ^{-1} ∫_0^∞ p̄(t, z) dt = continuumGreen d (σθ/2) z` for `d ≥ 3`. |
| [`HeatBoundsD`](Rigidity/Proofs/Green/GreenTimeIntegralThree.lean), [`HeatBoundsD.laplacian_timeGreenD`](Rigidity/Proofs/Green/GreenTimeIntegralThree.lean), [`HeatBoundsD.abs_timeGreenD_sub_le`](Rigidity/Proofs/Green/GreenQuantitativeThree.lean), [`HeatBoundsD.isGreenColumn_timeGreenD`](Rigidity/Proofs/Green/GreenQuantitativeThree.lean) | At one configuration, under the bounds of Theorem 1 and the small-time bound: the time integral of the heat kernel solves `−Δg = δ_y`, is within `C \|x − y\|^{2−2β}` of the homogenized Green function, and is a Green column. |
| [`DarioGuHeatKernelD`](Rigidity/Proofs/Green/GreenQuantitativeThree.lean), [`OpenHeatSmallTimeD`](Rigidity/Proofs/Green/GreenQuantitativeThree.lean), [`supercriticalBondGreenQuantitativeThree_of_heatKernel`](Rigidity/Proofs/Green/GreenQuantitativeThree.lean), [`Rigidity.Assembly.WithProvedBarlow.supercriticalBondGreenQuantitative_of_flux_heatKernel`](Rigidity/Proofs/Assembly/GreenQuantitativeEveryDim.lean) | Theorem 1 and the small-time bound in dimension `d` as named statements; Theorem 2 for `d ≥ 3` from them; the input in every dimension. |
| [`openHeatSmallTimeD_holds`](Rigidity/Proofs/Assembly/GreenQuantitativeEveryDim.lean), [`Rigidity.Assembly.ProvedFluxWeakNorm.supercriticalBondGreenQuantitative_of_heatKernel`](Rigidity/Proofs/Assembly/GreenQuantitativeEveryDim.lean) | The small-time bound in dimension `d`; the input in every dimension from `DarioGuHeatKernelD d` for `d ≥ 3` alone. |
| [`heatFlowG`](Rigidity/Proofs/Green/HeatFlowGraph.lean), [`hasSum_sq_heatFlowG_le`](Rigidity/Proofs/Green/HeatFlowGraph.lean), [`sq_heatFlowG_le_diag`](Rigidity/Proofs/Green/HeatFlowGraph.lean), [`sq_laplacian_heatFlowG_le`](Rigidity/Proofs/Green/HeatFlowGraph.lean) | The heat semigroup of a graph of bounded degree on `ℓ²`: a contraction, `(P_t f)(z)² ≤ p_{2t}(z, z) ‖f‖²` and `(ΔP_t f)(z)² ≤ 8 (2t)^{-2} p_{t/2}(z, z) ‖f‖²`. |

The thirteen reports for the declarations of this section are in [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Departures from Dario and Gu: the time integral is split at `t = |x − y|`, and the Gaussian kernel at small times is bounded
through the Gamma integral `∫_0^∞ t^{-d/2} e^{-a/t} dt = a^{1-d/2} Γ(d/2 − 1)` after the factor `e^{-|x−y|/(4σ)}` is taken out;
the minimal scale is `max(T(y), 1)` with `T(y)` the minimal time of Theorem 1.

## Good balls of the infinite cluster and Proposition 2.7 of Dario and Gu in every dimension

The volume regularity and the weak Poincaré inequality on the Euclidean balls of the supercritical infinite cluster are proved
in every dimension `d ≥ 2`, in particular in every `d ≥ 3`, where they are the percolation input of the Gaussian upper bound of
Barlow, in the forms of M. T. Barlow (*Random walks on supercritical percolation clusters*, Ann. Probab. 32 (2004), Definition 1.7,
Theorem 2.18 and Lemma 2.19) and of Dario and Gu (Proposition 2.7, weak form). The ball `𝒞_∞ ∩ B_r(z)` is good
(`IsGoodBall ω K C_V C_P L z r`) when `C_V r^d ≤ |𝒞_∞ ∩ B_r(z)|` and, for every `u`,
`Σ_{𝒞_∞ ∩ B_r(z)} (u − (u)_{𝒞_∞ ∩ B_r(z)})² ≤ C_P r² Σ_{x ∈ U} Σ_{z' ∈ U, z' ∼ x} (u(z') − u(x))²` with `U = 𝒞_∞ ∩ B_{Lr}(z)`
and the sum over the open edges.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.WeakPoincare.clusterGoodBalls_holds`](Rigidity/Proofs/WeakPoincare/GoodBallsHolds.lean) | `ClusterGoodBalls d`, `d ≥ 2`: Barlow's Theorem 2.18 (a), (b) with the random scale of Lemma 2.19 at a fixed centre: for `R ≥ M(y) ≤ O_s(C)` the ball `𝒞_∞ ∩ B_R(y)` is good with `C_V = C⁻¹`, `C_P = C` and a dilation `L` (the proof gives `L = 12d`), and `\|𝒞_∞ ∩ B_R(y)\| ≤ C R^d`. |
| [`clusterVeryGoodBalls_holds`](Rigidity/Proofs/WeakPoincare/VeryGood.lean), [`clusterVeryGoodBalls_of_goodBalls`](Rigidity/Proofs/WeakPoincare/VeryGood.lean) | `ClusterVeryGoodBalls d`: Barlow's Theorem 2.18 (c) with Lemma 2.19: for `θ > 0` and `A ≥ 1`, above a random scale `S(y) ≤ O_s(C')` every ball `𝒞_∞ ∩ B_r(z)` with `\|z − y\| ≤ A R` and `r ≥ R^θ` is good, with `C_V`, `C_P`, `L` not depending on `θ` and `A`. |
| [`clusterPoincare_holds`](Rigidity/Proofs/WeakPoincare/VeryGood.lean) | `ClusterPoincare d`: Proposition 2.7 of Dario and Gu, weak form, `p = 2`: `‖u − (u)‖_{L̲²(𝒞_∞ ∩ B_R(y))} ≤ C R ‖∇u‖_{L̲²(𝒞_∞ ∩ B_{LR}(y))}` for `R ≥ M(y) ≤ O_s(C)`. |
| [`planarVeryGoodBalls_holds`](Rigidity/Proofs/WeakPoincare/PlanarVeryGood.lean) | the case `d = 2` of `ClusterVeryGoodBalls`, `θ ∈ (0, 1]`, `A = 1`, with the planar balls, averages and distance of `Rigidity.Green` and the good ball written out. |
| [`sum_sq_sub_finAvg_clusterBall_le`](Rigidity/Proofs/WeakPoincare/Ball.lean) | the deterministic part: on the partition event, if the partition cubes of the triple `3□` of the triadic cube of scale `m` around `y` have scale at most `m − 3` and `Σ_{3□} ρ^{d(d+2)} ≤ A` for a bound `ρ` of the reach of the partition, then `Σ_{𝒞_∞ ∩ B_R(y)} (u − (u))² ≤ K A^{2/d} Σ_{edges of 𝒞_∞ ∩ B_ρ'(y)} \|∇u\|²` for `2R ≤ 3^m` and `ρ' ≥ 2d 3^m`. |

The proof is that of dimension two (`clusterPoincareTwo_holds`), with the partition into good cubes of Armstrong and Dario in
every dimension (Percolation-Cluster-Homogenization): their Sobolev inequality (Proposition 3.4, `s = 2`) on the cluster of the
triple of the triadic cube of scale `m` around `y`, turned into a Poincaré inequality by Hölder's inequality with the exponents
`(d+2)/2` and `(d+2)/d`; the vertices of `𝒞_∞ ∩ B_R(y)` joined to the anchors of their partition cubes (their Lemma 2.8); the
concentration of the stopping sizes of the partition into coarsely good cubes (their Proposition 2.4, with the power
`d(d+2)`), which dominate the reach of the partition, through a minimal scale on the `3^d` cubes of scale `m` around `y`; and
the lower bound on the volume of the cluster in balls (Proposition A.1 of Dario and Gu, in every dimension). The very good
balls follow by Markov's inequality and a union bound over the centres in a box of radius `⌈A 3^{m+1}⌉`, with a second minimal
scale.

Departures from Barlow: the balls are Euclidean (Barlow uses the balls of the graph distance of `𝒞_∞`), the measure is the
counting measure (Barlow's `μ_x` is the number of open edges at `x`) and the centre is any lattice point; the very good balls
are stated for all radii `r ≥ R^θ` (Barlow: `N_B ≤ r ≤ R`, `N_B ≤ R^{1/(d+2)}`). The Euclidean balls are a different family
from Barlow's balls of the graph distance, not a change of constants. The counting measure changes the constants only
(`1 ≤ μ_x ≤ 2d` on `𝒞_∞`); the other changes are those of the statements used by Dario and Gu. Proposition 2.7 of Dario and
Gu is stated in its weak form: the printed form, with the gradient on the same ball, fails in every dimension (see
`ClusterPoincareTwo`).

The six reports for the declarations of this section are in [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

## The Gaussian upper bound of Barlow in dimension two

The upper bound (0.4) of Theorem 1 of M. T. Barlow (*Random walks on supercritical percolation clusters*, Ann. Probab.
32 (2004)), with the tail (0.5) of the random time, in the form quoted by Dario and Gu as Theorem 4, is the input
`BarlowGaussianUpperBoundTwo`: for `p_c(2) < p < 1` there are `s, C > 0` and, for each `y`, a measurable time
`T_y ≤ O_s(C)` such that almost surely, if `y ∈ 𝒞_∞`, then `p_t(x, y) ≤ Φ_C(t, |x − y|)` for `t ≥ T_y` and `x ∈ 𝒞_∞`,
where `p_t` is the heat kernel of the variable-speed walk with unit conductances on the open edges of the planar
cluster. It is proved (`barlowGaussianUpperBoundTwo_of_veryGood`) along Sections 3 and 6 of the source, from the
Carne–Varopoulos bound (`carneVaropoulosTwo_holds`, Lemma 1.1 there) and `ClusterVeryGoodBallsTwo`, the very good
balls of Barlow's Theorem 2.18(c) and Lemma 2.19 for Euclidean balls of the cluster, with centres at any lattice point
and no upper bound on `r`: for every `θ ∈ (0, 1]`
there are a random scale `S_y ≤ O_s(C)` and constants `C_V, C_P > 0`, `L ≥ 1` such that, for `R ≥ S_y`, every ball
`B(z, r) ∩ 𝒞_∞` with `|z − y| ≤ R` and `r ≥ R^θ` has at least `C_V r²` points and satisfies
`Σ_{B(z, r) ∩ 𝒞_∞} (u − ū)² ≤ C_P r² E_{B(z, Lr) ∩ 𝒞_∞}(u)`. The proof uses `θ = 1/64`. The percolation estimates of
Section 2 of the source that give `ClusterVeryGoodBallsTwo` are proved in
[Good balls of the infinite cluster and Proposition 2.7 of Dario and Gu in every dimension](#good-balls-of-the-infinite-cluster-and-proposition-27-of-dario-and-gu-in-every-dimension):
it is the case `d = 2` of `clusterVeryGoodBalls_holds`, in the planar form `planarVeryGoodBalls_holds`
(`clusterVeryGoodBallsTwo_holds`). The Gaussian upper bound therefore holds with no hypothesis
(`barlowGaussianUpperBoundTwo_holds`). `Rigidity.Assembly.WithProvedBarlow.fast_decay_of_sections` and
`fast_decay_of_flux_gradient` restate `fast_decay_of_sections_barlow` and `fast_decay_of_flux_gradient_barlow`
(Theorem 1.3) without `BarlowGaussianUpperBoundTwo`, and `fast_decay_of_sections_veryGood` and
`fast_decay_of_flux_gradient_veryGood` restate them with `ClusterVeryGoodBallsTwo` in its place.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Barlow.tsum_mul_openLaplacian`](Rigidity/Proofs/Barlow/HeatEnergy.lean), [`hasDerivAt_openHeat_two_mul`](Rigidity/Proofs/Barlow/HeatEnergy.lean) | Lemma 1.6, the discrete Gauss–Green formula `Σ_x f Δf = −½ Σ_x Σ_{z ∼ x} (f(z) − f(x))²` for a summable bounded `f`, and the energy identity of the proof of Proposition 3.1, `d/dt p_{2t}(x, x) = −Σ_y Σ_{z ∼ y} (p_t(x, z) − p_t(x, y))²`. |
| [`openHeat_diag_le_of_good`](Rigidity/Proofs/Barlow/OnDiagonal.lean), [`openHeat_le_of_good`](Rigidity/Proofs/Barlow/OnDiagonal.lean) | Proposition 3.1 and Corollary 3.2: if the balls `B(z, r)` with `\|z − x₀\| ≤ R` and `N ≤ r ≤ R/18` are good and `p_s(x, y) ≤ ε` for `x` in the cluster, `s ≤ R` and `\|y − x\| ≥ R/18` (`ε N² C_V² ≤ 25`, `4εR ≤ 1`), then `p_{2t}(x₁, x₁) ≤ C/t` for `\|x₁ − x₀\| ≤ 8R/9` and `2 C_P L² C_V N⁴ ≤ t ≤ R`, and `p_{2t}(x₁, y) ≤ C/t` for every `y` when `\|x₁ − x₀\| ≤ 7R/9` and `t ≤ R/2`. |
| [`neg_log_le_heatEntropy`](Rigidity/Proofs/Barlow/MeanDisplacement.lean), [`heatEntropy_le_log_meanDist`](Rigidity/Proofs/Barlow/MeanDisplacement.lean), [`meanDist_le_of_entropy`](Rigidity/Proofs/Barlow/MeanDisplacement.lean) | Lemma 3.3 and the upper bound of Proposition 3.4, for `M(t) = E^x\|Y_t − x\|` and `Q(t) = −Σ_y p_t(x, y) log p_t(x, y)`: `Q(t) ≥ −log B` if `p_t(x, ·) ≤ B`; `Q(t) ≤ 25 + 2 log M(t)` if `M(t) ≥ 1/2`; and `M(t) ≤ 2(31 − c₁ + 2 log 4) √t` if `Q(s) ≥ c₁ + log s` on `[T₀, t]`, `1 ≤ T₀`, `T₀² ≤ t` and `M(t) ≥ 1/2`. |
| [`exitGen_le_mul_of_subset`](Rigidity/Proofs/Barlow/ExitTime.lean), [`mul_exitProb_le`](Rigidity/Proofs/Barlow/ExitTime.lean) | The strong Markov property at the exit time of `B ⊆ A` and optional stopping for a supersolution, for the lazy jump chain of the walk, stated for the exit probabilities `P^x(σ_A ≤ n)` and the truncated generating functions `E^x[s^{σ_A}; σ_A ≤ n]`. |
| [`exitProb_clBall_le`](Rigidity/Proofs/Barlow/ExitTail.lean), [`exitProb_clBall_le_exp`](Rigidity/Proofs/Barlow/ExitTail.lean) | Lemmas 3.5 and 3.6 and Proposition 3.7 for the jump chain: `(r − M̄) P^x(σ(x, r) ≤ n) ≤ E^x\|X_{2n} − x\|` if `E^z\|X_k − z\| ≤ M̄` for `n ≤ k ≤ 2n` at the points `z` with `\|z − x\| < r + 1`; and `P^x(σ(x, m(r + 1)) ≤ N) ≤ e^{8aN} (3/4)^m` if `P^z(σ(z, r) ≤ k) ≤ 1/2 + ak` for `k ≤ N` at the centres `z` within `D` of `x₀`, `0 < a ≤ 1/8` and `\|x − x₀\| + m(r + 1) ≤ D`. |
| [`BarlowRegion.tsum_far_le`](Rigidity/Proofs/Barlow/GaussianTail.lean) | Proposition 3.7 for the continuous-time walk: `P^x(\|Y_t − x\| ≥ ρ) ≤ (4/3) e^{−c₆ ρ²/t} + e^{−t}` for `κ ≤ ρ ≤ R/9`, `ρ r₁ ≤ κ t`, `1 ≤ t ≤ R/36` and `\|x − x₀\| ≤ R/3`, under the hypotheses of Proposition 3.1 (`BarlowRegion`). |
| [`BarlowRegion.openHeat_le_gauss`](Rigidity/Proofs/Barlow/GaussianBound.lean) | Theorem 3.8, under `BarlowRegion` with `9 ≤ R` and `n_* ≤ 2R` and the Carne–Varopoulos bound `p_s(a, b) ≤ C e^{−\|a − b\|²/(Cs)}` for `\|a − b\| ≤ s`: `p_t(x, y) ≤ C_G t^{−1} e^{−c_G \|x − y\|²/t}` for `x, y` in the cluster within `R/3` of `x₀`, `T_G ≤ t ≤ R/36` and `\|x − y\| ≤ t`, where `T_G ≤ c_T N^{16}` (`barlowTG_le`). |
| [`barlowGaussianUpperBoundTwo_of_veryGood`](Rigidity/Proofs/Barlow/GaussianHolds.lean) | The upper bound of Proposition 6.1 and of Theorem 1: `ClusterVeryGoodBallsTwo → BarlowGaussianUpperBoundTwo`, with `T_y = max(S_y/36, k₀)`; for `\|x − y\| > t` the bound is the Carne–Varopoulos bound. |
| [`clusterVeryGoodBallsTwo_holds`](Rigidity/Proofs/Barlow/UpperBoundHolds.lean), [`barlowGaussianUpperBoundTwo_holds`](Rigidity/Proofs/Barlow/UpperBoundHolds.lean) | `ClusterVeryGoodBallsTwo`, from `planarVeryGoodBalls_holds`, and the upper bound of Theorem 1, `BarlowGaussianUpperBoundTwo`, with no hypothesis. |
| [`Rigidity.Assembly.WithPlanarInputs.fast_decay_of_sections_veryGood`](Rigidity/Proofs/Assembly/PlanarDarioGuVeryGood.lean), [`fast_decay_of_flux_gradient_veryGood`](Rigidity/Proofs/Assembly/PlanarDarioGuVeryGood.lean) | Theorem 1.3 from `hSec` (or from Proposition 2.13 and Theorem 3 of Dario and Gu) and `ClusterVeryGoodBallsTwo`. |
| [`Rigidity.Assembly.WithProvedBarlow.fast_decay_of_sections`](Rigidity/Proofs/Assembly/ProvedBarlow.lean), [`fast_decay_of_flux_gradient`](Rigidity/Proofs/Assembly/ProvedBarlow.lean) | Theorem 1.3 from `hSec` alone, or from Proposition 2.13 and Theorem 3 of Dario and Gu alone. |

The twenty reports for the declarations of this section are in [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

Departures from Barlow:

- **Euclidean balls.** The balls are the sets `B(z, r) ∩ 𝒞_∞` of the Euclidean distance, not the balls of the chemical
  distance, and the good balls of Definition 1.7 are defined with them, with the energy of the Poincaré inequality taken
  on the ball of radius `Lr`. The Gaussian bound is stated with the Euclidean distance, as Dario and Gu quote it; the
  step of the proof of Theorem 1 that replaces the chemical distance by `|x − y|₁` is not needed.
- **The variable-speed walk.** The walk is the variable-speed walk of Dario and Gu, with rate one on each open edge, in
  place of the constant-speed walk `Y` of the source, whose kernel `q_t` is taken with respect to the degree measure.
  Its heat kernel is `p_t(x, y) = E[P^x(X_{N_{4t}} = y)]`, where `X` is the lazy jump chain that stays put with
  probability `1 − deg(x)/4` and `N` is a Poisson clock of rate one.
- **Proposition 3.1 and Corollary 3.2.** The bound (1.7) is not used: the comparison argument starts with the good balls
  of radius `N`, and the bounds are proved for `t ≤ R` in place of `t ≤ c R²/log R`, which is enough since Proposition
  6.1 applies them with `R = 36t`. The bound `p_s(x, y) ≤ ε` at distance `R/18` comes from the Carne–Varopoulos bound,
  in place of Lemma 1.1(b).
- **Proposition 3.4.** The integral argument is replaced by the monotonicity of `M(s) − 4√s − √s (Q(s) − c₁ − log s)` on
  `[T₀, t]`; only the upper bound of `M(t)` is proved.
- **Exit times on the jump chain with a Poisson clock.** Lemmas 3.5 and 3.6 and Proposition 3.7 are proved for the lazy
  jump chain: the strong Markov property at exit times is replaced by first-step recursions for the exit probabilities
  and the truncated generating functions, and optional stopping by backward induction; Lemma 3.6 enters through the
  submultiplicativity of `E^x[s^σ]` along nested balls. The continuous-time walk enters through the Poisson clock: the
  mean displacement of the jump chain is bounded by that of the walk, `E^z\|X_k − z\| ≤ M(z, k/4) + 6√k`
  (`discMean_le_meanDist_add`), and the clock adds the term `e^{−t}` to Proposition 3.7.
- **Theorem 3.8 by the Chapman–Kolmogorov equation at `t/2`.** In place of the decomposition (3.20)–(3.21) at the exit
  time of `B(x, |x − y|/2)`, `p_t(x, y) = Σ_z p_{t/2}(x, z) p_{t/2}(z, y)` is split according to `|z − x| ≥ |x − y|/2`
  or `|z − y| ≥ |x − y|/2`; the factor on the near side is bounded by Corollary 3.2 and the sum on the far side by
  Proposition 3.7. At distances `|x − y| > κt/r₁` the Carne–Varopoulos bound is used directly.
- **Proposition 6.1.** The ball is `B(y, R)` with `R = 36t` and `N = R^{1/64}`; the times of Section 3 are polynomial in
  `N` (`T_G ≤ c_T N^{16}`), so the hypotheses of Section 3 hold for `t ≥ max(S_y/36, k₀)`.

## The heat kernel and the Gaussian upper bound of Barlow in every dimension

For a bond configuration `ω` of `ℤ^d`, `bondHeat ω t x y` is the heat kernel of the variable-speed walk with rate one
on each open edge: the Poisson average `p_t(x, y) = E[P^x(X_{N_{2dt}} = y)]` of the lazy jump chain that stays put
with probability `1 − deg(x)/(2d)`, with the semigroup property, the symmetry, mass one, the heat equation and joint
measurability in `(ω, t)`; in dimension two it is the planar kernel `openHeat` (`bondHeat_two`, by definition).
The Carne–Varopoulos bound `CarneVaropoulos d` (Proposition 2.15 of Dario and Gu, Davies 1993) holds with
`C = 100 d²`, and its small-time case `HeatSmallTimeD d` with `C = 8d`. The Gaussian upper bound
`BarlowGaussianUpperBound d` is the `d`-dimensional form of `BarlowGaussianUpperBoundTwo`, with
`Φ_C(t, r) = C t^{−d/2} exp(−r²/(Ct))` for `r ≤ t` and `C t^{−d/2} exp(−(r/C)(1 + log(r/t)))` for `r > t`
(`dgPhiDim`; the prefactor is written `(√t)^{−d}`, and `dgPhiDim_eq_rpow` gives the power `t^{−d/2}`). It is proved
for `d ≥ 2` along Sections 3 and 6 of Barlow from the Carne–Varopoulos bound and `ClusterVeryGoodBalls d`
(`clusterVeryGoodBalls_holds`, with `θ = 1/(4d + 12)` and `A = 1`), and gives `BarlowGaussianUpperBoundTwo` again for
`d = 2` (`barlowGaussianUpperBoundTwo_of_lattice`). The proof is the planar one of
[The Gaussian upper bound of Barlow in dimension two](#the-gaussian-upper-bound-of-barlow-in-dimension-two), in
[`Rigidity/Proofs/BarlowLattice/`](Rigidity/Proofs/BarlowLattice/) and
[`Rigidity/Proofs/Green/Bond*.lean`](Rigidity/Proofs/Green/), with the changes listed below.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Green.hasSum_bondHeat_mul`](Rigidity/Proofs/Green/BondHeat.lean), [`bondHeat_symm`](Rigidity/Proofs/Green/BondHeat.lean), [`hasSum_bondHeat`](Rigidity/Proofs/Green/BondHeat.lean), [`hasDerivAt_bondHeat`](Rigidity/Proofs/Green/BondHeat.lean), [`measurable_bondHeat`](Rigidity/Proofs/Green/BondHeat.lean) | `Σ_y p_s(x, y) p_t(y, z) = p_{s+t}(x, z)`, `p_t(x, y) = p_t(y, x)`, `Σ_y p_t(x, y) = 1` for `s, t ≥ 0`, `∂_t p_t(x, y) = Σ_{z ∼ x} (p_t(z, y) − p_t(x, y))`, and the measurability of `(ω, t) ↦ p_t(x, y)`. |
| [`carneVaropoulos_holds`](Rigidity/Proofs/Green/BondCarneVaropoulos.lean), [`carneVaropoulosTwo_of_carneVaropoulos`](Rigidity/Proofs/Green/BondCarneVaropoulos.lean), [`heatSmallTimeD_holds`](Rigidity/Proofs/Green/BondCarneVaropoulos.lean) | `CarneVaropoulos d`: on an infinite component, `p_t(x, y) ≤ C e^{−\|x − y\|²/(Ct)}` for `\|x − y\| ≤ t` and `p_t(x, y) ≤ C e^{−(\|x − y\|/C)(1 + log(\|x − y\|/t))}` for `t ≤ \|x − y\|`, with `C = 100 d²`; the case `d = 2` is `CarneVaropoulosTwo`; and `HeatSmallTimeD d`: `p_t(x, y) ≤ C e^{−\|x − y\|/C}` for `0 < t ≤ \|x − y\|`. |
| [`dgPhiDim_eq_rpow`](Rigidity/Proofs/Green/BondGaussianInputs.lean), [`barlowGaussianUpperBoundTwo_of_dim`](Rigidity/Proofs/Green/BondGaussianInputs.lean) | `Φ_C` in dimension `d` with the prefactor `t^{−d/2}`, and `BarlowGaussianUpperBound 2 → BarlowGaussianUpperBoundTwo`. |
| [`Rigidity.BarlowLattice.tsum_mul_openLaplacian`](Rigidity/Proofs/BarlowLattice/HeatEnergy.lean), [`hasDerivAt_bondHeat_two_mul`](Rigidity/Proofs/BarlowLattice/HeatEnergy.lean) | Lemma 1.6 and the energy identity `d/dt p_{2t}(x, x) = −Σ_y Σ_{z ∼ y} (p_t(x, z) − p_t(x, y))²` on `ℤ^d`. |
| [`bondHeat_diag_le_of_good`](Rigidity/Proofs/BarlowLattice/OnDiagonal.lean), [`bondHeat_le_of_good`](Rigidity/Proofs/BarlowLattice/OnDiagonal.lean) | Proposition 3.1 and Corollary 3.2: if the balls `B(z, r)` with `\|z − x₀\| ≤ R` and `N ≤ r ≤ R/18` are good (volume `C_V r^d`) and `p_s(x, y) ≤ ε` at distance `R/18` for `s ≤ R` (`ε N^d C_V² ≤ 5^d`, `4ε R^{d/2} ≤ 1`), then `p_{2t}(x₁, x₁) ≤ C t^{−d/2}` for `\|x₁ − x₀\| ≤ 8R/9` and `2 C_P L^d C_V N^{d+2} ≤ t ≤ R`, and `p_{2t}(x₁, y) ≤ C t^{−d/2}` for `\|x₁ − x₀\| ≤ 7R/9`, `t ≤ R/2`. |
| [`neg_log_le_heatEntropy`](Rigidity/Proofs/BarlowLattice/MeanDisplacement.lean), [`heatEntropy_le_log_meanDist`](Rigidity/Proofs/BarlowLattice/MeanDisplacement.lean), [`meanDist_le_of_entropy`](Rigidity/Proofs/BarlowLattice/MeanDisplacement.lean) | Lemma 3.3 and the upper bound of Proposition 3.4: `Q(t) ≥ −log B` if `p_t(x, ·) ≤ B`; `Q(t) ≤ K_d + d log M(t)` if `M(t) ≥ 1/2`, `K_d = 1 + (6d)^d`; and `M(t) ≤ 2(3d + K_d − c₁ + d log(2d)) √t` if `Q(s) ≥ c₁ + (d/2) log s` on `[T₀, t]`, `T₀² ≤ t`. |
| [`exitGen_le_mul_of_subset`](Rigidity/Proofs/BarlowLattice/ExitTime.lean), [`mul_exitProb_le`](Rigidity/Proofs/BarlowLattice/ExitTime.lean), [`exitProb_clBall_le`](Rigidity/Proofs/BarlowLattice/ExitTail.lean), [`exitProb_clBall_le_exp`](Rigidity/Proofs/BarlowLattice/ExitTail.lean) | The exit-time estimates of the planar section (strong Markov property, optional stopping, Lemmas 3.5 and 3.6 and Proposition 3.7 for the jump chain) for the lazy jump chain on `ℤ^d`. |
| [`BarlowRegion.tsum_far_le`](Rigidity/Proofs/BarlowLattice/GaussianTail.lean), [`BarlowRegion.bondHeat_le_gauss`](Rigidity/Proofs/BarlowLattice/GaussianBound.lean) | Proposition 3.7 for the continuous-time walk and Theorem 3.8: `p_t(x, y) ≤ C_G t^{−d/2} e^{−c_G \|x − y\|²/t}` for `x, y` in the cluster within `R/3` of `x₀`, `T_G ≤ t ≤ R/36` and `\|x − y\| ≤ t`, where `T_G ≤ c_T N^{4(d+2)}`. |
| [`barlowGaussianUpperBound_of_veryGood`](Rigidity/Proofs/BarlowLattice/GaussianHolds.lean), [`barlowGaussianUpperBound_holds`](Rigidity/Proofs/BarlowLattice/GaussianHolds.lean), [`barlowGaussianUpperBoundTwo_of_lattice`](Rigidity/Proofs/BarlowLattice/GaussianHolds.lean) | Proposition 6.1 and Theorem 1: `ClusterVeryGoodBalls d → BarlowGaussianUpperBound d`; `BarlowGaussianUpperBound d` for `d ≥ 2` with no hypothesis; and `BarlowGaussianUpperBoundTwo` as its case `d = 2`. |

The twenty-six reports for the declarations of this section are in [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

The departures from Barlow are those of the planar proof (Euclidean balls, the variable-speed walk, the initial phase
and the range `t ≤ R` of Proposition 3.1, the monotone function of Proposition 3.4, the exit arguments on the jump
chain, Theorem 3.8 by the Chapman–Kolmogorov equation at `t/2`), with these changes for `d`:

- **The rate.** The Poisson clock has rate `2d` (the degree bound of `ℤ^d`), so that `M(t) ≤ 2dt`, the jump chain at
  step `k` is compared with the walk at time `k/(2d)`, the walk makes at most `8dt` steps by time `t` except with
  probability `e^{−t}`, and Lemma 3.5 is applied for `n ≤ dR` steps.
- **Proposition 3.1.** The covering bound (3.4) reads `Σ_{B(x₀, ρ)} f² ≤ 5^d C_P L^d C_V^{−1} r² E(f) + 5^d C_V^{−2} r^{−d}`;
  the choice `r^d = 4β/ψ` gives `ψ' ≤ −c ψ^{1+2/d}`, which is integrated as `(ψ^{2/d})' ≤ −(2c/d)(ψ^{2/d})²`; the initial
  time is `T₀ = C_P L^d C_V N^{d+2}`.
- **Lemma 3.3.** The lattice sum `Σ_y e^{−\|y − x\|/M} ≤ (6d)^d M^d` (through the product over the coordinates of
  the geometric sums in the `ℓ¹` distance) gives `Q(t) ≤ K_d + d log M(t)`, and the entropy bound enters Proposition 3.4
  as `Q(s) ≥ c₁ + (d/2) log s`.
- **Proposition 6.1.** The ball is `B(y, R)` with `R = 36t` and `N = R^{1/K}`, `K = 4d + 12`: the times of Section 3 are
  polynomial in `N` (`T_G ≤ c_T N^{4(d+2)}`), and `4ε R^{d/2} ≤ 1` follows from `e^{−x} ≤ d!/x^d`. In the regime
  `\|x − y\| > t` the factor `t^{−d/2}` comes from `e^{−t/(2C)} ≤ d! (2C)^d t^{−d}` and `t ≥ 1`.

## Guarantees

- **No `sorry`.** The library has none. The five comparator challenges under
  [`RigidityAudit/`](RigidityAudit/) each contain one intentional statement-level `sorry`, which the
  corresponding solution proves.
- **Standard axioms only.** [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean) prints 1116 axiom
  reports, among them the theorem of each of the 43 proved results, Lemma 5.25 as printed, the six
  propositions that state the quoted results used by the proofs (Proposition 2.3, Theorems 2.4 and
  2.5, Lemma 2.14), the slab connectivity theorem of
  [Slab connectivity above the critical point](#slab-connectivity-above-the-critical-point), the
  four theorems of
  [Well-connected cubes and finite clusters for d ≥ 3](#well-connected-cubes-and-finite-clusters-for-d--3),
  the four theorems of
  [Proposition 2.3 and the density concentration for d = 2](#proposition-23-and-the-density-concentration-for-d--2),
  the two forms of Theorem 1.3 from dimension-two inputs, `WithPlanarInputs.fast_decay` and
  `WithPlanarInputs.fast_decay_of_green_exists`, the three theorems of
  [Density concentration in every dimension](#density-concentration-in-every-dimension), the
  three theorems of
  [Green columns and the coarse-grained cluster for d = 2](#green-columns-and-the-coarse-grained-cluster-for-d--2),
  the twenty-one theorems of [Green columns for d ≥ 3](#green-columns-for-d--3), the thirteen
  declarations of
  [Order-zero regularity in every dimension](#order-zero-regularity-in-every-dimension), the two
  theorems of
  [Multiscale Poincaré inequality](#multiscale-poincaré-inequality), the twenty-one theorems of
  [Partitions into good cubes and functional inequalities on the cluster](#partitions-into-good-cubes-and-functional-inequalities-on-the-cluster),
  the eleven theorems of
  [Localization of the subadditive quantities and the homogenized matrix for d = 2](#localization-of-the-subadditive-quantities-and-the-homogenized-matrix-for-d--2),
  the thirty-five theorems of
  [Energy defects, finite-volume matrices and the identification of the limit for d = 2](#energy-defects-finite-volume-matrices-and-the-identification-of-the-limit-for-d--2),
  the sixty-one theorems and four definitions of
  [Clusters of integer cubes, the Meyers estimate and the coarse energy bounds toward Lemma 5.5](#clusters-of-integer-cubes-the-meyers-estimate-and-the-coarse-energy-bounds-toward-lemma-55),
  the fifty-four theorems and three definitions of
  [The subadditive quantities on the clusters of triadic cubes of Z^d](#the-subadditive-quantities-on-the-clusters-of-triadic-cubes-of-zd),
  the thirty theorems and three definitions of
  [Lemmas 5.8 and 5.9 and the qualitative part of Proposition 5.2 for d = 2](#lemmas-58-and-59-and-the-qualitative-part-of-proposition-52-for-d--2),
  the nineteen theorems of
  [The Dirichlet problem and the excess-decay iteration](#the-dirichlet-problem-and-the-excess-decay-iteration),
  the thirty-eight theorems and two definitions of
  [Lemmas 5.5 and 5.7 in dimension two](#lemmas-55-and-57-in-dimension-two),
  the twelve theorems of
  [The rate of Proposition 5.2 and Lemmas 5.3, 5.10 and 5.11 (Step 2) in dimension two](#the-rate-of-proposition-52-and-lemmas-53-510-and-511-step-2-in-dimension-two),
  the thirteen theorems and one definition of
  [Regularity of order one at the origin from the mesoscopic estimate](#regularity-of-order-one-at-the-origin-from-the-mesoscopic-estimate),
  the twenty-three theorems of
  [Propositions 5.2 and 5.13, Lemma 5.11 and the minimal scales in dimension two](#propositions-52-and-513-lemma-511-and-the-minimal-scales-in-dimension-two),
  the nineteen theorems of
  [Order-zero regularity and the planar corrector input from Lemma 7.1](#order-zero-regularity-and-the-planar-corrector-input-from-lemma-71),
  the twenty-one theorems of
  [Lemma 7.3 at k = 2 and regularity of order one at the origin in dimension two](#lemma-73-at-k--2-and-regularity-of-order-one-at-the-origin-in-dimension-two),
  the seventeen theorems of
  [Theorem 1 of Armstrong and Dario in dimension two](#theorem-1-of-armstrong-and-dario-in-dimension-two),
  the sixteen theorems of
  [Lemma 7.1 and the order-zero regularity in dimension two from Theorem 1](#lemma-71-and-the-order-zero-regularity-in-dimension-two-from-theorem-1),
  the thirty-five theorems of
  [Theorem 1 of Dario in dimension two](#theorem-1-of-dario-in-dimension-two),
  the theorems of
  [Steps 1 and 2 of Lemma 3.3 in flip form and Lemma 3.5 for the planar partition](#steps-1-and-2-of-lemma-33-in-flip-form-and-lemma-35-for-the-planar-partition)
  and the four forms of Theorem 1.3 of
  [`PlanarDarioGu`](Rigidity/Proofs/Assembly/PlanarDarioGu.lean),
  the thirty-three theorems of
  [Proposition 4.3 of Dario and Gu in dimension two](#proposition-43-of-dario-and-gu-in-dimension-two),
  the ten theorems of
  [Theorem 1 of Dario and Gu in dimension two](#theorem-1-of-dario-and-gu-in-dimension-two),
  the thirteen theorems of
  [Section 3 and the isotropy of the homogenized matrix in every dimension](#section-3-and-the-isotropy-of-the-homogenized-matrix-in-every-dimension),
  the twenty-seven theorems of
  [The corrector estimate, the Green column and the Green function estimate in dimension two](#the-corrector-estimate-the-green-column-and-the-green-function-estimate-in-dimension-two),
  the thirty-two theorems of
  [Corrected planes, the dimension of the harmonic functions of linear growth and the corrector input in dimension two](#corrected-planes-the-dimension-of-the-harmonic-functions-of-linear-growth-and-the-corrector-input-in-dimension-two),
  the seven theorems on Lemma 3.2 of Dario from (1.22) in
  [Theorem 1 of Dario in dimension two](#theorem-1-of-dario-in-dimension-two),
  the twenty-three theorems of
  [The quantitative sublinearity of the correctors in dimension two](#the-quantitative-sublinearity-of-the-correctors-in-dimension-two),
  the forty-three theorems of
  [Localization, stationarity and the limit of μ, and Definition 3.9, in every dimension](#localization-stationarity-and-the-limit-of-μ-and-definition-39-in-every-dimension),
  the fifteen theorems of
  [Proposition A.7, Proposition 2.15, Lemma 4.1 and the weak Poincaré inequality](#proposition-a7-proposition-215-lemma-41-and-the-weak-poincaré-inequality),
  the six theorems of
  [Good balls of the infinite cluster and Proposition 2.7 of Dario and Gu in every dimension](#good-balls-of-the-infinite-cluster-and-proposition-27-of-dario-and-gu-in-every-dimension),
  the twenty theorems of
  [The Gaussian upper bound of Barlow in dimension two](#the-gaussian-upper-bound-of-barlow-in-dimension-two),
  the thirty-four theorems of
  [Proposition 2.13 of Dario and Gu in dimension two](#proposition-213-of-dario-and-gu-in-dimension-two),
  the twenty-six theorems of
  [The heat kernel and the Gaussian upper bound of Barlow in every dimension](#the-heat-kernel-and-the-gaussian-upper-bound-of-barlow-in-every-dimension),
  the special case of Lemma 2.13 for unions of lattice squares (`Rigidity.Assembly.polyominoJordan`),
  and the thirty-five theorems of
  [The subadditive quantities of Armstrong and Dario in every dimension: Lemmas 5.3 and 5.4, (5.21) to (5.24) and Step 1 of Lemma 5.10](#the-subadditive-quantities-of-armstrong-and-dario-in-every-dimension-lemmas-53-and-54-521-to-524-and-step-1-of-lemma-510).
  Each of the 1116 reports lists only axioms among `propext`, `Classical.choice` and
  `Quot.sound`. [`scripts/check_axioms.py`](scripts/check_axioms.py) fails on any other axiom, on
  `sorryAx`, or on a missing report. The literature inputs are hypotheses, not axioms, so they do
  not appear in the reports of the theorems.
- **Independent check of the statements.** Theorems 1.1, 1.2, 1.3 and 6.5 are restated using mathlib
  alone in [`RigidityAudit/Lipschitz/`](RigidityAudit/Lipschitz/),
  [`RigidityAudit/IntegerLinearGrowth/`](RigidityAudit/IntegerLinearGrowth/),
  [`RigidityAudit/FastDecay/`](RigidityAudit/FastDecay/) and
  [`RigidityAudit/SlowMixing/`](RigidityAudit/SlowMixing/), and Theorem 6.5 with the regime as its
  only hypothesis, as `Rigidity.Assembly.Unconditional.slow_mixing` proves it, in
  [`RigidityAudit/SlowMixingUnconditional/`](RigidityAudit/SlowMixingUnconditional/). Each
  `Challenge.lean` restates every definition that its statement unfolds to and the literature inputs
  that the theorem takes as hypotheses (none for `SlowMixingUnconditional/`); each `Solution.lean`
  proves the restatement from the library; and
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the two statements
  agree, that only the permitted axioms are used, and replays the proof through an independent
  implementation of the Lean kernel. The other numbered results have no comparator pair.
- **Pinned toolchain and dependencies.** Lean `v4.32.0`, Mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997` and Lattice-Probability
  `7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069`, as recorded in [`lean-toolchain`](lean-toolchain) and
  [`lake-manifest.json`](lake-manifest.json) (see [Building](#building)).
- **The paper is part of the repository.** [`paper/`](paper/) holds the arXiv v2 source, the
  corrected draft, both compiled to PDF, and the list of corrections. The statements follow the
  corrected draft `paper/percolation-harmonic-corrected.tex`, with SHA-256
  `7efc35830365f4965c0e1c77f8ce60527798bee4df760511ea6d0728b3fb5abd`; the arXiv v2 source
  `paper/percolation-harmonic.tex` has SHA-256
  `8a77e097b6e5c2debd4a249d4c9a7721636277817026f87fe18189934adb0b1e`.
- **Literature inputs checked against their sources.** Each of the twelve literature inputs was
  checked against its source in an independent model review; the sources are listed in
  [Assumed literature inputs](#assumed-literature-inputs). The original theorem statements retain these
  hypotheses; eight of them are proved, and the versions described there discharge them.

## Size

`Rigidity/` and `Rigidity.lean`: 784 Lean files with 163,888 lines, on top of mathlib,
Lattice-Probability and Percolation-Cluster-Homogenization. The comparator pairs (17 files, 5,355
lines) and the axiom report `RigidityAudit/Axioms.lean` (1,754 lines) are counted separately.

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

Lattice-Probability has no prebuilt cache, so the first build compiles it as well as the library.
It is a public repository, pinned in [`lake-manifest.json`](lake-manifest.json):

- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069`, the commit of the tag
  `percolation-rigidity-2026-11-03`, which is not on `main`.

The main theorems are in `Rigidity/Proofs/Assembly/Main.lean`; `import Rigidity.Proofs.Assembly.Main`
loads them and what they use.

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

There are two continuous-integration workflows: **CI** builds the library, checks the axiom reports
and builds the comparator pairs; **Comparator audit** runs the comparator on the five pairs. CI runs
on pushes to `main` that change more than documentation, the paper, `formalization.yaml` or
`CITATION.cff`; the comparator audit runs after each successful CI run on `main` (on the commit that CI built) and on manual dispatch. Both workflows can be started
manually from the [Actions page](https://github.com/nitromannitol/Percolation-Rigidity/actions).
See [`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
Rigidity.lean                 the root module
Rigidity/
  Draft/                      the statements of the numbered results, one file per section
  Frozen/                     eight numbered results stated and proved first, with their definitions
  External/                   the literature inputs, stated as propositions
  Steps/                      one Lean proposition per proof step of the paper
  Proofs/                     the proofs of the steps
    Assembly/                 the numbered results, composed from the steps
      Main.lean               the main theorems, from the regime and the literature inputs only
      Unconditional.lean      Theorem 6.5 from the regime only, its literature inputs being proved
      ProvedDensity.lean      Proposition 2.6 and Theorem 1.3 without the density concentration
      ProvedOrderZero.lean    the main theorems without the order-zero regularity
      ProvedGreenColumn.lean  the main theorems with the Green columns and every proved input supplied
      PlanarGreenInputs.lean  Theorem 1.3 from five planar inputs, with the planar Green columns
      PlanarDarioGu.lean      Theorem 1.3 from the Green estimate of Dario and Gu alone, in dimension two
      ProvedBarlow.lean       Theorem 1.3 in dimension two with the Gaussian upper bound of Barlow proved
    Green/                    Green columns and heat kernel bounds of the cluster for d ≥ 3
    Barlow/                   the Gaussian upper bound of Barlow (2004) on the planar cluster
    BarlowLattice/            the Gaussian upper bound of Barlow (2004) on the cluster of ℤ^d
    Corrector/, Poincare/     Dario (2018) and Dario and Gu (2021)
    Regularity/               the corrector input and Theorem 2 (iii) at k = 1 in dimension two from
                              Theorem 1 of Dario, from the results of Percolation-Cluster-Homogenization
  Percolation/                supercritical estimates in boxes for the literature inputs
  Support/                    definitions and lemmas used by the frozen results
RigidityAudit/
  Axioms.lean                 the axiom report of every numbered result and of the further results
  Lipschitz/, IntegerLinearGrowth/, FastDecay/, SlowMixing/
                              the mathlib-only comparator pairs of Theorems 1.1, 1.2, 1.3 and 6.5
  SlowMixingUnconditional/    Theorem 6.5 with the regime as its only hypothesis
paper/                        the arXiv v2 source and the corrected draft (LaTeX and PDF), figures,
                              CORRECTIONS.md, make_corrected.py, the note on the gadget, README.md
scripts/                      check_axioms.py, run_comparators.sh, prefetch_toolchain.py (used by CI)
.github/workflows/            build.yml (CI) and comparator.yml (Comparator audit)
LICENSE                       the Apache License 2.0
CONTRIBUTING.md               build conventions and contribution notes
CITATION.cff                  citation metadata
formalization.yaml            source, statement, automation and review metadata
lakefile.lean, lake-manifest.json, lean-toolchain   the build
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and OpenAI (GPT),
under the direction of Ahmed Bou-Rabee. Every proof is checked by the Lean kernel. The models,
tooling and review process are disclosed in [`formalization.yaml`](formalization.yaml), following the
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
