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
hypotheses. The remaining five are quoted from the literature: four of them (Proposition 2.3,
Theorems 2.4 and 2.5, Lemma 2.14) enter as literature inputs, and the fifth (Lemma 2.13, a fact of
plane topology) is used by no proof. Of the main results, Theorems 1.1, 1.2 and 1.3 are stated as
printed, and Theorem 6.5 as printed with its restriction event made explicit (see
[Standing assumptions and scope](#standing-assumptions-and-scope), item 4); the statements changed by
the corrections are listed in
[Corrections to the published version](#corrections-to-the-published-version).

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and on the
public library [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability).

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
`Rigidity.integer_valued_linear_growth`, whose statement is written out in full.

### All numbered results

The table lists the 48 numbered results in the order of the paper, with their LaTeX labels. Theorems
and lemmas in `Rigidity.Assembly.Main` are in
[`Rigidity/Proofs/Assembly/Main.lean`](Rigidity/Proofs/Assembly/Main.lean), and the other
`Rigidity.Assembly` theorems in `Rigidity/Proofs/Assembly/Section*.lean`. The eight results proved
first, with their own definitions, are in [`Rigidity/Frozen/`](Rigidity/Frozen/). For a statement
in `Rigidity.Assembly`, the definition `Rigidity.Section<n>.<Name>Stmt` that it concludes is in
[`Rigidity/Draft/`](Rigidity/Draft/). A quoted result is marked *quoted*, with the literature input
that states it, if any.

| Paper | Label | Lean declaration | Content |
| --- | --- | --- | --- |
| Theorem 1.1 | `theorem:lipschitz` | `Rigidity.Assembly.Main.lipschitz` | Lipschitz harmonic functions on `𝒞_∞` are constant. |
| Theorem 1.2 | `theorem:integer-valued-linear-growth` | `Rigidity.Assembly.Main.integerValuedLinearGrowth` | Integer-valued harmonic functions of linear growth are constant. |
| Theorem 1.3 | `theorem:fast-decay` | `Rigidity.Assembly.Main.fastDecay` | `d = 2`: integer Laplacian of finite support and decay faster than `\|x\|⁻¹` force finite support. |
| Lemma 2.1 | `lemma:finite-energy` | `Rigidity.finite_flip_full_measure` | A full-measure event still holds, almost surely, after every finite modification of the bonds. |
| Proposition 2.3 | `prop:well-connected` | quoted: `Rigidity.External.WellConnectedInput` | The box `Q_N` is well-connected with probability at least `1 − C exp(−c Nˢ)`. |
| Theorem 2.4 | `theorem:large scale-regularity` | quoted: `LatticeProb.External.ArmstrongDarioOrderZero`, `Rigidity.External.ArmstrongDarioOrderOneOrigin` | Large-scale regularity of harmonic functions on `𝒞_∞` above a minimal scale. |
| Theorem 2.5 | `theorem:first-order-corrector` | quoted: `LatticeProb.External.SupercriticalBondCorrectorInput`, `Rigidity.External.CorrectorQuantitativeInput` | Harmonic functions of linear growth are corrected planes `a + p·x + χ_p`; bounds on the corrector. |
| Proposition 2.6 | `prop:homogenizationellipticgreen` | `Rigidity.Assembly.Main.greenGradientHomogenization` | `∇ₓG(x, y)` is close to `Σᵢ ∇ℓ_{eᵢ}(x) ∂ᵢḠ(x − y)` above a minimal scale. |
| Proposition 2.8 | `prop:green-mixed-derivative` | `Rigidity.mixed_green` | Decay of the mixed derivative `∇ₓ∇_y G` above a minimal scale. |
| Lemma 2.13 | (none) | quoted, not used | A simply connected bounded planar domain whose boundary points are simple is bounded by a Jordan curve. |
| Lemma 2.14 | `lemma:jordan-curve-theorem-on-s2` | quoted: `Rigidity.External.JordanCurveTheoremSphere` | The Jordan curve theorem on the sphere `S²`. |
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
   [Assumed literature inputs](#assumed-literature-inputs).
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
8. **Not formalized.** Lemma 2.13, which no proof uses; the quoted results, which enter as literature
   inputs; the remarks, problems and conjectures; the figures.

## Assumed literature inputs

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
Pisztora, p. 35 (`d ≥ 3`), by a union bound over the subcubes, with `s = 1/(d(10d)²)`.

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
`LatticeProb.External`, in the directory `LatticeProb/External/` of Lattice-Probability. Eight
results use no literature input: Lemma 2.1, Proposition 4.1, Lemmas 4.2 to 4.6 and Proposition 6.4.
The library also declares `Rigidity.External.AntalPisztoraChemicalDistance` (Antal and Pisztora,
Theorem 1.1), which no numbered result uses.

## Guarantees

- **No `sorry`.** The library has none. The four comparator challenges under
  [`RigidityAudit/`](RigidityAudit/) each contain one intentional statement-level `sorry`, which the
  corresponding solution proves.
- **Axioms.** [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean) prints 50 axiom reports: the
  theorem of each of the 43 proved results, Lemma 5.25 as printed, and the six propositions that state
  the quoted results used by the proofs (Proposition 2.3, Theorems 2.4 and 2.5, Lemma 2.14).
  [`scripts/check_axioms.py`](scripts/check_axioms.py) fails on any axiom other than `propext`,
  `Classical.choice` and `Quot.sound`, on `sorryAx`, or on a missing report. The literature inputs are
  hypotheses, not axioms, so they do not appear in the reports of the theorems.
- **Independent check of the statements.** Theorems 1.1, 1.2, 1.3 and 6.5 are restated using mathlib
  alone in [`RigidityAudit/Lipschitz/`](RigidityAudit/Lipschitz/),
  [`RigidityAudit/IntegerLinearGrowth/`](RigidityAudit/IntegerLinearGrowth/),
  [`RigidityAudit/FastDecay/`](RigidityAudit/FastDecay/) and
  [`RigidityAudit/SlowMixing/`](RigidityAudit/SlowMixing/). Each `Challenge.lean` restates every
  definition that its statement unfolds to and the literature inputs that the theorem takes as
  hypotheses; each `Solution.lean` proves the restatement from the library; and
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the two statements
  agree, that only the permitted axioms are used, and replays the proof through an independent
  implementation of the Lean kernel.
- **Literature inputs checked against their sources.** Each of the twelve literature inputs was
  checked against its source in an independent model review; the sources are listed in
  [Assumed literature inputs](#assumed-literature-inputs). The inputs remain assumptions.
- **Pinned toolchain and dependencies.** Lean `v4.32.0`, Mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997` and Lattice-Probability
  `7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069`, as recorded in [`lean-toolchain`](lean-toolchain) and
  [`lake-manifest.json`](lake-manifest.json).
- **The paper is part of the repository**, in [`paper/`](paper/): the arXiv v2 source, the corrected
  draft, both compiled to PDF, and the list of corrections.

## Size

`Rigidity/` and `Rigidity.lean`: 237 Lean files with 64,880 lines, on top of mathlib and
Lattice-Probability. The comparator sources are counted separately.

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
and builds the comparator pairs, on every push to `main`; **Comparator audit** runs the comparator on
the four pairs, on manual dispatch.

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
  Support/                    definitions and lemmas used by the frozen results
RigidityAudit/
  Axioms.lean                 the axiom report of every numbered result
  Lipschitz/, IntegerLinearGrowth/, FastDecay/, SlowMixing/
                              the mathlib-only comparator pairs of Theorems 1.1, 1.2, 1.3 and 6.5
paper/                        the arXiv v2 source and the corrected draft (LaTeX and PDF), figures,
                              CORRECTIONS.md, make_corrected.py, the note on the gadget, README.md
scripts/                      check_axioms.py, run_comparators.sh, prefetch_toolchain.py (used by CI)
.github/workflows/            build.yml (CI) and comparator.yml (Comparator audit)
CITATION.cff                  citation metadata
formalization.yaml            source, statement, automation and review metadata
lakefile.lean, lake-manifest.json, lean-toolchain   the build
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and OpenAI (GPT),
under the direction of Ahmed Bou-Rabee. Every proof is checked by the Lean kernel. The models,
tooling and review process are disclosed in [`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard.

## Authors and citation

The paper is by **Ahmed Bou-Rabee**, **William Cooperman** and **Paul Dario**. The Lean development
is by **Ahmed Bou-Rabee**. To cite the formalization, use [`CITATION.cff`](CITATION.cff). It is built
on [Lean 4](https://lean-lang.org), [Mathlib](https://github.com/leanprover-community/mathlib4) and
the library [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability).

## License

The Lean development is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE). The paper
sources in [`paper/`](paper/) are included with the permission of the paper's authors and are not
covered by the Apache license.
