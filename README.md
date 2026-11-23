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
hypotheses. Six of these twelve inputs, among them Proposition 2.3 and the concentration of the
density of the infinite cluster, are also proved in Lean, the Green-column input is proved for
`d ≥ 3` and follows from the planar order-zero estimate, and Theorem 6.5 is proved with no
literature hypothesis (see
[Assumed literature inputs](#assumed-literature-inputs)). The remaining five are quoted from the
literature: four of them (Proposition 2.3,
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
| Theorem 2.4 | `theorem:large scale-regularity` | quoted: `LatticeProb.External.ArmstrongDarioOrderZero`, `Rigidity.External.ArmstrongDarioOrderOneOrigin` | Large-scale regularity of harmonic functions on `𝒞_∞` above a minimal scale. |
| Theorem 2.5 | `theorem:first-order-corrector` | quoted: `LatticeProb.External.SupercriticalBondCorrectorInput`, `Rigidity.External.CorrectorQuantitativeInput` | Harmonic functions of linear growth are corrected planes `a + p·x + χ_p`; bounds on the corrector. |
| Proposition 2.6 | `prop:homogenizationellipticgreen` | `Rigidity.Assembly.Main.greenGradientHomogenization` | `∇ₓG(x, y)` is close to `Σᵢ ∇ℓ_{eᵢ}(x) ∂ᵢḠ(x − y)` above a minimal scale. |
| Proposition 2.8 | `prop:green-mixed-derivative` | `Rigidity.mixed_green` | Decay of the mixed derivative `∇ₓ∇_y G` above a minimal scale. |
| Lemma 2.13 | (none) | quoted, not used | A simply connected bounded planar domain whose boundary points are simple is bounded by a Jordan curve. |
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
   [Assumed literature inputs](#assumed-literature-inputs), with the six of them that are proved.
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
8. **Not formalized.** Lemma 2.13, which no proof uses; Theorems 2.4 and 2.5, which enter as
   literature inputs; the remarks, problems and conjectures; the figures. The other two quoted
   results, Proposition 2.3 and Lemma 2.14, enter as literature inputs that are proved.

## Assumed literature inputs

The table records the hypotheses of the original theorem statements. Six of these propositions
are now proved: [`Rigidity.Percolation.supercritical_bond_uniqueness`](Rigidity/Proofs/Percolation/BondUniqueness.lean),
[`Rigidity.Smoothing.micciancio_regev_smoothing`](Rigidity/Proofs/Smoothing/MicciancioRegev.lean),
[`Rigidity.Percolation.kesten_rectangle_crossing`](Rigidity/Proofs/Percolation/KestenCrossing.lean),
[`Rigidity.Topology.jordan_curve_theorem_sphere`](Rigidity/Proofs/Topology/JordanCurveSphere.lean),
[`Rigidity.Percolation.wellConnected_input`](Rigidity/Proofs/Percolation/WellConnected.lean)
(Proposition 2.3; see the note below the table), and
[`Rigidity.Proofs.S2.cluster_density_concentration`](Rigidity/Proofs/S2/ClusterDensityConcentration.lean)
(`ClusterDensityConcentrationInput`, the density concentration of Dario and Gu; see
[Density concentration in every dimension](#density-concentration-in-every-dimension)).
[`Rigidity.Assembly.WithProvedInputs`](Rigidity/Proofs/Assembly/ProvedInputs.lean) gives versions of
Theorems 1.1 and 1.2 without the uniqueness hypothesis, Theorem 1.3 without the uniqueness,
crossing, or sphere Jordan hypotheses, and Theorem 6.5 without the uniqueness or smoothing
hypotheses; `Rigidity.Percolation.wellConnected_input` supplies the hypothesis `WellConnectedInput`
of the versions of Theorems 1.1, 1.3 and 6.5, and
[`Rigidity.Assembly.Unconditional.slow_mixing`](Rigidity/Proofs/Assembly/Unconditional.lean) is
Theorem 6.5 with no literature hypothesis.
[`Rigidity.Assembly.WithProvedDensity`](Rigidity/Proofs/Assembly/ProvedDensity.lean) gives
Proposition 2.6 without the density-concentration hypothesis, and Theorem 1.3 without the
uniqueness, crossing, sphere Jordan, well-connectedness or density-concentration hypotheses. The
other inputs listed below remain hypotheses.

For Theorem 1.3, [`Rigidity.Assembly.WithPlanarInputs.fast_decay`](Rigidity/Proofs/Assembly/PlanarInputs.lean)
assumes only dimension-two forms of the qualitative and quantitative corrector estimates,
order-zero and order-one regularity, and the Green-column existence and quantitative estimates.
These six planar forms are stated in
[`Rigidity/External/PlanarInputs.lean`](Rigidity/External/PlanarInputs.lean) and are not proved.
The planar well-connectedness and cluster-density concentration estimates are supplied by
[`wellConnected_input_two`](Rigidity/Proofs/Percolation/PlanarWellConnected.lean) and
[`planar_cluster_density_concentration`](Rigidity/Proofs/S2/PlanarDensityConcentration.lean).
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
derives it in every dimension from the planar order-zero estimate `ArmstrongDarioOrderZeroTwo`; see
[Green columns for d ≥ 3](#green-columns-for-d--3).

In dimension two the planar inputs are reduced further. `ArmstrongDarioOrderZeroTwo` follows from the harmonic
approximation `PlanarHarmonicApproximationTwo` of AD Lemma 7.1, and `SupercriticalBondCorrectorInputTwo` follows from
`ArmstrongDarioOrderZeroTwo` with the existence of corrected planes and the bound `dim 𝒜₁ ≤ 3` (see
[Order-zero regularity and the planar corrector input from Lemma 7.1](#order-zero-regularity-and-the-planar-corrector-input-from-lemma-71)). The planar Green-column input follows from `SupercriticalBondCorrectorInputTwo`, the quantitative
corrector estimate from it with Theorem 1 of Dario, and the quantitative Green estimate with Theorem 1 of Dario and Gu
(see [The corrector estimate, the Green column and the Green function estimate in dimension two](#the-corrector-estimate-the-green-column-and-the-green-function-estimate-in-dimension-two)).

The input `ArmstrongDarioOrderOneOrigin` is proved from the mesoscopic estimate (7.18) of AD at `k = 2`
and the corrector inputs
([`armstrongDarioOrderOneOrigin_of_mesoscopicDegreeTwo`](Rigidity/Proofs/Regularity/OrderOneOrigin.lean)); see
[Regularity of order one at the origin from the mesoscopic estimate](#regularity-of-order-one-at-the-origin-from-the-mesoscopic-estimate).
In dimension two, (7.18) at `k = 2` is proved from the estimates on squares of the proof of AD Lemma 7.1, and
`ArmstrongDarioOrderOneOriginTwo` from them with Theorem 1 of Dario, the existence of corrected planes and the bound
`dim 𝒜₁ ≤ 3`; see
[Lemma 7.3 at k = 2 and regularity of order one at the origin in dimension two](#lemma-73-at-k--2-and-regularity-of-order-one-at-the-origin-in-dimension-two).

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
| [`Rigidity.Percolation.uniformCubeSlabConnectivity_of_criticalProbability_lt`](Rigidity/Percolation/Blocks/SlabConnectivity.lean) | If `3 ≤ d` and `criticalProbability d < p`, then `UniformCubeSlabConnectivity d p`. |

The proposition `UniformCubeSlabConnectivity d p`, defined in
[`Rigidity/Percolation/SlabTriadicPartition.lean`](Rigidity/Percolation/SlabTriadicPartition.lean),
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
[`Rigidity/Percolation/Bootstrap/`](Rigidity/Percolation/Bootstrap/) and
[`Rigidity/Percolation/Blocks/`](Rigidity/Percolation/Blocks/).

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
| [`Rigidity.Percolation.wellConnected_of_three_le`](Rigidity/Percolation/Pisztora/WellConnected.lean) | If `3 ≤ d` and `criticalProbability d < p`, there are `c, C, s > 0` such that every cube `x + Q_N` fails to be well-connected with probability at most `C exp(−c Nˢ)`: the statement of `WellConnectedInput` at `d`, here with `s = 1/(100d³)` and without the hypothesis `p < 1`. |
| [`Rigidity.Percolation.wellConnectedInput_of_planar`](Rigidity/Percolation/Pisztora/WellConnected.lean) | The case `d = 2` of `WellConnectedInput` implies `WellConnectedInput`. |
| [`Rigidity.Percolation.exists_finite_cluster_radius_le`](Rigidity/Percolation/Pisztora/FiniteClusters.lean) | If `3 ≤ d` and `criticalProbability d < p`, the open cluster of `x` is finite and reaches `ℓ^∞`-distance `l` from `x` with probability at most `C exp(−c l)`, for all `x` and `l`. |
| [`Rigidity.Percolation.exists_finite_cluster_card_le`](Rigidity/Percolation/Pisztora/FiniteClusters.lean) | Under the same hypotheses, the open cluster of `x` is finite with at least `n` vertices with probability at most `C exp(−c n^{1/d})`. |

The four theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`.

1. **Crossing estimate** (`Rigidity.Percolation.crossing_fail_le`, `Pisztora/CubeEstimates.lean`).
   From the slab bound, a cube of side `n` has, for `10dw ≤ r < 10dn`, a crossing component joined
   inside the cube to every open path that leaves each `ℓ¹`-ball of radius `r/10`, except with
   probability at most `(d + 2)(n + 1)^{2d+1} exp(−c(⌊r/(10dw)⌋ − 1))`. The proof explores the
   slabs of the cube one at a time (`Rigidity/Percolation/SlabRadiusCrossing.lean` and the modules
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
| [`Rigidity.Proofs.S2.planar_cluster_density_concentration`](Rigidity/Proofs/S2/PlanarDensityConcentration.lean) | `ClusterDensityConcentrationInputTwo`, the statement of `ClusterDensityConcentrationInput` at `d = 2`: the density of the infinite cluster in a triadic square of side `3ᵐ` differs from `θ(𝔭)` by `O_{2/15}(C 3^{−m})`. |
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
   `Rigidity/Proofs/Percolation/PlanarFiniteCluster.lean`). The Efron–Stein inequality for the
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
| [`Rigidity.Proofs.S2.cluster_density_concentration`](Rigidity/Proofs/S2/ClusterDensityConcentration.lean) | `ClusterDensityConcentrationInput`: for `d ≥ 2` and `𝔭_c(d) < p < 1`, the density of the infinite cluster in a triadic cube of side `3ᵐ` differs from `θ(𝔭)` by `O_{2(d−1)/(3d²+2d−1)}(C 3^{−dm/2})`; from `planar_cluster_density_concentration` (`d = 2`) and `clusterDensityConcentrationAt_of_three_le` (`d ≥ 3`, without the hypothesis `p < 1`). |
| [`Rigidity.Assembly.WithProvedDensity.green_gradient_homogenization`](Rigidity/Proofs/Assembly/ProvedDensity.lean) | Proposition 2.6 for every `d ≥ 2`, with the hypotheses `SupercriticalBondCorrectorInput`, `CorrectorQuantitativeInput`, `ArmstrongDarioOrderOneOrigin` and `SupercriticalBondGreenQuantitative`. |
| [`Rigidity.Assembly.WithProvedDensity.fast_decay`](Rigidity/Proofs/Assembly/ProvedDensity.lean) | Theorem 1.3, with the hypotheses `SupercriticalBondCorrectorInput`, `CorrectorQuantitativeInput`, `ArmstrongDarioOrderZero`, `ArmstrongDarioOrderOneOrigin`, `SupercriticalBondGreenColumnExistence` and `SupercriticalBondGreenQuantitative`. |

The three theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules
are in [`Rigidity/Proofs/S2/`](Rigidity/Proofs/S2/), from `DensityResamplingEnergy.lean` to
`ClusterDensityConcentration.lean`, and
[`Rigidity/Proofs/Percolation/BondShellExponential.lean`](Rigidity/Proofs/Percolation/BondShellExponential.lean).

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
`SupercriticalBondGreenColumnExistence` follows from the planar order-zero estimate alone. The same
route bounds the heat kernel of the cluster for `d ≥ 2` and the decay of the Green columns for
`d ≥ 3`, with a polynomial loss.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Green.latticeIsoperimetry`](Rigidity/Proofs/Green/LatticeIsoperimetry.lean) | for `d ≥ 2`, every finite `F ⊆ ℤᵈ` has at least `\|F\|^{(d−1)/d}` boundary edges. |
| [`Rigidity.Green.greenColumnExistence_of_three_le`](Rigidity/Proofs/Green/SupercriticalGreenColumn.lean) | for `d ≥ 3`, `𝔭_c(d) < p < 1` and each vertex `y`, almost surely, if `y` is in the infinite cluster there is exactly one Green column with pole `y`. |
| [`Rigidity.Green.supercriticalBondGreenColumnExistence_of_two`](Rigidity/Proofs/Green/SupercriticalGreenColumn.lean) | `SupercriticalBondGreenColumnExistence` from its planar case `SupercriticalBondGreenColumnExistenceTwo`. |
| [`Rigidity.Green.supercriticalBondGreenColumnExistence_of_orderZeroTwo`](Rigidity/Proofs/Green/SupercriticalGreenColumn.lean) | `SupercriticalBondGreenColumnExistence` from `ArmstrongDarioOrderZeroTwo`. |
| [`Rigidity.Green.heat_le_of_two_le`](Rigidity/Proofs/Green/SupercriticalGreenBounds.lean) | for `d ≥ 2`, `𝔭_c(d) < p < 1` and each vertex `y`, almost surely, if `y` is in the infinite cluster, then for `0 ≤ t ≤ 1` there are `K` and `N` with `p_n(x, y) ≤ K n^{−(d/2 − 1/100)(1 − t)} exp(−t\|x − y\|²/(2n))` for all `n ≥ N` and all vertices `x` of the cluster. |
| [`Rigidity.Green.greenColumn_le_rpow_of_three_le`](Rigidity/Proofs/Green/SupercriticalGreenBounds.lean) | for `d ≥ 3`, almost surely, for every `δ > 0` the Green column `g` with pole `y` satisfies `0 ≤ g(x) ≤ K \|x − y\|^{2 − d + 1/50 + δ}` for `\|x − y\| ≥ R`. |
| [`Rigidity.Green.greenColumn_le_one_add_rpow_of_three_le`](Rigidity/Proofs/Green/SupercriticalGreenBounds.lean) | for `d ≥ 3`, almost surely, for every `δ > 0`, `0 ≤ g(x) ≤ K (1 + \|x − y\|)^{2 − d + 1/50 + δ}` at every vertex `x`. |

The seven theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules
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
| [`Rigidity.Proofs.Multiscale.multiscalePoincare_holds`](Rigidity/Proofs/Multiscale/Poincare.lean) | AD Proposition A.2 (`MultiscalePoincare d`, [`Defs.lean`](Rigidity/Proofs/Multiscale/Defs.lean)): for every triadic cube `□_m` of `ℤᵈ`, every `n` with `m/2 ≤ n ≤ m` and every `u : ℤᵈ ∩ □_m → ℝ`, `‖u − (u)_{□_m}‖_{L̲²(□_m)} ≤ C 3^n ‖∇u‖_{L̲²(□_m)} + C Σ_{k=n}^{m−1} 3^k (the mean over the subcubes of size 3^k of the squared average of ∇u)^{1/2}` |
| [`Rigidity.Proofs.Multiscale.exists_multiscalePoincare_affine`](Rigidity/Proofs/Multiscale/Affine.lean) | the same inequality for `u − ℓ_ξ`, with `ℓ_ξ(x) = ξ · x`, in the form used for Lemma 5.8 of AD |

The two theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules are
in [`Rigidity/Proofs/Multiscale/`](Rigidity/Proofs/Multiscale/).

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
| [`Rigidity.Percolation.partition_estimates`](Rigidity/Proofs/Partition/AlmostSure.lean) | AD Proposition 2.1 for the good cubes: almost surely every vertex lies in exactly one maximal stopping cube `□_𝒫(x)` of the partition `𝒫`, `E[exp(size(□_𝒫(x))/θ)] ≤ 2` for every vertex `x`, and the partition is approximately local. |
| [`Rigidity.Percolation.partition_estimates_general`](Rigidity/Proofs/Partition/GeneralPartition.lean) | AD Proposition 2.1 for any random collection of good cubes whose failure probabilities are at most `C exp(−c 3^{ns})`, with `E[exp((size/θ)^s)] ≤ 2`. |
| [`Rigidity.Percolation.exists_minimalScale`](Rigidity/Proofs/Partition/MinimalScaleCombined.lean) | AD Proposition 2.4 for `𝒫`: for every `t ∈ ℕ` there are `C` and a measurable random scale `M`, finite almost surely, with a stretched exponential moment such that, almost surely, `M < 3ᵐ` implies `Λ_t(□_m) ≤ C` and that every vertex of `□_m` lies in a partition cube of size at most `3^{dm/(d+t)}`. |
| [`Rigidity.Percolation.exists_minimalScale_general`](Rigidity/Proofs/Partition/GeneralPartition.lean) | AD Proposition 2.4 for a random collection of good cubes satisfying AD (2.1) and (2.2) with `0 < s ≤ 1`. |
| [`Rigidity.Percolation.exists_measure_not_mem_goodCubes_le`](Rigidity/Proofs/Partition/AlmostSure.lean) | AD Lemma 2.7: a triadic cube of scale `n` fails to be good with probability at most `C exp(−c 3ⁿ)`. |
| [`Rigidity.Percolation.TriadicCube.reachable_of_mem_goodCubes`](Rigidity/Proofs/Partition/Adjacent.lean) | AD Lemma 2.8: the crossing clusters of two good cubes containing lattice neighbours, whose scales are equal or differ by one, are joined by an open path inside the union of the two cubes. |
| [`Rigidity.Percolation.reachable_partitionAnchor_of_walk`](Rigidity/Proofs/Partition/Paths.lean) | AD Corollary 2.10: along every lattice walk from `x` to `y`, the anchors of `□_𝒫(x)` and `□_𝒫(y)` are joined by an open path inside the union of the partition cubes of the vertices of the walk. |
| [`Rigidity.Percolation.partition_sum_abs_sub_coarseAnchor_rpow_le`](Rigidity/Proofs/Cluster/PartitionCoarseData.lean) | AD Lemma 3.2 on a triadic cube `U` resolved by the partition, for `1 ≤ s < ∞`: `Σ_{x ∈ C_*(U)} \|w(x) − [w]_𝒫(x)\|^s ≤ C^s Σ_{z ∈ C_*(U)} 3^{sdρ(z)} \|∇w 1_{𝐚≠0}\|^s(z)`, with `ρ(z) ≥ scale(□_𝒫(z))` the reach scale. |
| [`Rigidity.Percolation.partition_sum_gradNormIn_coarseAnchor_rpow_le`](Rigidity/Proofs/Cluster/PartitionCoarseData.lean) | AD Lemma 3.3 on a resolved cube `U`, for `1 ≤ s < ∞`: `Σ_{x ∈ U} \|∇[w]_𝒫\|^s(x) ≤ C^s Σ_{z ∈ C_*(U)} size(□_𝒫(z))^{sd−1} \|∇w 1_{𝐚≠0}\|^s(z)`. |
| [`Rigidity.Percolation.exists_partition_sum_rpow_le_of_latticeSobolevOn`](Rigidity/Proofs/Cluster/PartitionSobolev.lean) | AD Proposition 3.4 on a resolved cube `U`, for `1 ≤ t ≤ s` and `w` of mean zero on `C_*(U)`, given the Sobolev inequality `Σ_U \|f − (f)_U\|^s ≤ S (Σ_U \|∇f\|^t)^{s/t}` of the lattice cube: `Σ_{C_*(U)} \|w\|^s ≤ K (Σ_{z ∈ C_*(U)} 3^{tdρ(z)} \|∇w 1_{𝐚≠0}\|^t(z))^{s/t}`. |
| [`Rigidity.Percolation.exists_partition_sum_sq_le_two`](Rigidity/Proofs/Cluster/PartitionSobolevTwo.lean) | AD Proposition 3.4 for `d = 2`, `s = 2` and `t = 1`, the Sobolev inequality of the planar lattice square being proved. |
| [`Rigidity.Percolation.IntegerCube.exists_latticeSobolevOn`](Rigidity/Proofs/Cluster/SobolevCube.lean) | the Sobolev–Poincaré inequality of the integer cubes of `ℤᵈ`, `d ≥ 2`: for `s ≥ d/(d − 1)` and `t = sd/(s + d)` there is `S` with `Σ_B \|f − (f)_B\|^s ≤ S (Σ_B \|∇f\|^t)^{s/t}` on every cube `B`. |
| [`Rigidity.Percolation.exists_sum_rpow_le_of_eq_zero_on_boundary`](Rigidity/Proofs/Cluster/SobolevZero.lean) | the Sobolev inequality with zero boundary values: `Σ_D \|f\|^s ≤ S (Σ_D \|∇f\|^t)^{s/t}` for every finite `D ⊆ ℤᵈ` and every `f` vanishing at the points of `D` with a lattice neighbour outside `D`. |
| [`Rigidity.Percolation.exists_partition_sum_rpow_le_of_sum_eq_zero`](Rigidity/Proofs/Cluster/SobolevPartition.lean) | AD Proposition 3.4 on a resolved cube `U`, `d ≥ 2`, `s ≥ d/(d − 1)`, for `Σ_{C_*(U)} w = 0`: `Σ_{C_*(U)} \|w\|^s ≤ K (Σ_{z ∈ C_*(U)} 3^{tdρ(z)} \|∇w 1_{𝐚≠0}\|^t(z))^{s/t}`. |
| [`Rigidity.Percolation.exists_partition_sum_rpow_le_of_sum_coarsen_eq_zero`](Rigidity/Proofs/Cluster/SobolevPartition.lean) | the same for `Σ_U [w]_𝒫 = 0`. |
| [`Rigidity.Percolation.exists_partition_sum_rpow_le_of_coarsen_eq_zero`](Rigidity/Proofs/Cluster/SobolevCoarseZero.lean) | the same for `[w]_𝒫 = 0` at the points of `U` with a lattice neighbour outside `U`. |
| [`Rigidity.Percolation.exists_clusterSobolevTwo`](Rigidity/Proofs/Cluster/SobolevReverseHolder.lean) | AD Proposition 3.4 with `s = 2` in the form of the Sobolev hypothesis `ClusterSobolevTwo` of the reverse Hölder inequality, on `C_*(U)` for every resolved cube `U`, `d ≥ 2`. |
| [`Rigidity.Proofs.Cluster.caccioppoli_cluster`](Rigidity/Proofs/Cluster/Caccioppoli.lean) | AD Lemma 3.5: if `V ⊆ U`, every point of `U` with an open edge leaving `U` is at `ℓ∞` distance at least `r > 0` from `V`, and `u` is harmonic at the points of `U` all of whose open edges stay in `U`, then `Σ_V \|∇u 1_{𝐚≠0}\|² ≤ (8d/r²) Σ_{U ∖ int V} u²`. |
| [`Rigidity.Proofs.Cluster.reverse_holder_partition_cube`](Rigidity/Proofs/Cluster/ReverseHolderPartition.lean) | AD Lemma 3.6, deterministic part: on the crossing cluster of a resolved triadic cube `□` of scale `m + 1`, given the Sobolev inequality of the lattice cube with exponents `2` and `2_* = 2d/(d+2)` and `Σ_{C_*(□)} 3^{2dsρ} ≤ C_G \|□\|`, every `u` harmonic on `C_*(□)` has `3^{−md} Σ_{C_*(□) ∩ □'} \|∇u\|² ≤ C (\|□\|⁻¹ Σ_{C_*(□)} \|∇u\|^{t2_*})^{2/(t2_*)}`, `□'` the central subcube and `1/s + 1/t = 1`. |
| [`Rigidity.Proofs.Cluster.gehring_triadic`](Rigidity/Proofs/Cluster/Gehring.lean) | Gehring's lemma on the triadic cubes of `ℤᵈ`: for `0 < θ < 1`, a reverse Hölder inequality `avg_Q g ≤ A (avg_{Q^j} g^θ)^{1/θ}` on every subcube `Q` of `□` whose enlargement `Q^j` lies in `3□` gives `ε > 0` with `avg_□ g^{1+ε} ≤ C (avg_{3□} g)^{1+ε}`. |
| [`Rigidity.Proofs.Cluster.meyers_cluster`](Rigidity/Proofs/Cluster/MeyersCluster.lean) | AD Proposition 3.8, deterministic part: for `u` harmonic on `U₀` and a partition of `3□` into triadic cells of comparable neighbouring sizes, if the triadic cubes `□'` above the cells carry sets `U' ⊆ U₀ ∩ 3□'` with the Sobolev inequality and a moment bound, and `Σ_{x ∈ □} size(x)^t ≤ K\|□\|`, then `E = \|∇u 1_{𝐚≠0}\|²` has `avg_□ E^{1+ε/2} ≤ C (avg_{3□} E)^{1+ε/2}`. |

The twenty-one theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules
are in [`Rigidity/Proofs/Partition/`](Rigidity/Proofs/Partition/) and
[`Rigidity/Proofs/Cluster/`](Rigidity/Proofs/Cluster/).

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
4. **Coarsening** (`Rigidity/Proofs/Cluster/`: `CoarseData.lean`, `CoarseInequalities.lean`,
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
  partition `ℛ` of AD, Definition 3.7, are not proved here.

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
| [`Rigidity.Percolation.exists_measure_planarCappedDiscrepancy_le`](Rigidity/Proofs/Percolation/PlanarNuStationarity.lean) | AD Proposition 4.9 for `d = 2`: the planar partition differs somewhere in a triadic square `V` of scale `n` from the partition capped at scale `n` with probability at most `C exp(−c 3ⁿ)`. |
| [`Rigidity.Percolation.exists_planarNuLoc_localization`](Rigidity/Proofs/Percolation/PlanarNuLocal.lean) | AD Proposition 4.10 for `ν`, `d = 2`: a version of `ν(V, ξ)` measurable with respect to the edges near `V` differs from it on an event of probability at most `C exp(−c 3ⁿ)`, and the expectations differ by at most `C\|ξ\|₁² exp(−c 3ⁿ)`. |
| [`Rigidity.Percolation.exists_planarMuLoc_localization`](Rigidity/Proofs/Percolation/PlanarMuLocal.lean) | AD Proposition 4.10 for `μ`, `d = 2`, with the error `C\|q\|₁² exp(−c 3ⁿ)` in expectation. |
| [`Rigidity.Percolation.map_planarNuStat_shift`](Rigidity/Proofs/Percolation/PlanarLocalStationary.lean) | AD (4.40) for `d = 2`: the law of the local version of `ν(z + □_n, ξ)` does not depend on `z ∈ 3ⁿℤ²`. |
| [`Rigidity.Percolation.map_planarMuStat_shift`](Rigidity/Proofs/Percolation/PlanarLocalStationary.lean) | the same for `μ`. |
| [`Rigidity.Percolation.exists_tendsto_planarNuMean`](Rigidity/Proofs/Percolation/PlanarNuConvergence.lean) | `E[ν(□_m, ξ)]` converges as `m → ∞`, to a limit between `c\|ξ\|²` and `(9/4)\|ξ\|₁²`. |
| [`Rigidity.Percolation.exists_tendsto_planarMuMean`](Rigidity/Proofs/Percolation/PlanarMuConvergence.lean) | `E[−μ(□_m, q)]` converges as `m → ∞`, to a limit between `0` and `C\|q\|₁²`. |
| [`Rigidity.Percolation.planarNuLimit_eq_planarAhom`](Rigidity/Proofs/Percolation/PlanarNuQuadratic.lean) | AD Definition 5.1 for `d = 2`: the limit is the quadratic form `(1/2) ξ · ā ξ` of a matrix `ā`. |
| [`Rigidity.Percolation.exists_planarAhom_bounds`](Rigidity/Proofs/Percolation/PlanarNuQuadratic.lean) | AD (5.1) for `d = 2`: `c\|ξ\|² ≤ (1/2) ξ · ā ξ ≤ (9/4)\|ξ\|₁²` with `c > 0`. |
| [`Rigidity.Percolation.exists_planarMuLimit_two_sided`](Rigidity/Proofs/Percolation/PlanarMuLimitBounds.lean) | `\|q\|²/18 ≤ lim_m E[−μ(□_m, q)] ≤ C\|q\|₁²`. |
| [`Rigidity.Percolation.sum_mul_le_planarMuLimit_add_planarNuLimit`](Rigidity/Proofs/Percolation/PlanarDuality.lean) | for all slopes `q` and `ξ`, `q · ξ ≤ lim E[−μ(□_m, q)] + lim E[ν(□_m, ξ)]`. |

The eleven theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules
are in [`Rigidity/Proofs/Percolation/`](Rigidity/Proofs/Percolation/), from `PlanarLocality.lean`
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
| [`Rigidity.Percolation.sum_clusterForm_sub_add_sum_planarMu_subcubes_le`](Rigidity/Proofs/Percolation/PlanarSecondVariation.lean) | AD Lemma 4.2 and (5.11) for `μ`, `d = 2`: for the minimizer on a resolved cube and the minimizers on its subcubes of scale `n`, the energy of the differences plus the sum of `μ` over the subcubes is at most `μ` of the large cube. |
| [`Rigidity.Percolation.sum_clusterForm_sub_add_planarNu_le_sum_subcubes`](Rigidity/Proofs/Percolation/PlanarSecondVariation.lean) | the same for `ν`, for any solution of the first variation equation on the large cube. |
| [`Rigidity.Percolation.exists_lintegral_planarMuDefect_le`](Rigidity/Proofs/Percolation/PlanarMuEnergyDefect.lean) | AD Lemma 5.4, display (5.10), for `μ`: the expected energy of the differences between the restricted minimizer and the minimizers on the subcubes of scale `n` is at most the volume times the decrease of `E[−μ]` between the two scales, up to `C\|q\|₁² ε_n`. |
| [`Rigidity.Percolation.exists_lintegral_planarNuDefect_le`](Rigidity/Proofs/Percolation/PlanarNuEnergyDefect.lean) | the same for `ν`, with maximizers. |
| [`Rigidity.Percolation.exists_planarMuDefect_le_planarMuTau`](Rigidity/Proofs/Percolation/PlanarMuIncrements.lean) | AD (5.9) and (5.10) for `μ`: for `n ≤ m`, the expected energy of the differences, divided by the volume, is at most `2\|q\|² ∑_{n ≤ k < m} τ_k^μ` plus `C\|q\|₁² (∑_{n ≤ k < m} ε_k + ε_n)`. |
| [`Rigidity.Percolation.exists_planarNuDefect_le_planarNuTau`](Rigidity/Proofs/Percolation/PlanarNuDefectTau.lean) | the same for `ν` at `ā⁻¹ q`, with `τ^ν`. |
| [`Rigidity.Percolation.summable_planarTau`](Rigidity/Proofs/Percolation/PlanarTauSummable.lean) | `τ_k` is summable. |
| [`Rigidity.Percolation.exists_planarMuDefect_le_tendsto`](Rigidity/Proofs/Percolation/PlanarTauSummable.lean), [`exists_planarNuDefect_le_tendsto`](Rigidity/Proofs/Percolation/PlanarNuDefectTau.lean) | AD Lemma 5.4, qualitative form: the expected energy of the differences divided by the volume is at most `(\|q\|² + \|q\|₁²) R_n` with `R_n → 0`, uniformly in `m ≥ n`. |
| [`Rigidity.Percolation.planarMuLimit_eq_iff_planarOmegaLimit_eq_zero`](Rigidity/Proofs/Percolation/PlanarOmegaLimit.lean), [`forall_planarOmegaLimit_eq_zero_iff`](Rigidity/Proofs/Percolation/PlanarOmegaMatrix.lean) | AD Proposition 5.2: the limit of `E[ω(□_n, q)]` exists and is nonnegative, and `lim E[−μ(□_n, q)] = (1/2) q · ā⁻¹ q` for all `q` if and only if the limit of `E[ω]` vanishes, if and only if the finite-volume matrices converge to `ā⁻¹`. |
| [`Rigidity.Percolation.integral_coarsePairing_planarMuMinimizer`](Rigidity/Proofs/Percolation/PlanarFiniteVolumeMatrix.lean) | AD (5.23), the centering in Lemma 5.7: the expected spatial average of the coarsened gradient of the minimizer of `μ(□_n, q)` against `r` is `r · ā_{□_n}⁻¹ q`. |
| [`Rigidity.Percolation.tendsto_planarAhomInvFinite`](Rigidity/Proofs/Percolation/PlanarFiniteVolumeMatrix.lean) | the matrices `ā_{□_n}⁻¹` converge entrywise to twice the matrix of the limit of `E[−μ]`. |
| [`Rigidity.Percolation.exists_planarAhomInvFinite_bounds`](Rigidity/Proofs/Percolation/PlanarFiniteVolumeBounds.lean), [`exists_abs_planarAhomInvFinite_sub_le`](Rigidity/Proofs/Percolation/PlanarFiniteVolumeClose.lean) | AD (5.22) and (5.24): the matrices are uniformly elliptic from some scale on, and two of them differ by at most `2 ∑ τ_k` plus a vanishing error. |
| [`Rigidity.Percolation.tsum_sum_grad_mul_solenoidalField`](Rigidity/Proofs/Percolation/PlanarSolenoidalPairing.lean), [`solenoidalField_eq`](Rigidity/Proofs/Percolation/PlanarSolenoidalField.lean), [`abs_solenoidalField_le`](Rigidity/Proofs/Percolation/PlanarSolenoidalField.lean) | AD Lemma 5.7, Step 1, and (5.28) with right side zero, `d = 2`: a finitely supported, exactly divergence free field, bounded by `10 \|e\|₁`, equal to `e` near `□_n`, is orthogonal to every gradient. |
| [`Rigidity.Percolation.exists_abs_planarNu_sub_planarMu_sub_le`](Rigidity/Proofs/Percolation/PlanarQuadraticResponse.lean) | first display of the proof of AD Lemma 5.9, per cube: `ν(U, p) − μ(U, q) − q · p` differs from the energy of the difference between the maximizer and the minimizer, divided by twice the volume, by at most `\|q · p\|/L` plus the boundary error. |
| [`Rigidity.Percolation.exists_planarOmegaD_succ_le`](Rigidity/Proofs/Percolation/PlanarOmegaStepOne.lean), [`exists_neg_le_planarOmegaD`](Rigidity/Proofs/Percolation/PlanarOmegaDBounds.lean) | AD Lemma 5.10, Step 1 and the lower bound of `D_n`: from some scale on, `D_{n+1} ≤ D_n − c τ_n + C ε_n` and `D_n ≥ −C 3^{−n/2}`. |
| [`Rigidity.Percolation.exists_le_mul_pow_of_omega_iteration`](Rigidity/Proofs/Percolation/PlanarOmegaIteration.lean), [`exists_le_mul_pow_of_omega_iteration_of_ge`](Rigidity/Proofs/Percolation/PlanarOmegaIteration.lean) | AD Lemma 5.10, Steps 1 to 3, for real sequences, also when the hypotheses hold only from a starting scale on. |
| [`Rigidity.Percolation.exists_planarOmegaD_le_pow_of_decay`](Rigidity/Proofs/Percolation/PlanarOmegaDecayIteration.lean), [`exists_planarTau_le_pow_of_decay`](Rigidity/Proofs/Percolation/PlanarOmegaDecayIteration.lean), [`exists_abs_planarAhomInvLimit_sub_le_of_decay`](Rigidity/Proofs/Percolation/PlanarFiniteVolumeRate.lean) | AD Lemma 5.10 with the bound of Lemma 5.9 as an explicit hypothesis `h59`: `D_n`, `τ_n` and the distance from `ā_{□_n}⁻¹` to its limit decay geometrically. |
| [`Rigidity.Percolation.planarMuLimit_eq_of_decay`](Rigidity/Proofs/Percolation/PlanarIdentification.lean) | AD Proposition 5.2, qualitative part, with the bound of Lemma 5.9, `D_n ≤ C (σⁿ + ∑_{l ≤ n} ρ^{n−l} τ_l)` from some scale on with `σ, ρ < 1`, as an explicit hypothesis: `lim E[−μ(□_n, q)] = (1/2) q · ā⁻¹ q` for every `q`. |

The theorems of the table and their supporting results (the limit matrix is invertible, the matrices
`ā_{□_n}` converge to its inverse, `D_n` converges, the limit matrix is below `ā⁻¹`) depend on
exactly `propext`, `Classical.choice` and `Quot.sound`; thirty-five of them have axiom reports in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean). The modules are in
[`Rigidity/Proofs/Percolation/`](Rigidity/Proofs/Percolation/), from `PlanarSecondVariation.lean`
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
| [`Rigidity.Proofs.Cluster.reverse_holder_partition_cube_of_moment`](Rigidity/Proofs/Cluster/ReverseHolderMoment.lean), [`reverse_holder_partition_of_moment`](Rigidity/Proofs/Cluster/ReverseHolderMoment.lean) | AD Lemma 3.6, deterministic part, every `d ≥ 2`, with the Sobolev hypothesis proved: for a resolved cube `□_{m+1}` with `∑_{z ∈ C_*(□_{m+1})} (3^{ρ(z)})^{2ds} ≤ C_G \|□_{m+1}\|` and `u` harmonic on `C_*(□_{m+1})`, `3^{−md} ∑_{C_*(□_{m+1}) ∩ □_m} \|∇u 1_{𝐚≠0}\|² ≤ C (\|□_{m+1}\|⁻¹ ∑_{C_*(□_{m+1})} \|∇u 1_{𝐚≠0}\|^{t 2_*})^{2/(t 2_*)}`, as in `reverse_holder_partition_cube`. |
| [`Rigidity.Proofs.Cluster.planar_reverse_holder_cube_of_moment`](Rigidity/Proofs/Cluster/ReverseHolderPlanar.lean) | the same for the planar partition, with the weight `((3^ρ)² + 3^{ρ'})^{1/4}` and the moment bound `∑ ((3^ρ)² + 3^{ρ'})^s ≤ C_G 3^{2(m+1)}`. |
| [`Rigidity.Percolation.exists_planarBox_sum_sq_le`](Rigidity/Proofs/Cluster/PlanarBoxSobolev.lean), [`exists_clusterSobolevTwo_box`](Rigidity/Proofs/Cluster/PartitionBoxSobolev.lean) | AD Proposition 3.4 with `s = 2`, with Lemmas 3.2 and 3.3 proved on the cluster of an integer square (`d = 2`) or integer cube (every `d ≥ 2`) `B` resolved by the partition, for `w` of mean zero on the cluster: `∑_{C(B)} w² ≤ K (∑_{z ∈ C(B)} w_ρ(z) \|∇w 1_{𝐚≠0}\|(z))²` with the weight `w_ρ` built from the reach scales of `B`, which are bounded by the reach of the partition (`three_pow_reachScale_le_planarReach_box`, `three_pow_reachScale_le_partitionReach_box`). |
| [`Rigidity.Proofs.Cluster.reverse_holder_clusterEnergy_local`](Rigidity/Proofs/Cluster/MeyersPlanarBox.lean), [`meyers_cluster_of_local`](Rigidity/Proofs/Cluster/MeyersPlanarBox.lean) | the reverse Hölder inequality for functions harmonic near the cube, and `meyers_cluster` with a weight chosen for each cube `□'`. |
| [`Rigidity.Proofs.Cluster.planar_meyers`](Rigidity/Proofs/Cluster/MeyersPlanarBox.lean), [`planar_meyers_clusterHarmonic`](Rigidity/Proofs/Cluster/PlanarMeyersHarmonic.lean) | AD Proposition 3.8, deterministic part, `d = 2`, with the Sobolev inequality on the clusters of the triples proved, for `u` harmonic on the cluster of a triadic cube `V ⊇ 3□` (for the extension by zero of a harmonic function of a smaller cube in the second form). Hypotheses: the planar partition event; a Gehring partition of `3□` into cells of comparable neighbouring sizes with `∑_{x ∈ □} (3^{s(x)})^t ≤ K \|□\|`; for every triadic `□' = cube k y` above a cell with `3□' ⊆ 3□`, the partition cubes of the vertices of `3□'` have scale at most `k` and `∑_{z ∈ 3□'} planarReach(z)^8 ≤ C_G \|3□'\|`. |
| [`Rigidity.Proofs.Cluster.partition_meyers`](Rigidity/Proofs/Cluster/MeyersPartitionBox.lean) | the same in every dimension `d ≥ 2` on `C_*(V) ∩ 3□`, `V` resolved, with `∑_{z ∈ 3□'} partitionReach(z)^{2d(d+2)} ≤ C_G \|3□'\|` and the partition scales below `k`. |
| [`Rigidity.Proofs.Cluster.sum_mul_le_of_meyers_cells`](Rigidity/Proofs/Cluster/PlanarCoarseMeyers.lean), [`planarBox_coarse_energy_le_of_meyers`](Rigidity/Proofs/Cluster/PlanarCoarseMeyers.lean) | AD display (5.16), deterministic, `d = 2`: with the Meyers estimate on cells `□'` covering the cluster of a resolved square `B ⊆ V`, triples of overlap at most `N`, and cell averages of a weight `W ≥ 3^{ρ'}` with `(avg_{□'} W^{3q})^{1/q} ≤ A`, `∑_B \|∇[w]_𝒫\|² ≤ C² A C_M^{1/p} N ∑_V \|∇w 1_{𝐚≠0}\|²`. |
| [`Rigidity.Percolation.edgePairing_sq_le_of_subset`](Rigidity/Proofs/Cluster/PlanarEdgePairing.lean), [`coarsePairing_eq_edgePairing`](Rigidity/Proofs/Cluster/PlanarEdgePairing.lean) | AD Lemma 5.5, Step 2 (removal of the boundary layer): `⟨∇f, g⟩_V² ≤ 8 G² \|B\| E_B + 16 G² \|V ∖ B\| E_V` for `\|g\| ≤ G`. |
| [`Rigidity.Proofs.Cluster.edgePairing_clusterExtend_sq_le_clusterForm`](Rigidity/Proofs/Cluster/PlanarCoarseEnergy.lean), [`edgePairing_innerCells_sq_le`](Rigidity/Proofs/Cluster/PlanarInnerCells.lean) | AD Lemma 5.5, Steps 2 and 3 on one subcube, with the Hölder inequality inside the cells of scale `j` of the inner square: `⟨∇[w]_𝒫, g⟩_V² ≤ Λ B(w, w)`. Hypotheses: the partition scales on `V` are at most `j`, the Meyers estimate for `w` on the cells, the bound `A` on the cell averages of the weight, and `W ≥ 3 planarReach` on the cluster. |
| [`Rigidity.Proofs.Cluster.sum_edgePairing_sq_le_planarMuDefect`](Rigidity/Proofs/Cluster/PlanarRestrictDefect.lean) | AD Lemma 5.5, deterministic part, summed over the resolved subcubes of scale `n`: `∑_V ⟨∇[w_V]_𝒫, g⟩_V² ≤ 2 Λ D_n(U, q)`, with the hypotheses of `edgePairing_innerCells_sq_le` on each subcube. |
| [`Rigidity.Percolation.exists_measure_partitionScale_gt_le`](Rigidity/Proofs/Cluster/PlanarPartitionScaleTail.lean) | for every `m`, the probability that some vertex of a finite set `S` has a planar partition cube of scale larger than `j` is at most `C \|S\| 3^{−(j+1)(m+1)}`. |
| [`Rigidity.Proofs.Cluster.ofReal_sum_gradNormIn_coarse_planarMuMinimizer_le`](Rigidity/Proofs/Cluster/PlanarCoarseMinimizer.lean), [`exists_lintegral_coarse_minimizer_le`](Rigidity/Proofs/Cluster/PlanarCoarseEnergyMoments.lean), [`exists_lintegral_coarse_minimizer_sq_le`](Rigidity/Proofs/Cluster/PlanarCoarseEnergySecondMoment.lean) | AD (4.24), `d = 2`: for the minimizer `u_V` of `μ(V, q)` on a resolved triadic cube, `∑_V \|∇[u_V]_𝒫\|² ≤ C \|q\|₁² (3 max_V R)³ ∑_V R⁴` with `R = planarReach`, `E[∑_V \|∇[u_V]_𝒫\|²] ≤ C_a \|q\|₁² \|V\|^{1+1/a}` for `a ≥ 2`, and the second moment `≤ C \|q\|₁⁴ \|V\|^{2+2/a}` for `a ≥ 3`. |
| [`Rigidity.Percolation.edgePairing_sub_sum_subcubes_sq_le`](Rigidity/Proofs/Cluster/PlanarSubcubePairing.lean), [`Rigidity.Proofs.Cluster.exists_lintegral_edgePairing_sub_sum_subcubes_le`](Rigidity/Proofs/Cluster/PlanarHolderAway.lean) | AD Lemma 5.7, Step 2, display (5.29), `d = 2`: the pairing of a bounded field with the coarsened gradient on `U` differs from the sum over the subcubes of scale `n` by at most the number of crossing edges times the energy, and in expectation `E[(⟨∇[u_U], g⟩_U − ∑_V ⟨∇[u_U], g⟩_V)²] ≤ C G² \|q\|₁² 3^{−n} \|U\|² \|U\|^{1/a}`. |

The theorems of the table and their supporting results depend only on axioms among `propext`, `Classical.choice`
and `Quot.sound`; sixty-five of them (sixty-one theorems and four definitions) have axiom reports in
[`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean). The modules are in
[`Rigidity/Proofs/Cluster/`](Rigidity/Proofs/Cluster/), from `ReverseHolderMoment.lean` to
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
[`Rigidity/Proofs/Percolation/GeneralDim/`](Rigidity/Proofs/Percolation/GeneralDim/), with the names
`cubeMu`, `cubeNu`, `cubeForm`, `cubeHarmonic` in place of the planar `planarMu`, `clusterForm`, and
so on. On the partition event and for a resolved cube, `cl_𝒫(U) = U` and `C_*(U)` is the crossing
cluster of `U`; the space `A_*(U)` of the paper is `cubeHarmonic`, the functions on `C_*(U)` harmonic
at the vertices of `C_*(U)` in the lattice interior of `U`. AD numbering below is that of the arXiv v2
source (Definition 4.1, Lemmas 4.2 to 4.5, Corollary 4.6, Lemmas 4.7 and 4.8, Definition 5.1).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.cubeMu`](Rigidity/Proofs/Percolation/GeneralDim/CubeEnergy.lean), [`cubeNu`](Rigidity/Proofs/Percolation/GeneralDim/CubeEnergy.lean), [`exists_cubeMu_minimizer`](Rigidity/Proofs/Percolation/GeneralDim/CubeEnergy.lean), [`exists_cubeNu_maximizer`](Rigidity/Proofs/Percolation/GeneralDim/CubeEnergy.lean) | AD Definition 4.1 and Lemma 4.2: `μ(U, q) = inf_{A_*(U)} (B(u, u)/2 − ℓ_q(u))/\|U\|` and `ν(U, p) = sup_{A_*(U)} (F_p(v) − B(v, v)/2)/\|U\|` are attained, at solutions of the first variation equations `B(w, u) = ℓ_q(w)` and `B(w, v) = F_p(w)` for `w ∈ A_*(U)`; here `B` is the Dirichlet form on the open edges of `C_*(U)`, `ℓ_q` the coarse pairing over the lattice edges inside `U`, and `F_p` the flux pairing. |
| [`cubeMu_mul_latticeVolume_add_cubeForm_sub`](Rigidity/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeFluxPairing_sub_add_cubeForm_sub`](Rigidity/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeMu_mul_latticeVolume_eq`](Rigidity/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeNu_mul_latticeVolume_eq`](Rigidity/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeNu_sub_cubeMu_eq`](Rigidity/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeMu_smul_add_smul`](Rigidity/Proofs/Percolation/GeneralDim/CubeVariations.lean), [`cubeNu_smul_add_smul`](Rigidity/Proofs/Percolation/GeneralDim/CubeVariations.lean) | AD Lemma 4.2, (4.4), (4.6), (4.7) and (4.8): the second variations, the values `\|U\| μ(U, q) = −B(u, u)/2` and `\|U\| ν(U, p) = B(v, v)/2` at the optimizers, the comparison identity of `ν` and `μ`, and the quadratic dependence of `μ` and `ν` on `q` and `p`. |
| [`cubeMu_nonpos`](Rigidity/Proofs/Percolation/GeneralDim/CubeEnergyBounds.lean), [`cubeNu_nonneg`](Rigidity/Proofs/Percolation/GeneralDim/CubeEnergyBounds.lean), [`cubeNu_le`](Rigidity/Proofs/Percolation/GeneralDim/CubeEnergyBounds.lean), [`neg_cubeMu_le`](Rigidity/Proofs/Percolation/GeneralDim/CubeMuUpperBound.lean), [`exists_lintegral_neg_cubeMu_le`](Rigidity/Proofs/Percolation/GeneralDim/CubeMuMoment.lean) | `μ(U, q) ≤ 0 ≤ ν(U, p) ≤ (3^d/4) \|p\|₁²` ((4.13)); the bound of `−μ` by the partition sizes, `−μ(U, q) ≤ d C₃² \|q\|₁² \|U\|⁻¹ ∑_{z ∈ C_*(U)} size(□_𝒫(z))^{2d−2}` ((4.12)), through AD Lemma 3.3 with `s = 1`; and `E[−μ(U, q); partition event, U resolved] ≤ C \|q\|₁²` ((4.16), in expectation). |
| [`exists_cubeNu_maximizer_affine`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuDirichlet.lean), [`exists_cubeHarmonic_eq_on_boundary`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuDirichlet.lean), [`cubeNu_le_of_affine_boundary`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuDirichlet.lean), [`exists_cubeNu_eq_of_affine_boundary`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuDirichlet.lean) | AD Lemma 4.3, (4.1) and (4.9): the functions vanishing outside the lattice interior of `U` are orthogonal to `A_*(U)`, the Dirichlet problem on `C_*(U)` with any boundary values is solvable, the maximizer of `ν(U, p)` is affine of slope `p` at the boundary vertices of `C_*(U)` up to a constant, and `ν(U, p) \|U\|` is the least half energy of a function with such boundary values. |
| [`cubeCoarsePairing_eq_faces`](Rigidity/Proofs/Percolation/GeneralDim/CubeStokes.lean), [`abs_cubeCoarsePairing_sub_le`](Rigidity/Proofs/Percolation/GeneralDim/CubeNablaAffine.lean), [`cubeBoundaryError_le`](Rigidity/Proofs/Percolation/GeneralDim/CubeBoundaryErrorBound.lean), [`cubeBoundaryWeight_le`](Rigidity/Proofs/Percolation/GeneralDim/CubeBoundaryWeightBound.lean), [`exists_integral_sum_faces_le`](Rigidity/Proofs/Percolation/GeneralDim/CubeSizeMoments.lean), [`exists_integral_sum_margin_le`](Rigidity/Proofs/Percolation/GeneralDim/CubeSizeMoments.lean) | AD Lemma 4.5, (4.27), in every dimension: by the discrete Stokes formula the coarse pairing is a sum of coarsened values over the faces of `U`; for the maximizer `v` of `ν(U, p)`, `\|ℓ_q(v) − (q · p) L^{d−1}(L − 1)\| ≤ \|q\|₁ E_p(v)`, the boundary error `E_p(v)` being a weighted variation of `v` over the partition cubes at the faces, bounded by the Hölder and Young inequalities through the weight `W_∂(z) ≤ ∑_i 2 size(□_𝒫(z))^{d−1} 1{margin_i(z) < size(□_𝒫(z))}`; and the expectations of the sums of the sizes over the faces and of the margin-weighted sums are at most `C L^{d−1}`. |
| [`exists_abs_cubeNu_sub_cubeMu_sub_le`](Rigidity/Proofs/Percolation/GeneralDim/CubeMuNuComparison.lean), [`exists_cubeMu_le_cubeNu_sub`](Rigidity/Proofs/Percolation/GeneralDim/CubeMuNuComparison.lean) | AD Corollary 4.6, (4.29): `\|ν(U, p) − μ(U, q) − q · p − B(v − u, v − u)/(2\|U\|)\| ≤ \|q · p\|/L + \|q\|₁ E_p(v)/\|U\|`, with `E_p(v)` the boundary error, and `μ(U, q) ≤ ν(U, p) − q · p` up to the same errors. |
| [`exists_cubeMu_le_neg_sum_sq`](Rigidity/Proofs/Percolation/GeneralDim/CubeMuLowerBound.lean), [`le_cubeNu_add_of_resolved`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuLowerBound.lean), [`exists_le_integral_cubeNu`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuLowerBoundMean.lean) | AD Lemma 4.7, (4.30) and (4.31): `μ(U, q) ≤ −\|q\|²/(3^d d) + t \|q\|²/L + \|q\|₁ E_{tq}(v)/\|U\|` with `t = 2/(3^d d)`; `κ \|p\|² ≤ ν(U, p)` up to explicit errors for every `κ > 0`; and, in expectation, `c \|p\|² ≤ E[ν(U, p)] + C \|p\|₁² 3^{−m/2}` for every triadic cube `U` of scale `m`. |
| [`sum_cubeMu_subcubes_le`](Rigidity/Proofs/Percolation/GeneralDim/CubeSubadditive.lean), [`cubeNu_le_sum_subcubes`](Rigidity/Proofs/Percolation/GeneralDim/CubeSubadditive.lean), [`flux_error_le`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuSubadditiveError.lean), [`cubeNu_mul_latticeVolume_le_sum_add`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuSubadditiveError.lean), [`sum_exp_neg_margin_le`](Rigidity/Proofs/Percolation/GeneralDim/CubeExceptionalTail.lean) | AD Lemma 4.8, (4.32) and (4.33): for a resolved `U` and `n ≤` the scale of `U`, the sum over the vertices `x` of `U` of `μ(V(x), q)` over the resolved subcubes `V(x)` of scale `n` is at most `\|U\| μ(U, q)` plus the coarse pairing of the minimizer over the exceptional lattice edges, and `\|U\| ν(U, p)` is at most the sum over `x` of `ν(V(x), p)` plus the flux pairing of the maximizer over the open edges not inside the cluster of a resolved subcube; the second is bounded by `(3^d/4) \|p\|₁² (s G + \|U\|/s)` for every `s > 0`, `G` the number of exceptional vertices. |
| [`sum_cubeForm_sub_add_sum_cubeMu_subcubes_le`](Rigidity/Proofs/Percolation/GeneralDim/CubeSecondVariation.lean), [`sum_cubeForm_sub_add_cubeNu_le_sum_subcubes`](Rigidity/Proofs/Percolation/GeneralDim/CubeSecondVariation.lean), [`cubeNuDefect_add_le`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuEnergyDefect.lean), [`exists_lintegral_cubeNuDefect_le`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuEnergyDefect.lean) | the subadditivity of `μ` and `ν` with the energies of the differences on the left side (AD, proof of Lemma 5.4, (5.11) and its analogue for `ν`): `∑_V B_V(u\|_V − u_V)/2 + ∑_V \|V\| μ(V, q) ≤ \|U\| μ(U, q) + E_q(u)` and `∑_V B_V(v\|_V − v_V)/2 + \|U\| ν(U, p) ≤ ∑_V \|V\| ν(V, p) + F_p^{exc}(v)`; and the expectation of the energy `D^ν_n(U, p)` of the differences of the maximizers of `ν` is at most `\|U\| (E[ν(V, p)] − E[ν(U, p)] + C \|p\|₁² 3^{−n/2})`. |
| [`cubeNu_eq_of_equiv`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuLocal.lean), [`measurable_cubeNu`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuLocal.lean), [`integral_cubeNu_eq_of_scale_eq`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuLocal.lean), [`integrable_cubeNu`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuLocal.lean) | `ν(U, p)` depends only on the open edges inside `U`, is a measurable and integrable function of the configuration, and `E[ν(U, p)]` is the same for all triadic cubes of a given scale (exact stationarity). |
| [`exists_integral_cubeNu_le_of_scale_le`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuMonotone.lean) | AD (4.49), every `d ≥ 2`: `E[ν(U, p)] ≤ E[ν(V, p)] + C \|p\|₁² 3^{−n/2}` for triadic cubes `V`, `U` of scales `n ≤ m`. |
| [`cubeNu_eq_sum_polarization`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`exists_tendsto_cubeNuMean`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`tendsto_cubeNuLimit`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`cubeAhom`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`cubeNuLimit_eq_cubeAhom`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`cubeAhom_symm`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`cubeAhom_bounds`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuLimit.lean), [`exists_cubeAhom_lower_bound`](Rigidity/Proofs/Percolation/GeneralDim/CubeNuLowerBoundMean.lean) | AD Definition 5.1 and (5.1), every `d ≥ 2`: `ν(U, ·)` is a quadratic form given by polarization; `E[ν(□_m, ξ)]` converges as `m → ∞`; the limit is `(1/2) ξ · ā ξ` for a symmetric matrix `ā = cubeAhom`, and `c \|ξ\|² ≤ (1/2) ξ · ā ξ ≤ (3^d/4) \|ξ\|₁²`. |

The theorems of the table and their supporting results depend only on axioms among `propext`,
`Classical.choice` and `Quot.sound`; fifty-seven of them (fifty-four theorems and three definitions)
have axiom reports in [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean). The modules are the
twenty-four files of [`Rigidity/Proofs/Percolation/GeneralDim/`](Rigidity/Proofs/Percolation/GeneralDim/).
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
  is resolved. The quantity `μ`, which uses the anchors of the partition, is not shown to be local;
  its localization, stationarity and the limit of `E[−μ]` are proved here only for `d = 2`, in the
  sections cited above.
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
[`Rigidity/Proofs/Percolation/`](Rigidity/Proofs/Percolation/) from `PlanarFlatnessInputs.lean` to
`PlanarOmegaDecay.lean`, from the weak convergence of the spatial averages of the coarsened gradients
(Lemma 5.7, display (5.25)) and the almost additivity of these averages (Lemma 5.5, display (5.12))
alone. The proofs use the coarse energy bounds (4.24), (4.25) and the display (4.26) in `L²`, which are
proved here, not assumed. With Lemma 5.10 and `planarMuLimit_eq_of_decay` this gives the
identification `lim E[−μ(□_m, q)] = (1/2) q · ā⁻¹ q` (the qualitative part of Proposition 5.2) with
the following three hypotheses, for `𝔭_c(2) < p < 1`:

- [`PlanarWeakConvergence`](Rigidity/Proofs/Percolation/PlanarFlatnessInputs.lean), display (5.25) of
  Lemma 5.7: `E[\|\|□\|⁻¹ ⟨∇[u(·, □, q)]_𝒫⟩_□ − ā_{□_n}⁻¹ q\|²] ≤ C \|q\|² (τ_n + 3^{−n/4})` for every
  triadic cube `□` of scale `n`;
- [`PlanarRestrictQuadCoarsenMu`](Rigidity/Proofs/Percolation/PlanarFlatnessInputs.lean) and
  [`PlanarRestrictQuadCoarsenNu`](Rigidity/Proofs/Percolation/PlanarFlatnessInputs.lean), display
  (5.12) of Lemma 5.5, for `n ∈ [(9/10) m, m)`, with the almost-sure measurability of the quantities
  of the display.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Percolation.exists_coarseEnergyMu_majorant`](Rigidity/Proofs/Percolation/PlanarCoarseEnergyMajorant.lean), [`exists_coarseEnergyNu_majorant`](Rigidity/Proofs/Percolation/PlanarCoarseEnergyMajorant.lean) | AD (4.24) and (4.25), `d = 2`: for every `δ > 0` the normalized energy of the coarsened minimizer of `μ` and of the coarsened maximizer of `ν` on a cube `□` is almost surely below a measurable function of expectation at most `C(δ) \|q\|² size(□)^δ`. |
| [`sum_sq_planarNuGradAvg_sub_le`](Rigidity/Proofs/Percolation/PlanarNablaAffineSq.lean), [`exists_lintegral_planarNuGradAvg_sub_le`](Rigidity/Proofs/Percolation/PlanarNablaAffineMoments.lean) | AD (4.26) in `L²(P)`, `d = 2`: the spatial average of the coarsened gradient of the maximizer of `ν(V, p)` is within `C \|p\|² 3^{−n/4}`, in the second moment, of `p`. |
| [`exists_flatness_le_multiscale`](Rigidity/Proofs/Percolation/PlanarFlatnessBound.lean) | the multiscale Poincaré inequality (AD Proposition A.2) in the form of the first display of the proof of Lemma 5.8: the mean square of `w − ℓ_ξ` minus its mean is at most `C 3^{2n}(‖∇w‖² + \|ξ\|²) + C 3^m ∑_{k=n}^{m−1} 3^k (…)`. |
| [`exists_planarMuFlatness_majorant`](Rigidity/Proofs/Percolation/PlanarFlatnessMu.lean), [`exists_lintegral_planarMuFlatness_le`](Rigidity/Proofs/Percolation/PlanarFlatnessMu.lean), [`exists_planarNuFlatness_majorant`](Rigidity/Proofs/Percolation/PlanarFlatnessNu.lean), [`exists_lintegral_planarNuFlatness_le`](Rigidity/Proofs/Percolation/PlanarFlatnessNu.lean), [`exists_planarMuFlatness_majorant_ae`](Rigidity/Proofs/Percolation/PlanarFlatnessAE.lean), [`exists_planarNuFlatness_majorant_ae`](Rigidity/Proofs/Percolation/PlanarFlatnessAE.lean) | AD Lemma 5.8, (5.32) and (5.33), `d = 2`: `E[\|□_{n+1}\|⁻¹ ∑ \|[u]_𝒫(x) − x · ā_{□_n}⁻¹ q − c\|²] ≤ C \|q\|² 3^{2n}(3^{−n/10} + 3^{−n} ∑_{k ≤ n} 3^k τ_k)` and the same for `v` and `ξ`, `c` the mean; the `_ae` forms hold from Lemmas 5.7 and 5.5 alone, with an almost-sure measurable majorant. |
| [`caccioppoli_dist`](Rigidity/Proofs/Percolation/PlanarOmegaCaccioppoli.lean), [`clusterForm_restrict_le_caccioppoli`](Rigidity/Proofs/Percolation/PlanarOmegaCaccioppoli.lean) | AD Lemma 3.5 from `□_{n+1}` to `□_n` on planar clusters: `B_{□_n}(w, w) ≤ 16 (3^n − 1)⁻² ∑_{C_*(□_{n+1})} (w − c)²` for `w` harmonic in the interior (the Caccioppoli step (5.39) of the proof of Lemma 5.9). |
| [`planarNu_sub_planarMu_sub_le`](Rigidity/Proofs/Percolation/PlanarOmegaPointwise.lean), [`planarOmega_chain`](Rigidity/Proofs/Percolation/PlanarOmegaChain.lean), [`planarOmega_real_le`](Rigidity/Proofs/Percolation/PlanarOmegaAssembly.lean), [`planarOmega_integral_le`](Rigidity/Proofs/Percolation/PlanarOmegaAssembly.lean) | the pointwise chain of the proof of Lemma 5.9, (5.38) to (5.41): `ν(V, p) − μ(V, q) − q · p` is bounded by the boundary error, three times the energies of the differences of Lemma 5.4, and the Caccioppoli term in the coarsening errors and the flatness errors of Lemma 5.8, and then, summed over the subcubes, by the subadditivity gaps; its integrated form. |
| [`exists_boundaryMajorant`](Rigidity/Proofs/Percolation/PlanarOmegaBad.lean), [`exists_lintegral_not_resolved_le`](Rigidity/Proofs/Percolation/PlanarOmegaBad.lean), [`exists_badMajorant`](Rigidity/Proofs/Percolation/PlanarOmegaBad.lean), [`exists_lintegral_subMuSum_le`](Rigidity/Proofs/Percolation/PlanarOmegaIntegrals.lean), [`exists_lintegral_subNuSum_le`](Rigidity/Proofs/Percolation/PlanarOmegaIntegrals.lean), [`exists_lintegral_nuSubGap_le`](Rigidity/Proofs/Percolation/PlanarOmegaIntegrals.lean), [`exists_muSubGap_majorant`](Rigidity/Proofs/Percolation/PlanarOmegaIntegrals.lean), [`exists_subadditivityMajorant`](Rigidity/Proofs/Percolation/PlanarOmegaMajorants.lean), [`exists_coarseError_majorant`](Rigidity/Proofs/Percolation/PlanarOmegaMajorants.lean), [`planarTau_le_weighted`](Rigidity/Proofs/Percolation/PlanarOmegaRates.lean) | the expectations of the terms of the chain: the boundary term (`C \|p\|₁ 3^{−n/2}`), the event that `□_n` is resolved and `□_{n+1}` is not (`C 9^{−n}`), the sums of `−μ` and `ν` over the subcubes by approximate stationarity, the subadditivity gaps (`C \|ξ\|₁² \|U\| 3^{−n/2}`), and the coarsening error through the reach of the partition, each with a measurable majorant, and the comparison `τ_n ≤ 3^{−n} ∑_{k ≤ n} 3^k τ_k`. |
| [`exists_planarOmegaD_le_of_inputs`](Rigidity/Proofs/Percolation/PlanarOmegaDecay.lean), [`exists_planarOmegaD_decay`](Rigidity/Proofs/Percolation/PlanarOmegaDecay.lean) | AD Lemma 5.9, (5.37), `d = 2`, in the form used by Lemma 5.10: for `n ≥ N`, `D_n ≤ K (3^{−n/10} + 3^{−n} ∑_{k ≤ n} 3^k τ_k)`, that is `D_n ≤ C σⁿ + C ∑_{l ≤ n} ρ^{n−l} τ_l` with `σ = 3^{−1/10}` and `ρ = 1/3`, without the absolute value. |
| [`Rigidity.Percolation.planarMuLimit_eq_of_inputs`](Rigidity/Proofs/Percolation/PlanarOmegaDecay.lean) | AD Proposition 5.2, qualitative part, `d = 2`: `lim E[−μ(□_m, q)] = (1/2) q · ā⁻¹ q` from `PlanarWeakConvergence`, `PlanarRestrictQuadCoarsenMu` and `PlanarRestrictQuadCoarsenNu`; the hypothesis `h59` of `planarMuLimit_eq_of_decay` is discharged by `exists_planarOmegaD_decay`. |

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
([`planarRestrictQuadCoarsenMu_holds`](Rigidity/Proofs/Cluster/PlanarRHRestrictQuad.lean),
[`planarRestrictQuadCoarsenNu_holds`](Rigidity/Proofs/Cluster/PlanarRHRestrictQuad.lean),
[`planarWeakConvergence_holds`](Rigidity/Proofs/Cluster/PlanarRHWeakConv.lean),
[`planarMuLimit_eq`](Rigidity/Proofs/Cluster/PlanarRHWeakConv.lean)): the three hypotheses of the
identification in the previous section are discharged, and
`lim E[−μ(□_m, q)] = (1/2) q · ā⁻¹ q` for every `q`.

The partition `𝓡` of Definition 3.7 is obtained from Propositions 2.1 and 2.4 applied to a local family
[`planarRHGood`](Rigidity/Proofs/Cluster/PlanarRHLocal.lean). A cube is good when, on each of its
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
| [`Rigidity.Proofs.Cluster.measurableSet_not_mem_planarRHGood_local`](Rigidity/Proofs/Cluster/PlanarRHLocal.lean) | the failure event of a cube `T` of the local family is determined by the open edges inside `3T`, as the hypothesis (2.1) of Proposition 2.1 requires. |
| [`planarRHCube_of_scales`](Rigidity/Proofs/Cluster/PlanarRHEvent.lean), [`planarRHFailureBound_holds`](Rigidity/Proofs/Cluster/PlanarRHProb.lean) | the planar form of AD Lemma 3.6 on the triple of a cube whose partition cubes are small, and the failure bound (2.2) of the local family, `C exp(−c 3^{ns})`, for `p > 𝔭_c(2)`. |
| [`planarRHPartition_of_failureBound`](Rigidity/Proofs/Cluster/PlanarRHPartition.lean), [`planarRHPartition_holds`](Rigidity/Proofs/Cluster/PlanarRHProb.lean) | the partition `𝓡` of AD Definition 3.7 in `d = 2`, with comparable neighbours, predecessors in the local family and, for every `t` and `B`, `∑_{x ∈ □} size(cell(x))^t ≤ K \|□\|` off an event of probability `C 3^{−Bk}` (Propositions 2.1 and 2.4). |
| [`Rigidity.Proofs.Cluster.planar_meyers_rh_uniform`](Rigidity/Proofs/Cluster/PlanarRHMeyers.lean), [`meyers_triadic_uniform`](Rigidity/Proofs/Cluster/MeyersUniform.lean), [`planar_meyers_uniform`](Rigidity/Proofs/Cluster/MeyersUniform.lean), [`planar_meyers_clusterHarmonic_uniform`](Rigidity/Proofs/Cluster/MeyersUniform.lean), [`partition_meyers_uniform`](Rigidity/Proofs/Cluster/MeyersUniform.lean) | AD Proposition 3.8, deterministic part, in the form `∃ ε t, ∀ K, ∃ C`: the exponents `ε` and `t` depend only on the reverse Hölder constant (as the minimal scale `𝓜_t(𝓡)` requires) and only the constant depends on the moment bound `K`; for the local family `planarRHGood` in `planar_meyers_rh_uniform`. |
| [`planarReachConcentration_holds`](Rigidity/Proofs/Cluster/PlanarReachConcentrationHolds.lean), [`Rigidity.Percolation.exists_measure_not_mem_planarCoarseGood_le`](Rigidity/Proofs/Percolation/PlanarReachDomination.lean), [`planarReach_le_stoppingSize`](Rigidity/Proofs/Percolation/PlanarReachDomination.lean) | the analogue of AD Proposition 2.4 for the planar partition: `∑_{x ∈ □} planarReach(x)^τ ≤ A \|□\|` off an event of probability `C 3^{−Bk}`, through the coarsely good cubes, whose failure is determined by the threefold enlargement and whose stopping size dominates the reach. |
| [`planarRestrictQuadCoarsenMu_holds`](Rigidity/Proofs/Cluster/PlanarRHRestrictQuad.lean), [`planarRestrictQuadCoarsenNu_holds`](Rigidity/Proofs/Cluster/PlanarRHRestrictQuad.lean) | AD Lemma 5.5, display (5.12), `d = 2`, `p > 𝔭_c(2)`: on the good event the deterministic bound of Step 3 applies, and off it the Cauchy–Schwarz inequality with a measurable majorant built from the moments of the reach. |
| [`Rigidity.Proofs.Cluster.exists_planarMuRestrictError_majorant`](Rigidity/Proofs/Cluster/PlanarRestrictErrorMajorant.lean), [`exists_planarNuRestrictError_majorant`](Rigidity/Proofs/Cluster/PlanarRestrictErrorMajorant.lean), [`measure_restrictBad_le`](Rigidity/Proofs/Cluster/PlanarRestrictBad.lean), [`Rigidity.Percolation.measurable_planarMuRestrictError`](Rigidity/Proofs/Percolation/PlanarRestrictErrorMeasurable.lean), [`measurable_planarNuRestrictError`](Rigidity/Proofs/Percolation/PlanarRestrictErrorMeasurable.lean), [`measurable_planarMuGen_indicator`](Rigidity/Proofs/Percolation/PlanarMuGeneral.lean) | the measurable majorants of the restriction errors, the probability of the bad event of the proof of Lemma 5.5, and the measurability of the errors (part of the hypothesis of the previous section, proved here). |
| [`Rigidity.Proofs.Cluster.exists_lintegral_sum_subcube_solenoidal_sq_le`](Rigidity/Proofs/Cluster/PlanarOneVarEstBound.lean), [`exists_lintegral_planarMuRestrictFieldError_le`](Rigidity/Proofs/Cluster/PlanarRestrictFieldQuad.lean) | AD Lemma 5.7, display (5.30), `d = 2`: for `n ≥ 9`, `E[\|∑_V \|□_n\|⁻¹ ⟨∇[u(·, V, q)]_𝒫, g⟩_V\|²] ≤ C \|e\|₁² \|q\|² (τ_n + 3^{−n/4})`, the sum over the subcubes `V` of scale `n` of `□_{n+1}` and `g` the solenoidal field of Step 1; the expectation of the error of the pairing of a bounded field with the coarsened gradient on `U` against its restriction to the subcubes (from the hypothesis `PlanarGehringPartition`; the same bounds with no further hypothesis, above the partition `𝓡` of `planarRHPartition_holds`, are [`exists_lintegral_sum_subcube_solenoidal_sq_le_rh`](Rigidity/Proofs/Cluster/PlanarRHWeakConv.lean) and [`exists_lintegral_planarMuRestrictFieldError_le_rh`](Rigidity/Proofs/Cluster/PlanarRHRestrictQuad.lean), on which `planarWeakConvergence_holds` rests). |
| [`Rigidity.Proofs.Cluster.exists_measure_not_planarCapGood_le`](Rigidity/Proofs/Cluster/PlanarSwitchLocProb.lean), [`exists_lintegral_sq_sub_switchLoc_le`](Rigidity/Proofs/Cluster/PlanarSwitchLocProb.lean), [`exists_variance_planarMuGradAvg_origin_le`](Rigidity/Proofs/Cluster/PlanarWeakConvOrigin.lean) | AD Proposition 4.9 and Lemma 5.7, display (5.31), `d = 2`: the planar partition is determined by the edges of a neighbourhood at the cap `k`, off an event of probability at most `C (2 · 3^{n−k} + 29)² exp(−c 3^k)`; for `n ≥ 120` and `k = ⌊n/12⌋` the pairing and its local version differ in mean square by at most `C G² \|q\|₁² 3^{−n/4}`; the variance of the spatial average at the origin is at most `C \|q\|² (τ_n + 3^{−n/4})` (the last from `PlanarGehringPartition`; with no further hypothesis in [`exists_variance_planarMuGradAvg_origin_le_rh`](Rigidity/Proofs/Cluster/PlanarRHWeakConv.lean), on which `planarWeakConvergence_holds` rests). |
| [`Rigidity.Percolation.exists_lintegral_planarMuDefect_le_tau`](Rigidity/Proofs/Percolation/PlanarDefectTauCube.lean), [`exists_lintegral_planarNuDefect_le_tau`](Rigidity/Proofs/Percolation/PlanarNuDefectTauCube.lean) | AD Lemma 5.4, display (5.10), `d = 2`, on every triadic cube `U`: `E[1{𝒫, U resolved} D_n(U, q)] ≤ \|U\| C \|q\|² (∑_{k=n}^{m−1} τ_k + 3^{−n/4})` for `μ` and for `ν`. |
| [`planarWeakConvergence_holds`](Rigidity/Proofs/Cluster/PlanarRHWeakConv.lean), [`planarMuLimit_eq`](Rigidity/Proofs/Cluster/PlanarRHWeakConv.lean) | AD Lemma 5.7, display (5.25), for every triadic cube, and AD Proposition 5.2, qualitative part, `d = 2`, `p > 𝔭_c(2)`: `lim E[−μ(□_m, q)] = (1/2) q · ā⁻¹ q`. |

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
[`Rigidity/Proofs/Cluster/`](Rigidity/Proofs/Cluster/). The decay of `D_n` of Lemma 5.9 holds
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
| [`Rigidity.Proofs.Cluster.exists_planarOmegaD_decay_holds`](Rigidity/Proofs/Cluster/PlanarConvergenceRate.lean), [`exists_planarOmegaD_le_geometric`](Rigidity/Proofs/Cluster/PlanarConvergenceRate.lean), [`exists_planarTau_le_geometric`](Rigidity/Proofs/Cluster/PlanarConvergenceRate.lean) | AD Lemma 5.9 with no hypothesis, and the geometric decay `D_n, τ_n ≤ K l^n` for `n ≥ N`, `l < 1`. |
| [`planarAhomInvLimit_eq_inv`](Rigidity/Proofs/Cluster/PlanarConvergenceRate.lean), [`exists_abs_planarAhom_inv_sub_planarAhomInvFinite_le`](Rigidity/Proofs/Cluster/PlanarConvergenceRate.lean) | AD Lemma 5.10, Step 4, `d = 2`: the limit of the finite-volume matrices is `ā⁻¹`, and `\|(ā⁻¹)_{ij} − (ā_{□_n}⁻¹)_{ij}\| ≤ K l^n` for `n ≥ N`. |
| [`planar_convexp`](Rigidity/Proofs/Cluster/PlanarConvergenceRate.lean) | AD Proposition 5.2, display (5.4), `d = 2`: there are `α ∈ (0, 1/4]` and `C` with `\|E[−μ(□_n, q)] − (1/2) q · ā⁻¹ q\| + \|E[ν(□_n, ξ)] − (1/2) ξ · ā ξ\| ≤ C (\|ξ\|² + \|q\|²) 3^{−nα}` for all `n`, `ξ`, `q`. |
| [`planar_omegadecayrate`](Rigidity/Proofs/Cluster/PlanarOmegaSupRate.lean) | AD Lemma 5.10, display (5.42), `d = 2`: for each `n` there is a measurable `M`, at least `ρ(□_n) = sup_q \|q\|⁻² ω₊(□_n, q)` almost surely, with `E[M] ≤ C 3^{−nα}`. |
| [`exists_integral_min_planarRhoStat_le`](Rigidity/Proofs/Cluster/PlanarSIStepTwo.lean) | AD Lemma 5.11, Step 2: the truncated stationary version `ρ_stat` of `ρ` on a cube `V` satisfies `E[min(ρ_stat, C₁)] ≤ C (1 + C₁) 3^{−nα}`. |
| [`measureReal_sum_ge_le_of_bounded`](Rigidity/Proofs/Cluster/BoundedChernoff.lean), [`planar_SIupgrade_step2`](Rigidity/Proofs/Cluster/PlanarSIStepTwo.lean) | the Chernoff bound of Step 2 (variables in `[0, A]` with expectations at most `ε`, each independent of the sum of any set of the others not containing it: `P[∑ ≥ \|s\| t] ≤ exp(−\|s\|(t − (e − 1)ε)/A)`), and AD Lemma 5.11, Step 2, the display at AD18.tex:3944-3947: the sum of `min(ρ_stat, C₁)` over the 729 groups of subcubes of scale `n` of a cube of scale `n + 3 + j`, `9^j` per group, exceeds `729 · 9^j t` with probability at most `729 exp(−9^j (t − (e − 1) C (1 + C₁) 3^{−nα})/C₁)`. |
| [`abs_quadratic_sub_half_le`](Rigidity/Proofs/Cluster/PlanarMinimalSet.lean), [`planar_minimalset`](Rigidity/Proofs/Cluster/PlanarMinimalSet.lean) | AD Lemma 5.3, `d = 2`, in a deterministic pointwise form: on the partition event for a resolved cube `U`, `\|μ(U, q) + (1/2) q · ā⁻¹ q\| ≤ (4 Y S + √(8 (Λ + 1)(ρ + Y S))) \|q\|²` and the corresponding bound for `ν(U, ā⁻¹ q) − (1/2) q · ā⁻¹ q`, with `Y` the random error of the comparison of Corollary 4.6, `Λ` the bound of `−μ`, `ρ` of Lemma 5.10 and `S` an `ℓ¹` operator bound of `ā⁻¹` (`‖ā⁻¹ v‖₁ ≤ S ‖v‖₁`); the statement assumes `Y(U) < ∞`, which holds almost surely since `E[Y] < ∞`. |

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
[`Rigidity/Proofs/Cluster/`](Rigidity/Proofs/Cluster/). The bounds are stated with `IsOsBond`, the
stretched exponential moment (`X ≤ O_r(θ)`) of the source, and are stable statements that the later results of
the dimension-two chain take as hypotheses
([`PlanarScaleStatements.lean`](Rigidity/Proofs/Cluster/PlanarScaleStatements.lean)).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Cluster.exists_planar_minimalScale`](Rigidity/Proofs/Cluster/PlanarMinimalScales.lean) | AD Proposition 2.4 for a family of cubes with the local measurability (2.1) and the failure bound (2.2): for every `τ` and `α > 0` a minimal scale `M ≤ O_r(θ)` such that, whenever `M ≤ 3^m`, the `τ`-th moment of the sizes on `□_m` is at most `K \|□_m\|` and every size is at most `3^{α m}`. |
| [`Rigidity.Proofs.Cluster.planarMinimalScales_holds`](Rigidity/Proofs/Cluster/PlanarMinimalScales.lean) | the statement `PlanarMinimalScales p` ([`PlanarScaleStatements.lean`](Rigidity/Proofs/Cluster/PlanarScaleStatements.lean)): the partition `𝓡` of Definition 3.7 (maximal stopping cubes of the local family `planarRHGood`), with, for all `t, α > 0`, a minimal scale `M ≤ O_r(θ)` above which on `□_m` the `t`-th moments of the sizes of the cells of `𝓡`, of the planar partition cubes and of `planarReach` are at most `K \|□_m\|` and these sizes are at most `3^{α m}`. |
| [`planarMinimalScales_partition_holds`](Rigidity/Proofs/Cluster/PlanarScaleForms.lean), [`planarMesoscopicConvergence_holds`](Rigidity/Proofs/Cluster/PlanarScaleForms.lean) | the two statements `Rigidity.Dirichlet.PlanarMinimalScales` and `Rigidity.Dirichlet.PlanarMesoscopicConvergence`, in the form of the inputs of the proof of Theorem 1 in dimension two: both bounds of (2.13) for the planar partition (`t ≥ 1`), and Proposition 5.13 on the triadic subcubes of `□_m` of scale `⌈m/8⌉`. |
| [`exists_measure_not_planarReachLe_le`](Rigidity/Proofs/Cluster/PlanarReachEvent.lean), [`planarRho_le_avg_of_planarReachLe`](Rigidity/Proofs/Cluster/PlanarReachErrors.lean), [`planarComparisonError_le_of_planarReachLe`](Rigidity/Proofs/Cluster/PlanarReachErrors.lean), [`sum_subcubesAt_eq_sum_sum`](Rigidity/Proofs/Cluster/PlanarSubcubeIndex.lean) | the event that the reach is at most `3^ℓ` on a cube and the deterministic bounds on it: `-μ`, the error of the comparison of Corollary 4.6, the subadditivity errors and the subadditivity (5.56) of `ρ`; the subcubes of `□_{n+3+j}` are the cubes `⟨n, a + 27 b⟩`. |
| [`exists_planarRho_tail`](Rigidity/Proofs/Cluster/PlanarSIUpgrade.lean) | AD Lemma 5.11, Steps 1 to 3: the stretched exponential tail of `ρ(□_{n+3+j})` at an explicit threshold, together with the event that the reach is at most `3^ℓ`. |
| [`exists_planarSubaddGood_tail`](Rigidity/Proofs/Cluster/PlanarSubaddTail.lean), [`exists_planarSubaddGood_tail_cube`](Rigidity/Proofs/Cluster/PlanarBoundN.lean) | AD Proposition 5.2 as a tail bound: `\|μ(V, q) + (1/2) q · ā⁻¹ q\| ≤ K \|q\|² 3^{−β scale V}` and `\|ν(V, ξ) − (1/2) ξ · ā ξ\| ≤ K \|ξ\|² 3^{−β scale V}` on the partition event with `V` resolved, off an event of probability at most `K' exp(−c 3^{m s})`, for `□_m` and then for every triadic cube and every translate. |
| [`planar_subadd_os`](Rigidity/Proofs/Cluster/PlanarSubaddOsMain.lean) | AD Proposition 5.2, displays (5.2) and (5.3), `d = 2`: there are `r, α, C > 0` such that, for every triadic cube `V`, the random error `X(V)` of `μ(V, ·) + (1/2) q · ā⁻¹ q` and `ν(V, ·) − (1/2) ξ · ā ξ` (with `μ = ν = 0` off the event that the partition exists and resolves `V`) is measurable with `X(V) ≤ O_r(C 3^{−α scale V})`, `\|μ-error(q)\| ≤ X \|q\|²` and `\|ν-error(ξ)\| ≤ X \|ξ\|²`. |
| [`planar_SIupgrade_os`](Rigidity/Proofs/Cluster/PlanarSIUpgradeOs.lean) | AD Lemma 5.11, `d = 2`: `sup_q \|q\|⁻² \|ω(V, q)\| ≤ O_r(C 3^{−α scale V})`, with a measurable majorant, for every triadic cube `V`. |
| [`planar_muupbound_os`](Rigidity/Proofs/Cluster/PlanarSIUpgradeOs.lean) | AD (4.17), `d = 2`, with the rate `size^{−α}` in place of `size^{−1}`: `−μ(V, q) ≤ (K + Z(V)) \|q\|²` with `Z(V) ≤ O_r(C 3^{−α scale V})`. |
| [`planarBoundN_holds`](Rigidity/Proofs/Cluster/PlanarBoundN.lean), [`exists_planarBoundN_general`](Rigidity/Proofs/Cluster/PlanarBoundN.lean) | AD Proposition 5.13, `d = 2` (the statement `PlanarBoundN p`): a random scale `N ≤ O_r(θ)` such that, whenever `N ≤ 3^m` and `n = ⌈m/4⌉`, on the triadic cubes `V` of scale `n` in `□_m`, and on `□_n` in the configuration translated by `−z` for every `z ∈ □_m`, the partition event holds, the cube is resolved, and `\|μ + (1/2) q · ā⁻¹ q\| ≤ C \|q\|² 3^{−mα}`, `\|ν − (1/2) ξ · ā ξ\| ≤ C \|ξ\|² 3^{−mα}`; the second theorem allows any `n(m)` with `n(m) ≤ m ≤ L n(m)`. |
| [`osBound_indicator`](Rigidity/Proofs/Cluster/OsTailCalculus.lean), [`OsBound.add`](Rigidity/Proofs/Cluster/OsTailCalculus.lean), [`OsBound.mul`](Rigidity/Proofs/Cluster/OsTailCalculus.lean), [`isOsBond_of_osBound`](Rigidity/Proofs/Cluster/OsTailCalculus.lean) | the calculus of the stretched exponential bounds used above, in the tail form: indicators, sums, products (AD (1.9)) and the passage to `IsOsBond`. |

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
| [`Rigidity.Dirichlet.innerEdgeEnergy_dirichletSolution_div_le_of_coarse`](Rigidity/Proofs/Dirichlet/LemmaSixTwoCoarse.lean) | AD Lemma 6.2 on the lattice: the normalized homogenized energy of the solution `u_hom` of the discrete `ā`-Dirichlet problem on a cube `Q` of side `L`, with the boundary interpolation `w̃` of the coarsened function as datum, is at most the energy of `u` in `Q` plus the errors of the `μ` test and `C((r + N)/L)^{1−2/s}` times the bound of Lemma 6.4 (iii). |
| [`Rigidity.Dirichlet.patch_cubeCutoff_of_not_mem`](Rigidity/Proofs/Dirichlet/CutoffRegions.lean) | AD Lemma 6.3 (i) on the lattice: off the cube the patched function is the outer function. |
| [`Rigidity.Dirichlet.innerEdgeEnergy_patch_div_le_of_coarse`](Rigidity/Proofs/Dirichlet/LemmaSixThreeCoarse.lean) | AD Lemma 6.3 (ii) on the lattice: the energy on the cluster of the patch `ũ` of the `ν`-maximizers and of `u_hom` is at most the homogenized energy of `u_hom` plus the boundary-layer and patching errors. |
| [`Rigidity.Dirichlet.exists_sum_sq_patch_sub_div_le_of_coarse`](Rigidity/Proofs/Dirichlet/LemmaSixThreeCoarse.lean) | AD Lemma 6.3 (iii) on the lattice: `L^{−d} Σ (ũ − u_hom)²` is at most the `L²` distances of the maximizers to their affine functions plus `C N⁴ r^{−2}` times the bound of Lemma 6.4 (iii). |
| [`Rigidity.Dirichlet.sum_abs_grad_boundaryInterpolation_rpow_div_le`](Rigidity/Proofs/Dirichlet/Interpolation.lean) | AD Lemma 6.4 (iii) on the lattice: for `1 ≤ s < p`, the normalized `Lˢ` norm of `∇w̃` is at most the moments of the partition sizes times `(V⁻¹ Σ_{C_*} \|∇u 1_{𝐚≠0}\|^p)^{s/p}`. |
| [`Rigidity.Dirichlet.sum_sq_sub_le_of_inner_energy_chain`](Rigidity/Proofs/Dirichlet/PropSixOne.lean) | AD Proposition 6.1 on the lattice, from the energy comparisons: if `u` is harmonic in `Q`, `ũ = u` off the interior of `Q`, `E_hom(u_hom) ≤ E(u) + δ₁` and `E(ũ) ≤ E_hom(u_hom) + δ₂`, then `Σ (u − u_hom)² ≤ 2P(δ₁ + δ₂)/λ + 2δ₃`, with `P` a Poincaré constant for `ũ − u` and `δ₃` a bound for `Σ (ũ − u_hom)²`. |
| [`Rigidity.Dirichlet.sum_energy_cubeLayer_div_le`](Rigidity/Proofs/Dirichlet/LayerEnergyBound.lean) | the energy of the discrete homogenized solution in the boundary layer of width `ℓ + 1` of a cube of side `N` is at most twice that of its datum plus `C((ℓ + 1)/N)^γ (N^{−d} Σ \|∇f\|^p)^{2/p}`, for `p > 2` and small `γ > 0`. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2`](Rigidity/Proofs/Regularity/KIterationGeneral.lean) | AD Lemma 7.2 for every `k`, for abstract seminorms with the excess-decay hypothesis: `D_k(r) ≤ C(r/R)^{k+1} D_k(R) + C r^{1−α}(D_0(R)/R + E/r)` for `r ∈ [X ∨ C, R/2]`. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_zero`](Rigidity/Proofs/Regularity/KIteration.lean) | AD Lemma 7.2 for `k = 0`: `D_0(r) ≤ C(r/R) D_0(R) + C r^{1−α}(D_0(R)/R + E/r)`. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_one`](Rigidity/Proofs/Regularity/KIteration.lean) | AD Lemma 7.2 for `k = 1`, with the quadratic polynomials: `D_1(r) ≤ C(r/R)² D_1(R) + C r^{1−α}(D_0(R)/R + E/r)`. |
| [`Rigidity.Proofs.Regularity.harmonicRegularity_latticeHarmonicClass`](Rigidity/Proofs/Regularity/LatticeHarmonicExcess.lean) | the excess decay of order one of the harmonic functions on the balls of `ℤᵈ`, above a fixed radius. |
| [`Rigidity.Proofs.Regularity.harmonicRegularity_planarHarmonicClass`](Rigidity/Proofs/Regularity/PlanarHarmonicRegularity.lean) | the excess decay of order one of the harmonic functions on the discs of `ℝ²`, in the normalized `L²` norms, with the constant `1024`. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_zero_latticeHarmonic`](Rigidity/Proofs/Regularity/LatticeHarmonicExcess.lean) | AD Lemma 7.2 for `k = 0` with the harmonic functions on the balls of `ℤᵈ`, from the harmonic-approximation hypothesis alone. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_one_latticeHarmonic`](Rigidity/Proofs/Regularity/LatticeHarmonicExcessTwo.lean) | AD Lemma 7.2 for `k = 1` with the harmonic functions and the harmonic quadratic functions on the balls of `ℤᵈ`, from the harmonic-approximation hypothesis alone. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_zero_planar`](Rigidity/Proofs/Regularity/PlanarHarmonicRegularity.lean) | AD Lemma 7.2 for `k = 0` in the plane, in the normalized `L²` norms of Lebesgue measure with the harmonic functions on discs, from the harmonic-approximation hypothesis alone. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_one_planar`](Rigidity/Proofs/Regularity/PlanarHarmonicRegularityTwo.lean) | AD Lemma 7.2 for `k = 1` in the plane, from the harmonic-approximation hypothesis alone. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_3_zero_planar`](Rigidity/Proofs/Regularity/PlanarMesoscopicRegularity.lean) | the iteration of AD Lemma 7.3 for `k = 0` in the plane, from the harmonic-approximation hypothesis. |
| [`Rigidity.Proofs.Regularity.armstrongDario_lemma_7_3_one_planar`](Rigidity/Proofs/Regularity/PlanarMesoscopicRegularity.lean) | the same for `k = 1`. |
| [`Rigidity.Proofs.Regularity.armstrongDario_orderZero_origin_planar`](Rigidity/Proofs/Regularity/PlanarMesoscopicRegularity.lean) | order-zero regularity at the origin in the plane: one constant `φ` with `‖u − φ‖_{L̲²(B_r)} ≤ C(r/R)B` for `r ∈ [X ∨ C, R/2]`, under the harmonic-approximation hypothesis. |

The nineteen theorems depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The modules
are in [`Rigidity/Proofs/Dirichlet/`](Rigidity/Proofs/Dirichlet/) and
[`Rigidity/Proofs/Regularity/`](Rigidity/Proofs/Regularity/).

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

## Regularity of order one at the origin from the mesoscopic estimate

`Rigidity.External.ArmstrongDarioOrderOneOrigin` (Theorem 2.4, part (iii) at `k = 1`; AD Theorem 2(iii)
at `k = 1`) is a theorem from one new hypothesis and two inputs that are already assumed:
[`ArmstrongDarioMesoscopicDegreeTwo`](Rigidity/Proofs/Regularity/OrderOneOrigin.lean), AD Lemma 7.3, display (7.18) at `k = 2`
for bond percolation at the origin, with `Ā₂` the harmonic quadratic polynomials and the normalization
`r^{−d/2} ‖·‖_{L²(𝒞_∞ ∩ B_r)}`, together with `Rigidity.External.CorrectorQuantitativeInput` and
`LatticeProb.External.SupercriticalBondCorrectorInput`. The mesoscopic estimate itself needs the
harmonic approximation of AD Lemma 7.1, hence Theorem 1 (Sections 5 and 6), and is not proved in general; in
dimension two it is proved from the estimates on squares of Lemma 7.1 (see
[Lemma 7.3 at k = 2 and regularity of order one at the origin in dimension two](#lemma-73-at-k--2-and-regularity-of-order-one-at-the-origin-in-dimension-two)).

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_of_mesoscopicDegreeTwo`](Rigidity/Proofs/Regularity/OrderOneOrigin.lean) | `ArmstrongDarioOrderOneOrigin` from `ArmstrongDarioMesoscopicDegreeTwo`, `CorrectorQuantitativeInput` and `SupercriticalBondCorrectorInput`. |
| [`Rigidity.Proofs.Regularity.ballExcess_le_of_clusterBallVolumeL2`](Rigidity/Proofs/Regularity/OrderOneOrigin.lean) | the change of normalization from `r^{−d/2} ‖·‖_{L²}` to the ball excess, under the volume comparison `K` of the cluster balls, with the constant multiplied by `√K`. |
| [`Rigidity.Proofs.Regularity.orderOneEndpointData_cluster`](Rigidity/Proofs/Regularity/ClusterOrderOne.lean), [`clusterLiftMap_mem_harmonicGrowthSpace`](Rigidity/Proofs/Regularity/ClusterOrderOne.lean) | the hypotheses of the endpoint iteration on the cluster: the lifts of the affine functions by the corrected planes, with relative error `C t^{−1/2}` on `B_t` (absolute error `C t^{1/2}`), the trace-free quadratic polynomials, and the comparison of sizes from the density of the infinite cluster in cubes. |
| [`Rigidity.Proofs.Regularity.weighted_endpoint_step`](Rigidity/Proofs/Regularity/OrderOneEndpoint.lean), [`orderOneEndpoint_step`](Rigidity/Proofs/Regularity/OrderOneEndpoint.lean), [`orderOneEndpoint_iterate`](Rigidity/Proofs/Regularity/OrderOneEndpoint.lean), [`orderOneEndpoint_fit`](Rigidity/Proofs/Regularity/OrderOneEndpoint.lean), [`exists_forall_le_of_orderOneEndpoint`](Rigidity/Proofs/Regularity/OrderOneEndpoint.lean) | the endpoint iteration for abstract data: one step at the endpoint of the scale range, the product of the step factors bounded by `exp(c r^{−δ}/(1 − θ^δ))`, the fit `N_t(u − Lℓ₀) ≤ C (t/R)² N_R(u)` at each radius `t ∈ [𝒳, R/2]`, and one lifted affine function `Lℓ` for all such radii. |

`ArmstrongDarioMesoscopicDegreeTwo` is a definition of a proposition, not an axiom. The nine theorems of the
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
- **Normalization.** The statement (7.18) is used with `|B_r| = r^d`; the Lebesgue measure
  `ω_d r^d` gives the same statement, and `Ā₂` is the space of the trace-free quadratic polynomials, as the
  homogenized matrix is a multiple of the identity.
- **The random scale.** `X = c_0 max(X_{(7.18)}, M_cube, M_corr(0), 1)` with `c_0` deterministic, and the
  exponent `s` is the minimum of the three exponents.

## Order-zero regularity and the planar corrector input from Lemma 7.1

Two reductions of the planar inputs are proved in
[`Rigidity/Proofs/Regularity/`](Rigidity/Proofs/Regularity/), together with deterministic steps of the proof of
AD Lemma 7.1 in dimension two. Lemma 7.1 itself is not proved: its estimates on squares
(`PlanarSquareEstimatesTwo`, which rests on Theorem 1, Sections 5 and 6) are a named hypothesis. The bound on the
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
  `M ≤ O_s(θ)`). The first is not proved here; the second is proved in the next section.
* **R2 in dimension two** (`SupercriticalBondCorrectorInputTwo`) from `ArmstrongDarioOrderZeroTwo`,
  `PlanarCorrectedPlaneExistenceTwo` (every slope has a corrected plane on the planar infinite cluster, AD
  Theorem 2(ii) at `k = 1`, with the sublinearity in the uniform norm of AD Remark 1.1 and (1.22)) and `PlanarOrderOneDimensionTwo` (`dim 𝒜₁ ≤ 3`, AD Theorem 2(i) at `k = 1`).
  The last two are named hypotheses.

| Lean declaration | Statement |
| --- | --- |
| [`Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_of_planarHarmonicApproximation`](Rigidity/Proofs/Regularity/PlanarOrderZeroInput.lean) | `PlanarHarmonicApproximationTwo → ArmstrongDarioOrderZeroTwo`; the other inputs it uses (the density of the infinite cluster in cubes and its concentration) are proved. |
| [`exists_planarOrderZeroDecay`](Rigidity/Proofs/Regularity/PlanarOrderZero.lean), [`le_of_geometric_step`](Rigidity/Proofs/Regularity/PlanarOrderZero.lean) | the Campanato iteration on the lattice balls of `𝒞_∞` that turns the harmonic approximation into the decay of the oscillation of `u`, and its elementary step. |
| [`planarHarmonicApproximationTwo_of_squareEstimates`](Rigidity/Proofs/Regularity/PlanarHarmonicApproximationTwo.lean), [`planarHarmonicApproximationAt_of_squareEstimates`](Rigidity/Proofs/Regularity/PlanarHarmonicApproximationSquares.lean), [`harmonicApproximation_of_squares`](Rigidity/Proofs/Regularity/PlanarHarmonicApproximationBalls.lean) | Lemma 7.1 in dimension two from the estimates on the squares `□_j`, by the iteration of Step 4 (`le_sum_squareIterCoeff`) and the comparison of the norms on squares and on lattice balls (`componentBallL2_le_squareL2`, `squareL2_le_componentBallL2`). |
| [`mem_clusterVertices_succ`](Rigidity/Proofs/Regularity/PlanarClusterInclusions.lean), [`mem_supp_of_mem_clusterVertices`](Rigidity/Proofs/Regularity/PlanarClusterInclusions.lean) | the inclusions of the clusters used in the proof: `𝒞_*(□_j) ⊆ 𝒞_∞` for a resolved square meeting `𝒞_∞`, and `𝒞_∞ ∩ □_m ⊆ 𝒞_*(□_{m+1})` when the partition scales on `□_m` are at most `m − 2`. |
| [`clusterRestrictTo_mem_clusterHarmonic`](Rigidity/Proofs/Regularity/PlanarClusterRestriction.lean), [`clusterForm_clusterRestrictTo_le`](Rigidity/Proofs/Regularity/PlanarClusterRestriction.lean) | the restriction of a function harmonic on `𝒞_∞` to `𝒞_*(V)`, for a resolved `V` with `𝒞_*(V) ⊆ 𝒞_∞`, is harmonic there, and the Caccioppoli inequality from `□_{n+1}` to `□_n` for it. |
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
(AD18.tex:5296-5318) the squares are `□_{m+3(k+1)}`, with the factor `3^{−k(m + 3(k+1)/2)}`, where
AD18.tex:5137-5146 prints `□_{m+3k}`. It does not affect Lemma 7.3.

## Lemma 7.3 at k = 2 and regularity of order one at the origin in dimension two

AD Lemma 7.3, display (7.18) at `k = 2`, is proved for planar bond percolation
(`ArmstrongDarioMesoscopicDegreeTwoPlanar`, the planar case of `ArmstrongDarioMesoscopicDegreeTwo`) from the
estimates on squares of the proof of Lemma 7.1 (`PlanarSquareEstimatesTwo`). With it,
`Rigidity.External.ArmstrongDarioOrderOneOriginTwo` (AD Theorem 2(iii) at `k = 1`, at the origin, in the plane)
is proved from `PlanarSquareEstimatesTwo`, Theorem 1 of Dario in dimension two (`DarioOptimalCorrectorTwo`),
`PlanarCorrectedPlaneExistenceTwo` and `PlanarOrderOneDimensionTwo`. The other inputs are proved: the minimal
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
| [`mesoscopicDegreeTwoAt_of_inputs`](Rigidity/Proofs/Regularity/PlanarMesoscopicDegreeTwo.lean), [`armstrongDarioMesoscopicDegreeTwoPlanar_of_inputs`](Rigidity/Proofs/Regularity/PlanarMesoscopicDegreeTwo.lean), [`armstrongDarioOrderOneOriginTwo_of_inputs`](Rigidity/Proofs/Regularity/PlanarMesoscopicDegreeTwo.lean) | (7.18) at `k = 2` almost surely, for one law and for every supercritical law, from Lemma 7.1 (`PlanarCoarseHarmonicApproximationTwo`) and the minimal scales of the partition cubes (`PlanarPartCubeMoments`), with `δ = α/2`; and Theorem 2(iii) at `k = 1` in the plane with the planar corrector inputs. |
| [`mesoscopicDegreeTwo_core`](Rigidity/Proofs/Regularity/PlanarMesoscopicTwoMain.lean) | (7.18) at `k = 2` for one configuration, on `[r₀X, R/2]`, from Lemma 7.1 in the form of the proof of Lemma 7.3, partition cubes of side at most `c R^{α/2}` in `B_R` whose sizes have moments of orders one and two at most `K R²`, and the density of the cluster in cubes. |
| [`coarse_top_bounds`](Rigidity/Proofs/Regularity/PlanarMesoscopicTwoTopBounds.lean), [`harmonicApproximation_error_le`](Rigidity/Proofs/Regularity/PlanarMesoscopicTwoTopBounds.lean) | the excesses of `[u]_𝒫` over the lattice harmonic quadratic functions and over the constants at the top scale `T` bounded by the cluster excesses of `u` on `B_R` and the harmonic-approximation error at `4T`; that error bounded through the crude bound of the coarse oscillation at `R/2`. |
| [`armstrongDario_lemma_7_2_two_latticeHarmonic`](Rigidity/Proofs/Regularity/LatticeKIterationTwo.lean), [`armstrongDario_lemma_7_3_two_latticeHarmonic`](Rigidity/Proofs/Regularity/LatticeKIterationTwo.lean) | AD Lemma 7.2 at `k = 2` and its iteration for the harmonic functions on the balls of `ℤ²`, from the harmonic-approximation hypothesis alone. |
| [`harmonicRegularity_three_latticeHarmonicClass`](Rigidity/Proofs/Regularity/LatticeHarmonicExcessThree.lean), [`polynomialComparison_latticeHarmonicCubic`](Rigidity/Proofs/Regularity/LatticeCubicComparison.lean) | the excess decay of order three of the harmonic functions on the balls of `ℤ²` (harmonic third-order expansion at a corner and fourth differences), and the comparison of the excesses of the lattice harmonic cubic polynomials over the harmonic quadratic functions on two balls (third differences). |
| [`componentBallL2_le_sum_abs_of_latticeHarmonic`](Rigidity/Proofs/Regularity/LatticeHarmonicMeanValue.lean) | the `ℓ^∞`–`ℓ¹` bound `‖g‖_{L̲²(B_ρ)} ≤ C ρ^{−2} Σ_{B_{4ρ}} \|g\|` for `g` lattice harmonic on `B_{4ρ}`, by an absorption over boxes. |
| [`orderOneOrigin_of_mesoscopicDegreeTwoAt`](Rigidity/Proofs/Regularity/OrderOneOriginTwo.lean), [`armstrongDarioOrderOneOriginTwo_of_mesoscopicDegreeTwoPlanar`](Rigidity/Proofs/Regularity/OrderOneOriginTwo.lean) | the reduction of Theorem 2(iii) at `k = 1` to (7.18) at `k = 2` for one dimension and one law, and its planar case. |
| [`armstrongDario_lemma_7_2_two_planar`](Rigidity/Proofs/Regularity/PlanarHarmonicRegularityThree.lean), [`armstrongDario_lemma_7_3_two_planar`](Rigidity/Proofs/Regularity/PlanarHarmonicRegularityThree.lean) | AD Lemma 7.2 at `k = 2` and its iteration in the plane for the continuum norms, with the harmonic cubic polynomials as `Ā₃`. |

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

## The corrector estimate, the Green column and the Green function estimate in dimension two

Three planar inputs are reduced to named statements of Dario and of Dario and Gu, in
[`Rigidity/Proofs/Corrector/`](Rigidity/Proofs/Corrector/) and [`Rigidity/Proofs/Green/`](Rigidity/Proofs/Green/):

* **R6 in dimension two** (`SupercriticalBondGreenColumnExistenceTwo`) from `SupercriticalBondCorrectorInputTwo`
  alone: the existence of the planar Green columns is proved, and the uniqueness follows from the uniqueness of the
  zero-slope corrected plane (`supercriticalBondGreenColumnExistenceTwo_of_correctorInput`).
* **R5 in dimension two** (`CorrectorQuantitativeInputTwo`, Dario and Gu, Proposition 2.12) from
  `DarioOptimalCorrectorTwo`, Theorem 1 of Dario in dimension two, and `SupercriticalBondCorrectorInputTwo`
  (`correctorQuantitativeInputTwo_of_dario`). `DarioOptimalCorrectorTwo` states: for every `p ∈ (𝔭_c(2), 1)`
  there are `s, C > 0` such that for all `x, y ∈ ℤ²` and every slope `q` there is a measurable `Z` with
  `Z ≤ O_s(C ‖q‖₁ √(log(2 + ‖x − y‖)))` and, almost surely, every corrected plane `ℓ` of slope `q` satisfies
  `|(ℓ(x) − q·x) − (ℓ(y) − q·y)| ≤ Z` for `x, y` in the infinite cluster. It is a named hypothesis.
* **R7 in dimension two** (`SupercriticalBondGreenQuantitativeTwo`, Dario and Gu, Theorem 2) from
  `DarioGuHeatKernelTwo`, Theorem 1 of Dario and Gu for the heat kernel `openHeat` of the infinite cluster (for
  `t ≥ 1`), and the Liouville theorem at order zero, which follows from `SupercriticalBondCorrectorInputTwo` or
  from `ArmstrongDarioOrderZeroTwo`
  (`supercriticalBondGreenQuantitativeTwo_of_darioGu_of_correctorInput`, `..._of_orderZero`). The small-time bound
  of the Carne–Varopoulos type is proved for the lazy walk (`lazyPow_le_carneVaropoulos`, `heatSmallTimeTwo`), so
  the hypothesis `CarneVaropoulosTwo` is not used.

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
are consequences of `DarioOptimalCorrectorTwo`, `DarioGuHeatKernelTwo`, `PlanarHarmonicApproximationTwo`,
`PlanarCorrectedPlaneExistenceTwo` and `PlanarOrderOneDimensionTwo`. The proofs of `DarioOptimalCorrectorTwo` and
`DarioGuHeatKernelTwo` are not part of this repository.

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

## Guarantees

- **No `sorry`.** The library has none. The four comparator challenges under
  [`RigidityAudit/`](RigidityAudit/) each contain one intentional statement-level `sorry`, which the
  corresponding solution proves.
- **Standard axioms only.** [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean) prints 448 axiom
  reports: the theorem of each of the 43 proved results, Lemma 5.25 as printed, the six
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
  the seven theorems of [Green columns for d ≥ 3](#green-columns-for-d--3), the two theorems of
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
  the nine theorems and one definition of
  [Regularity of order one at the origin from the mesoscopic estimate](#regularity-of-order-one-at-the-origin-from-the-mesoscopic-estimate),
  the twenty-three theorems of
  [Propositions 5.2 and 5.13, Lemma 5.11 and the minimal scales in dimension two](#propositions-52-and-513-lemma-511-and-the-minimal-scales-in-dimension-two),
  the nineteen theorems of
  [Order-zero regularity and the planar corrector input from Lemma 7.1](#order-zero-regularity-and-the-planar-corrector-input-from-lemma-71),
  the twenty-one theorems of
  [Lemma 7.3 at k = 2 and regularity of order one at the origin in dimension two](#lemma-73-at-k--2-and-regularity-of-order-one-at-the-origin-in-dimension-two),
  and the twenty-seven theorems of
  [The corrector estimate, the Green column and the Green function estimate in dimension two](#the-corrector-estimate-the-green-column-and-the-green-function-estimate-in-dimension-two).
  Each of the 469 reports lists only axioms among `propext`, `Classical.choice` and
  `Quot.sound`. [`scripts/check_axioms.py`](scripts/check_axioms.py) fails on any other axiom, on
  `sorryAx`, or on a missing report. The literature inputs are hypotheses, not axioms, so they do
  not appear in the reports of the theorems.
- **Independent check of the statements.** Theorems 1.1, 1.2, 1.3 and 6.5 are restated using mathlib
  alone in [`RigidityAudit/Lipschitz/`](RigidityAudit/Lipschitz/),
  [`RigidityAudit/IntegerLinearGrowth/`](RigidityAudit/IntegerLinearGrowth/),
  [`RigidityAudit/FastDecay/`](RigidityAudit/FastDecay/) and
  [`RigidityAudit/SlowMixing/`](RigidityAudit/SlowMixing/). Each `Challenge.lean` restates every
  definition that its statement unfolds to and the literature inputs that the theorem takes as
  hypotheses; each `Solution.lean` proves the restatement from the library; and
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
  hypotheses; six of them are proved, and the versions described there discharge them.

## Size

`Rigidity/` and `Rigidity.lean`: 1286 Lean files with 246,397 lines, on top of mathlib and
Lattice-Probability, including the 153 copied modules under `Rigidity/Vendor/` (32,183 lines; see
[Copied code](#copied-code)). The comparator pairs (15 files, 5,052 lines) and the axiom report
`RigidityAudit/Axioms.lean` (801 lines) are counted separately.

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
and builds the comparator pairs; **Comparator audit** runs the comparator on the four pairs. CI runs
on pushes to `main` that change more than documentation, the paper, `formalization.yaml` or
`CITATION.cff`; the comparator audit runs when it is started manually. Both workflows can be started
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
      PlanarGreenInputs.lean  Theorem 1.3 from five planar inputs, with the planar Green columns
    Cluster/                  the coarse-grained and elliptic inequalities on the cluster of Armstrong and Dario (AD §3)
    Dirichlet/                the homogenization error for the Dirichlet problem of Armstrong and Dario (AD §6)
    Green/                    Green columns and heat kernel bounds of the cluster for d ≥ 3
    Multiscale/               the multiscale Poincaré inequality of Armstrong and Dario (Proposition A.2)
    Partition/                the partition of ℤᵈ into good triadic cubes of Armstrong and Dario (AD §2)
    Regularity/               the excess-decay iteration of Armstrong and Dario (AD §7)
  Percolation/                supercritical estimates in boxes and slabs for the literature inputs
    Bootstrap/, Blocks/       the slab connectivity above the critical point (d ≥ 3)
    Pisztora/                 well-connected cubes and finite clusters (d ≥ 3)
  Support/                    definitions and lemmas used by the frozen results
  Vendor/                     modules copied from other repositories (see Copied code)
RigidityAudit/
  Axioms.lean                 the axiom report of every numbered result and of the further results
  Lipschitz/, IntegerLinearGrowth/, FastDecay/, SlowMixing/
                              the mathlib-only comparator pairs of Theorems 1.1, 1.2, 1.3 and 6.5
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
dependency. Each copied file starts with a header naming its source repository, file and commit.
The headers of the modules from formal-math, openai/math, Leonardo Bonanno's repository and
Lattice-High-Contrast-Homogenization also state the changes made; the modules from
Lattice-Probability are adapted from the named revision, and the headers of the five modules
adapted from its revision `7512f4fb` state the changes.

| Source | Commit | Files in this repository |
| --- | --- | --- |
| [anthropics/formal-math](https://github.com/anthropics/formal-math/tree/795efb86f191735c5481675763537cfb4ff37e55/percolation), the `percolation/` project (Apache License 2.0; its `LICENSE` and `NOTICE` are kept verbatim in [`Rigidity/Vendor/FormalMathPercolation/`](Rigidity/Vendor/FormalMathPercolation/)) | `795efb86f191735c5481675763537cfb4ff37e55` | the 53 modules under `Rigidity/Vendor/FormalMathPercolation/`, from the files of the same paths under `percolation/Percolation/` |
| [openai/math](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae) (Apache License 2.0; text in [`Rigidity/Vendor/CriticalPercolation/LICENSE`](Rigidity/Vendor/CriticalPercolation/LICENSE)) | `4eaee87548250b2682affda7d05d947c05554bae` | the 44 modules under `Rigidity/Vendor/CriticalPercolation/`, from `lean/OAI/Probability/CriticalPercolation/` |
| Leonardo Bonanno, [lean-formalizations](https://github.com/leobon12/lean-formalizations/tree/31e748330ee154d5f41537c4b01f71b8a5510c2d) (no licence stated upstream) | `31e748330ee154d5f41537c4b01f71b8a5510c2d` | `Rigidity/Vendor/BonannoPerc/`: `Basic`, `Duality`, `DualityMain`, `Exclusive`, `ExclusiveMain`, `Paths`, `Peierls`, `StepSum`, from the files of the same names in `LQGMetric/Perc/` |
| [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability/tree/c21955fb1c127db67c43b995f47db4543f88f9fd) (Apache License 2.0) | `c21955fb1c127db67c43b995f47db4543f88f9fd` | the 12 modules under `Rigidity/Proofs/Topology/PlanarJordan/`, which are based on Leonardo Bonanno's lean-formalizations and on R. Kirov's [jordan_pick](https://github.com/rkirov/jordan_pick/tree/b3c9b7cf7358bf81a077d78ad67e6e8247869ddd) (Apache License 2.0) |
| [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability/tree/a6fae9f9df6a47c15e338b928807feb20d9da4b0) (Apache License 2.0) | `a6fae9f9df6a47c15e338b928807feb20d9da4b0` | `Rigidity/Proofs/Percolation/Kesten/`: `EdgeCrossing`, `DualDecayRectangle`, `RigidityCrossingAdapter` |
| [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability/tree/7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069) (Apache License 2.0) | `7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069` | `Rigidity/Support/PlanarOrderZeroGradient.lean`, `Rigidity/Support/PlanarGreenQuantitativeField.lean`, `Rigidity/Proofs/S3/PlanarCorrectorValid.lean`, `Rigidity/Proofs/S3/PlanarGreenColumn.lean`: theorems of the modules `LatticeOrderZeroApproximation`, `LatticeOrderZeroTranslation`, `LatticeOrderZeroGradient`, `GreenQuantitativeField`, `MeasurableRootedPlane` and `GreenColumnEvent` of `LatticeProb/Prob/Percolation/`, specialized to `d = 2`; `Rigidity/Proofs/Green/LocalNash.lean`: `heat_step_of_faberKrahnOn`, adapted from `heat_step` of `LatticeProb/Graph/OnDiagonal.lean` |
| Lattice-High-Contrast-Homogenization (a private repository; Apache License 2.0, text in [`Rigidity/Vendor/LHCH/LICENSE`](Rigidity/Vendor/LHCH/LICENSE)) | `f47a932a9f7a07e1692bfe4aae564d02e8ca0944` | the 48 modules under `Rigidity/Vendor/LHCH/`, from the files of the same paths under `LatticeHC/`; [`Rigidity/Proofs/Cluster/SobolevCubePoincare.lean`](Rigidity/Proofs/Cluster/SobolevCubePoincare.lean), adapted from `LatticeHC/Support/Analysis/CubePoincare.lean` (squares replaced by `p`-th powers) |

The repository of Leonardo Bonanno does not state a licence, and none is claimed here for the
modules copied from it.

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
