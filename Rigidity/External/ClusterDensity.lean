import Rigidity.External.CorrectorQuantitative

/-! Concentration of the density of the infinite cluster in triadic cubes (literature input).

Source: P. Dario and C. Gu, *Quantitative homogenization of the parabolic and elliptic Green's
functions on percolation clusters*, arXiv:1909.10439v4, Appendix A, Proposition A.1 (LaTeX label
`prop:DensityContrentration`, PDF p. 60). It replaces the citation of Penrose–Pisztora at paper
L508-511 (correction C35 of the corrected draft): Penrose–Pisztora, Theorem 1, concerns continuum
percolation, and their lattice theorems are stated for site percolation.

Setting of the source (§1.6.1): i.i.d. conductances `a(e) ∈ {0} ∪ [λ, 1]` with
`𝔭 = P[a(e) ≠ 0] > p_c(d)`, `d ≥ 2`; Bernoulli bond percolation of parameter `𝔭` is the case
`a ∈ {0, 1}`, and the density of `𝒞_∞` only depends on the set of open bonds. It is stated here for
`p_c(d) < p < 1`, the range of the paper.

Conventions (§1.6 of the source).
* A triadic cube is `□_m(z) := z + (-3^m/2, 3^m/2)^d`, `z ∈ 3^m ℤ^d`, `m ∈ ℕ`, as a set of
  vertices of `ℤ^d`; its size is `3^m`, and `𝒯_m = {z + □_m : z ∈ 3^m ℤ^d}`. Here `z = 3^m k`,
  `k ∈ ℤ^d` (`triadicCube`).
* `|A|` is the number of vertices of `A`; `θ(𝔭) = P[0 ∈ 𝒞_∞]` is `LatticeProb.Percolation.theta`.
* `X ≤ 𝒪_s(θ)` means `E[exp((θ⁻¹X)_+^s)] ≤ 2` (eq. `eq:ODef`), which is `IsOsBond`.
* `𝒞_∞` is the almost surely unique infinite open cluster. The random variable `|𝒞_∞ ∩ □|` is
  `infiniteClusterCount □`, the number of vertices of `□` whose open cluster is infinite; it equals
  `|𝒞_∞ ∩ □|` whenever the infinite open cluster exists and is unique, hence almost surely.
-/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.External

/-- The triadic cube `□_m(3^m k) = ℤ^d ∩ (3^m k + (-3^m/2, 3^m/2)^d)` of size `3^m`, `k ∈ ℤ^d`. -/
def triadicCube (d m : ℕ) (k : Vertex d) : Set (Vertex d) :=
  {y | ∀ i, |(y i : ℝ) - 3 ^ m * (k i : ℝ)| < 3 ^ m / 2}

/-- The number of vertices of `Q` whose open cluster is infinite: `|𝒞_∞ ∩ Q|` when the infinite
open cluster `𝒞_∞` exists and is unique. -/
noncomputable def infiniteClusterCount {d : ℕ} (Q : Set (Vertex d)) (ω : Configuration d) : ℕ :=
  {y ∈ Q | ω ∈ infiniteComponentEvent y}.ncard

/-- **Concentration of the density of the infinite cluster** (literature input; Dario–Gu,
arXiv:1909.10439v4, Proposition A.1): "There exists a positive constant `C(d,𝔭) < ∞` such that for
any triadic cube `□ ∈ 𝒯` of size `3^m`, one has an estimate
`| |𝒞_∞ ∩ □| / |□| - θ(𝔭) | ≤ 𝒪_{2(d-1)/(3d²+2d-1)}(C 3^{-dm/2})`."
Bond percolation, `d ≥ 2`, `p_c(d) < p < 1`. -/
def ClusterDensityConcentrationInput : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex d),
      IsOsBond d p
        (fun ω => |(infiniteClusterCount (triadicCube d m k) ω : ℝ) /
          ((triadicCube d m k).ncard : ℝ) - theta d p|)
        (2 * ((d : ℝ) - 1) / (3 * (d : ℝ) ^ 2 + 2 * (d : ℝ) - 1))
        (C * (3 : ℝ) ^ (-((d : ℝ) * (m : ℝ)) / 2))

end Rigidity.External
