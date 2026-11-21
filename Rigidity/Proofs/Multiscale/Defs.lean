import Rigidity.Percolation.IntegerCube

/-!
# The discrete multiscale Poincaré inequality: statement

Armstrong–Dario, *Elliptic regularity and quantitative homogenization on percolation clusters*
(CPAM 2018), Appendix "Multiscale Poincaré inequality", Proposition 8.2 (`p.mspoincare`): for
`n, m ∈ ℕ` with `n ∈ [m/2, m]` there is `C(d) < ∞` such that for every `u : ℤ^d ∩ □_m → ℝ`,

`‖u - (u)_{□_m}‖_{L̲²(ℤ^d ∩ □_m)} ≤ C 3^n ‖∇u‖_{L̲²(ℤ^d ∩ □_m)}
  + C Σ_{k=n}^{m-1} 3^k (|3^k ℤ^d ∩ □_m|⁻¹ Σ_{y ∈ 3^k ℤ^d ∩ □_m} | |□_k|⁻¹ ⟨∇u⟩_{ℤ^d ∩ (y + □_k)} |²)^{1/2}`.

Conventions.
* `□_m = (-3^m/2, 3^m/2)^d ⊆ ℝ^d`; it is stated here for every triadic cube `3^m z + □_m`,
  `z ∈ ℤ^d`, whose lattice points are `cube m z`. For `y ∈ 3^k ℤ^d`, `ℤ^d ∩ (y + □_k)` is
  `cube k (y / 3^k)`, and `|□_k| = 3^{dk}` is the Lebesgue measure of `□_k`.
* `L̲²` norms are normalized by the number of lattice points; `(u)_A` is the mean over `A`.
* `|∇u|²(x) = (1/2) Σ_{y ∈ A, y ∼ x} |u(x) - u(y)|²` on the domain `A` (AD §1.2), the neighbours
  of `x` being `x ± e_i`.
* `⟨∇u⟩_B ∈ ℝ^d` is the spatial sum of the gradient over the edges of `B`, counted once per
  unordered edge: its `j`-th coordinate is `Σ_{x, x + e_j ∈ B} (u(x + e_j) - u(x))`. This is the
  normalization of the Dirichlet form of AD §1.2 and of the coarse pairing of AD §4, for which
  `|□_k|⁻¹ ⟨∇ℓ_ξ⟩_{y + □_k}` is close to `ξ` for the affine function `ℓ_ξ(x) = ξ · x`, as in the
  application of the inequality in AD §5 (Lemma 5.8); the inner product of AD §1.2 counts each
  edge in both orientations, which only changes the constant.
* A function on `ℤ^d ∩ □_m` is a function on `ℤ^d`; only its values on the cube enter.
-/

namespace Rigidity.Proofs.Multiscale

open LatticeProb.Percolation Rigidity.Percolation

noncomputable section

variable {d : ℕ}

/-- The unit vector `e_i` of `ℤ^d`. -/
def unitVec (i : Fin d) : Vertex d := Pi.single i 1

/-- The lattice points `ℤ^d ∩ (3^m z + □_m)` of the triadic cube of scale `m` and index `z`,
where `□_m = (-3^m/2, 3^m/2)^d`. -/
def cube (m : ℕ) (z : Vertex d) : Finset (Vertex d) :=
  (TriadicCube.mk m z).toIntegerCube.vertices

/-- The points `3^k ℤ^d ∩ (3^m z + □_m)`: the centers of the subcubes of scale `k`. -/
def centers (m : ℕ) (z : Vertex d) (k : ℕ) : Finset (Vertex d) :=
  (cube m z).filter fun y => ∀ i, (3 : ℤ) ^ k ∣ y i

/-- The lattice points `ℤ^d ∩ (y + □_k)` of the subcube of scale `k` centered at `y ∈ 3^k ℤ^d`. -/
def subcube (k : ℕ) (y : Vertex d) : Finset (Vertex d) :=
  cube k fun i => y i / 3 ^ k

/-- The mean `(u)_A = |A|⁻¹ Σ_{x ∈ A} u(x)` of a function over a finite set of vertices. -/
def finsetMean (A : Finset (Vertex d)) (u : Vertex d → ℝ) : ℝ :=
  ((A.card : ℝ))⁻¹ * ∑ x ∈ A, u x

/-- The squared magnitude of the gradient on the domain `A`,
`|∇u|²(x) = (1/2) Σ_{y ∈ A, y ∼ x} |u(x) - u(y)|²`, the neighbours of `x` being `x ± e_i`. -/
def gradNormSq (A : Finset (Vertex d)) (u : Vertex d → ℝ) (x : Vertex d) : ℝ :=
  (1 / 2) * ∑ i : Fin d,
    ((if x + unitVec i ∈ A then (u x - u (x + unitVec i)) ^ 2 else 0) +
      (if x - unitVec i ∈ A then (u x - u (x - unitVec i)) ^ 2 else 0))

/-- The spatial sum `⟨∇u⟩_B ∈ ℝ^d` of the gradient over the edges of `B`, once per unordered edge:
`⟨∇u⟩_B · e_j = Σ_{x ∈ B, x + e_j ∈ B} (u(x + e_j) - u(x))`. -/
def gradSum (B : Finset (Vertex d)) (u : Vertex d → ℝ) : Fin d → ℝ := fun j =>
  ∑ x ∈ B, if x + unitVec j ∈ B then u (x + unitVec j) - u x else 0

/-- The mean square, over the subcubes of scale `k` of `3^m z + □_m`, of the normalized spatial
average of the gradient: `|3^k ℤ^d ∩ □_m|⁻¹ Σ_y | |□_k|⁻¹ ⟨∇u⟩_{ℤ^d ∩ (y + □_k)} |²`. -/
def subcubeGradMeanSq (m : ℕ) (z : Vertex d) (k : ℕ) (u : Vertex d → ℝ) : ℝ :=
  ((centers m z k).card : ℝ)⁻¹ * ∑ y ∈ centers m z k, ∑ j : Fin d,
    ((((3 : ℝ) ^ k) ^ d)⁻¹ * gradSum (subcube k y) u j) ^ 2

/-- **Discrete multiscale Poincaré inequality** (Armstrong–Dario 2018, Proposition 8.2): there is
`C(d) < ∞` such that for all `n, m ∈ ℕ` with `n ∈ [m/2, m]`, every triadic cube `3^m z + □_m` and
every `u`,
`‖u - (u)_{□_m}‖_{L̲²} ≤ C 3^n ‖∇u‖_{L̲²} + C Σ_{k=n}^{m-1} 3^k (subcubeGradMeanSq m z k u)^{1/2}`. -/
def MultiscalePoincare (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ m n : ℕ, (m : ℝ) / 2 ≤ n → n ≤ m → ∀ (z : Vertex d) (u : Vertex d → ℝ),
    Real.sqrt (((cube m z).card : ℝ)⁻¹ *
        ∑ x ∈ cube m z, (u x - finsetMean (cube m z) u) ^ 2) ≤
      C * (3 : ℝ) ^ n * Real.sqrt (((cube m z).card : ℝ)⁻¹ *
          ∑ x ∈ cube m z, gradNormSq (cube m z) u x) +
        C * ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (subcubeGradMeanSq m z k u)

end

end Rigidity.Proofs.Multiscale
