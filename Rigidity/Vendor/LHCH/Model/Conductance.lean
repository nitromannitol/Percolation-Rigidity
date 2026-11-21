/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Model/Conductance.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Lattice

/-!
# Conductances: the operator, the Dirichlet Green function, and the kernel form

The objects of Appendix A built from a field `c` of conductances on the edges of `ℤ^d`:
* the operator `L_c = ∇* c ∇` and its restriction `L_{c,U}` to a finite set `U`;
* the Dirichlet Green function `g_U = L_{c,U}⁻¹`, extended by zero outside `U × U` (§4.1);
* the fields `μ_x = Σ_{y ∼ x} c_{xy}` and `ν_x = Σ_{y ∼ x} c_{xy}⁻¹`, averages and local norms
  `‖f‖_{p,B}` (used by (e:weighted-Sobolev) and (e:local-corrector));
* the kernel form `𝒦(a) = Σ_{x,y} |a_x a_y| (1 + |x-y|)^{2-d}` of (H3).

The edges at a site `x` are `(x, j)`, joining `x` to `x + e_j`, and `(x - e_j, j)`, joining
`x - e_j` to `x`.

Junk-value decisions:
* `ν` is `ℝ≥0∞`-valued, so that `c = 0` gives `c⁻¹ = ∞` and not `0`.
* `L_{c,U}⁻¹` is `Matrix.inv`. The matrix is positive definite for positive conductances (proved in
  Support), so its junk value `0` is never read under the paper's hypotheses.
-/

namespace LatticeHC

open MeasureTheory LatticeProb
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- `L_c u(x) = Σ_{y ∼ x} c_{xy} (u(x) - u(y))`, the operator `L_c = ∇* c ∇` (§4.1). -/
def condLaplacian (c : Edge d → ℝ) (u : Site d → ℝ) (x : Site d) : ℝ :=
  ∑ j : Fin d, (c (x, j) * (u x - u (x + unit j)) + c (x - unit j, j) * (u x - u (x - unit j)))

/-- `u` is `c`-harmonic on `S`: `L_c u = 0` on `S` (§4.2). -/
def IsHarmonicOn (c : Edge d → ℝ) (u : Site d → ℝ) (S : Set (Site d)) : Prop :=
  ∀ x ∈ S, condLaplacian c u x = 0

/-- The restriction `L_{c,U}` of `L_c` to `U × U` (§4.1). -/
def condLaplacianU (c : Edge d → ℝ) (U : Finset (Site d)) : Matrix U U ℝ :=
  fun x z => condLaplacian c (fun y => if y = z.1 then 1 else 0) x.1

/-- The Dirichlet Green function `g_U = L_{c,U}⁻¹` of `c` on `U`, extended by zero outside `U × U`
(§4.1). -/
def dirichletGreen (c : Edge d → ℝ) (U : Finset (Site d)) (x z : Site d) : ℝ :=
  if hx : x ∈ U then if hz : z ∈ U then (condLaplacianU c U)⁻¹ ⟨x, hx⟩ ⟨z, hz⟩ else 0 else 0

/-- `μ_x = Σ_{y ∼ x} c_{xy}` (§4, before `p:spatial`), valued in `ℝ≥0∞`. -/
def muField (c : Edge d → ℝ) (x : Site d) : ℝ≥0∞ :=
  ∑ j : Fin d, (ENNReal.ofReal (c (x, j)) + ENNReal.ofReal (c (x - unit j, j)))

/-- `ν_x = Σ_{y ∼ x} c_{xy}⁻¹` (§4, before `p:spatial`), valued in `ℝ≥0∞` so that `0⁻¹ = ∞`. -/
def nuField (c : Edge d → ℝ) (x : Site d) : ℝ≥0∞ :=
  ∑ j : Fin d, ((ENNReal.ofReal (c (x, j)))⁻¹ + (ENNReal.ofReal (c (x - unit j, j)))⁻¹)

/-- The average `avg_B f = |B|⁻¹ Σ_{x ∈ B} f(x)` over a finite set. -/
def avg (B : Finset (Site d)) (f : Site d → ℝ≥0∞) : ℝ≥0∞ := (B.card : ℝ≥0∞)⁻¹ * ∑ x ∈ B, f x

/-- The local norm `‖f‖_{p,B} = (|B|⁻¹ Σ_{x ∈ B} |f(x)|^p)^{1/p}` (§4, before `p:spatial`).

The definition has junk values: for `p ≤ 0` it is not the intended norm (at `p = 0` the exponent
`1 / p` is `0` in `ℝ`), and for empty `B` the average is `0`. The lemmas about `localNorm` carry
`0 < p` (or a Hölder-conjugate pair of exponents) and `B.card ≠ 0` hypotheses where the value
matters. -/
def localNorm (p : ℝ) (B : Finset (Site d)) (f : Site d → ℝ≥0∞) : ℝ≥0∞ :=
  avg B (fun x => f x ^ p) ^ (1 / p)

/-- The kernel form `𝒦(a) = Σ_{x,y} |a_x a_y| (1 + |x - y|)^{2-d}` of a function supported in `U`
(`p:Green-forms`, (H3)). -/
def kernelForm (U : Finset (Site d)) (a : Site d → ℝ) : ℝ :=
  ∑ x ∈ U, ∑ y ∈ U, |a x * a y| * (1 + euclidNorm (x - y)) ^ (2 - (d : ℝ))

end

end LatticeHC
