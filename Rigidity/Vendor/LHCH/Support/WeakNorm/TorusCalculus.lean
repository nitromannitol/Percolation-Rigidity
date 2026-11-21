/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/TorusCalculus.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusPairing

/-!
# Difference calculus on the periodic lattice

The vocabulary of the lattice multiscale Poincaré inequality: functions on `ℤ^d` of period `2N`
in every coordinate, which are the functions on the torus of side `2N` whose fundamental domain is
`torusBox d N`; the discrete Laplacian `∇*∇`; and the mixed second differences `∇_i∇_j`. No
property is proved here.
-/

namespace LatticeHC

open LatticeProb

noncomputable section

variable {d : ℕ}

/-- `f` has period `2N` in every coordinate. -/
def IsTorusPeriodic (N : ℕ) (f : Site d → ℝ) : Prop :=
  ∀ (x : Site d) (i : Fin d), f (x + (2 * (N : ℤ)) • unit i) = f x

/-- The discrete Laplacian `∇*∇ f(x) = Σ_i (2 f(x) − f(x + e_i) − f(x − e_i))`. -/
def latticeLaplacian (f : Site d → ℝ) (x : Site d) : ℝ :=
  ∑ i : Fin d, (2 * f x - f (x + unit i) - f (x - unit i))

/-- The mixed second difference
`∇_i∇_j f(x) = f(x + e_i + e_j) − f(x + e_i) − f(x + e_j) + f(x)`. -/
def secondDiff (f : Site d → ℝ) (i j : Fin d) (x : Site d) : ℝ :=
  f (x + unit i + unit j) - f (x + unit i) - f (x + unit j) + f x

end

end LatticeHC
