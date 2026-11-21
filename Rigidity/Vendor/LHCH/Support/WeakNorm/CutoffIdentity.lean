/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/CutoffIdentity.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.TwoScale.DirichletProblem

/-!
# The cutoff identity

For `φ` harmonic on a finite set and a
cutoff `ψ` vanishing off it, the `ψ`-weighted energy of `φ` equals minus the pairing of `(φ − m)∇ψ`
with the flux `c∇φ`, by summation by parts of `ψ(φ − m) L_cφ = 0` and the discrete product rule.
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- **The cutoff identity**: if `φ` is
`c`-harmonic on a finite set `U`, `ψ` vanishes off `U`, `m` is a constant and `S` contains every
`x` with `x ∈ U` or `x + e_j ∈ U`, then
`Σ_{x∈S} Σ_j ψ(x + e_j) c(x,j) (∇_jφ(x))² = −Σ_{x∈S} Σ_j (φ(x) − m) ∇_jψ(x) c(x,j) ∇_jφ(x)`:
sum `ψ(φ − m) L_cφ = 0` by parts and use the discrete product rule. -/
theorem sum_cutoff_energy_eq (c : Edge d → ℝ) (U S : Finset (Site d)) (φ ψ : Site d → ℝ)
    (m : ℝ) (hφ : ∀ x ∈ U, condLaplacian c φ x = 0) (hψ : ∀ x, x ∉ U → ψ x = 0)
    (hS : ∀ x (j : Fin d), (x ∈ U ∨ x + unit j ∈ U) → x ∈ S) :
    ∑ x ∈ S, ∑ j : Fin d, ψ (x + unit j) * c (x, j) * (φ (x + unit j) - φ x) ^ 2 =
      -∑ x ∈ S, ∑ j : Fin d,
        (φ x - m) * (ψ (x + unit j) - ψ x) * (c (x, j) * (φ (x + unit j) - φ x)) := by
  classical
  have hu : ∀ x, x ∉ U → ψ x * (φ x - m) = 0 := fun x hx => by rw [hψ x hx, zero_mul]
  have key := sum_mul_condLaplacian_eq_sum_gradient_mul c U S (fun x => ψ x * (φ x - m)) φ hu hS
  rw [Finset.sum_eq_zero fun x hx => by rw [hφ x hx, mul_zero]] at key
  have hsplit : ∀ x (j : Fin d),
      c (x, j) * ((ψ (x + unit j) * (φ (x + unit j) - m) - ψ x * (φ x - m)) *
        (φ (x + unit j) - φ x)) =
      ψ (x + unit j) * c (x, j) * (φ (x + unit j) - φ x) ^ 2 +
        (φ x - m) * (ψ (x + unit j) - ψ x) * (c (x, j) * (φ (x + unit j) - φ x)) :=
    fun x j => by ring
  simp only [hsplit, Finset.sum_add_distrib] at key
  linarith

end LatticeHC

end
