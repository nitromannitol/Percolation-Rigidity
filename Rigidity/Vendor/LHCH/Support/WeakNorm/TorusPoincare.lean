/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/TorusPoincare.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.Analysis.CubePoincare
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusCalculus

/-!
# The Poincaré inequality on the period box

The period box `{0, …, 2N − 1}^d` is the lattice cube of side `2N − 1`, so the discrete Poincaré
inequality on cubes gives `Σ_x (w − w̄)² ≤ C(d) (2N)² Σ_x Σ_i (∇_i w)²` there.
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- The period box `{0, …, 2N − 1}^d` is the lattice cube of side `2N − 1` based at the origin. -/
theorem torusBox_eq_latticeCube (N : ℕ) (hN : 0 < N) :
    torusBox d N = latticeCube 0 (2 * N - 1) := by
  ext x
  rw [mem_latticeCube_iff_coord]
  simp only [torusBox, Fintype.mem_piFinset, Finset.mem_Ico, Pi.zero_apply]
  refine forall_congr' fun i => ?_
  push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * N)]
  omega

/-- **The Poincaré inequality on the period box**: there is `C(d)` such that for `N ≥ 1` and every
`w`, `Σ_x (w(x) − w̄)² ≤ C (2N)² Σ_x Σ_i (w(x + e_i) − w(x))²`, the sums over `{0, …, 2N − 1}^d`
and `w̄` the average there (the period box is the lattice cube of side `2N − 1`). -/
theorem exists_sum_torusBox_sq_sub_avg_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ w : Site d → ℝ,
      ∑ x ∈ torusBox d N, (w x - ((torusBox d N).card : ℝ)⁻¹ * ∑ y ∈ torusBox d N, w y) ^ 2 ≤
        C * (2 * (N : ℝ)) ^ 2 * ∑ x ∈ torusBox d N, ∑ i : Fin d, (w (x + unit i) - w x) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_sum_sq_sub_avg_le (d := d)
  refine ⟨C, hC, fun N hN w => ?_⟩
  rw [torusBox_eq_latticeCube N hN]
  refine (hbound 0 (2 * N - 1) w).trans ?_
  have hL : ((2 * N - 1 : ℕ) : ℝ) ^ 2 ≤ (2 * (N : ℝ)) ^ 2 := by
    have h : ((2 * N - 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      have h' : 2 * N - 1 ≤ 2 * N := Nat.sub_le _ _
      exact_mod_cast h'
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) h 2
  have hE : ∑ x ∈ latticeCube 0 (2 * N - 1), ∑ i : Fin d,
      (if x + unit i ∈ latticeCube 0 (2 * N - 1) then (w (x + unit i) - w x) ^ 2 else 0) ≤
        ∑ x ∈ latticeCube 0 (2 * N - 1), ∑ i : Fin d, (w (x + unit i) - w x) ^ 2 :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ => by
      split_ifs
      exacts [le_rfl, sq_nonneg _]
  have hE0 : 0 ≤ ∑ x ∈ latticeCube 0 (2 * N - 1), ∑ i : Fin d,
      (if x + unit i ∈ latticeCube 0 (2 * N - 1) then (w (x + unit i) - w x) ^ 2 else 0) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
  have hE1 : 0 ≤ ∑ x ∈ latticeCube 0 (2 * N - 1), ∑ i : Fin d, (w (x + unit i) - w x) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left hL hC) hE hE0 (by positivity)

end LatticeHC

end
