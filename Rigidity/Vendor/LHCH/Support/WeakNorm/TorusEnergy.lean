/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/TorusEnergy.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusParts
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusPoincare

/-!
# The energy of the Neumann solution on the torus

If `∇*∇ w = u` on the torus with `u` of mean zero, then `Σ|∇w|² ≤ C(d) (2N)² Σ u²` — summation
by parts gives `Σ|∇w|² = Σ (w − w̄) u`, and Cauchy–Schwarz with the Poincaré inequality on the
period box closes it.
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- **The energy of the torus solution**: there is `C(d)` such that if `u`, `w` have period `2N`,
`u` has mean zero and `∇*∇ w = u`, then `Σ_x Σ_i (∇_i w)² ≤ C (2N)² Σ_x u²` over the period box
(summation by parts gives `Σ|∇w|² = Σ u (w − w̄)`, then Cauchy–Schwarz and the Poincaré
inequality on the period box). -/
theorem exists_sum_grad_sq_le_of_latticeLaplacian_eq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ u w : Site d → ℝ, IsTorusPeriodic N u →
      IsTorusPeriodic N w → ∑ x ∈ torusBox d N, u x = 0 → (∀ x, latticeLaplacian w x = u x) →
        ∑ x ∈ torusBox d N, ∑ i : Fin d, (w (x + unit i) - w x) ^ 2 ≤
          C * (2 * (N : ℝ)) ^ 2 * ∑ x ∈ torusBox d N, u x ^ 2 := by
  obtain ⟨C, hC, hpoinc⟩ := exists_sum_torusBox_sq_sub_avg_le (d := d)
  refine ⟨C, hC, fun N hN u w hu hw hmean hlap => ?_⟩
  set E : ℝ := ∑ x ∈ torusBox d N, ∑ i : Fin d, (w (x + unit i) - w x) ^ 2 with hE
  set m : ℝ := ((torusBox d N).card : ℝ)⁻¹ * ∑ y ∈ torusBox d N, w y with hm
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hU0 : 0 ≤ ∑ x ∈ torusBox d N, u x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hparts := sum_mul_latticeLaplacian_eq N hN w w hw hw
  have hEeq : E = ∑ x ∈ torusBox d N, w x * u x := by
    simp only [hE, sq]
    rw [← hparts]
    exact Finset.sum_congr rfl fun x _ => by rw [hlap x]
  have hcenter : E = ∑ x ∈ torusBox d N, (w x - m) * u x := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hmean, mul_zero, sub_zero]
    exact hEeq
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (torusBox d N) (fun x => w x - m) u
  have hP := hpoinc N hN w
  have hsq : E * E ≤ E * (C * (2 * (N : ℝ)) ^ 2 * ∑ x ∈ torusBox d N, u x ^ 2) := by
    calc E * E = (∑ x ∈ torusBox d N, (w x - m) * u x) ^ 2 := by rw [sq, ← hcenter]
      _ ≤ (∑ x ∈ torusBox d N, (w x - m) ^ 2) * ∑ x ∈ torusBox d N, u x ^ 2 := hCS
      _ ≤ (C * (2 * (N : ℝ)) ^ 2 * E) * ∑ x ∈ torusBox d N, u x ^ 2 :=
          mul_le_mul_of_nonneg_right hP hU0
      _ = E * (C * (2 * (N : ℝ)) ^ 2 * ∑ x ∈ torusBox d N, u x ^ 2) := by ring
  rcases hE0.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · exact le_of_mul_le_mul_left hsq hpos

end LatticeHC

end
