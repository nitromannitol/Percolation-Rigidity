/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/TorusParts.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusH2

/-!
# Summation by parts on the torus

For functions of period `2N`, `Σ_x u ∇*∇w = Σ_x Σ_i ∇_i u ∇_i w` over the period box, from the
translation invariance of sums over the box.
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- **One direction of the summation by parts**: for `u`, `w` of period `2N` and a vector `v`,
`Σ_x u(x) (2 w(x) − w(x + v) − w(x − v)) = Σ_x (u(x + v) − u(x)) (w(x + v) − w(x))`. -/
theorem sum_mul_second_difference_eq_sum_mul_difference (N : ℕ) (hN : 0 < N) (u w : Site d → ℝ)
    (hu : IsTorusPeriodic N u) (hw : IsTorusPeriodic N w) (v : Site d) :
    ∑ x ∈ torusBox d N, u x * (2 * w x - w (x + v) - w (x - v)) =
      ∑ x ∈ torusBox d N, (u (x + v) - u x) * (w (x + v) - w x) := by
  have hper : IsTorusPeriodic N (fun y => u y * (w y - w (y - v))) := by
    intro x i
    have h : x + (2 * (N : ℤ)) • unit i - v = (x - v) + (2 * (N : ℤ)) • unit i := by abel
    simp only [h, hu x i, hw x i, hw (x - v) i]
  have hshift := sum_torusBox_add N hN _ hper v
  simp only [add_sub_cancel_right] at hshift
  have hsplit : ∑ x ∈ torusBox d N, u x * (2 * w x - w (x + v) - w (x - v)) =
      ∑ x ∈ torusBox d N, u x * (w x - w (x + v)) +
        ∑ x ∈ torusBox d N, u x * (w x - w (x - v)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hsplit, ← hshift, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **Summation by parts on the torus**: for `u`, `w` of period `2N`,
`Σ_x u(x) ∇*∇w(x) = Σ_x Σ_i (u(x + e_i) − u(x)) (w(x + e_i) − w(x))`, the sums over the period
box. -/
theorem sum_mul_latticeLaplacian_eq (N : ℕ) (hN : 0 < N) (u w : Site d → ℝ)
    (hu : IsTorusPeriodic N u) (hw : IsTorusPeriodic N w) :
    ∑ x ∈ torusBox d N, u x * latticeLaplacian w x =
      ∑ x ∈ torusBox d N, ∑ i : Fin d, (u (x + unit i) - u x) * (w (x + unit i) - w x) := by
  have hL : ∀ x, u x * latticeLaplacian w x = ∑ i : Fin d,
      u x * (2 * w x - w (x + unit i) - w (x - unit i)) := fun x => by
    rw [latticeLaplacian, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => hL x, Finset.sum_comm, Finset.sum_comm (s := torusBox d N)]
  exact Finset.sum_congr rfl fun i _ =>
    sum_mul_second_difference_eq_sum_mul_difference N hN u w hu hw (unit i)

end LatticeHC

end
