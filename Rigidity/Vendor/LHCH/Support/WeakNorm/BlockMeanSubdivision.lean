/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/BlockMeanSubdivision.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.Lattice.Subdivision
import Rigidity.Vendor.LHCH.Support.WeakNorm.BlockMean

/-!
# Block means average under subdivision

The block mean of an edge field on `Z + {0, …, mN}^d` is the average of its block means on the `N^d`
children `Z + m y + {0, …, m}^d`, because the face weights add under subdivision.
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- The coordinate-`j` face-weighted sum over the edges of a cube is the unfiltered weighted sum of
the field cut off to the edges parallel to `e_j`. -/
theorem sum_weighted_edgesOf_filter_direction (z : Site d) (L : ℕ) (j : Fin d)
    (F : Edge d → ℝ) :
    ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * F e =
      ∑ e ∈ edgesOf z L, faceWeight z L e * (if e.2 = j then F e else 0) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

/-- **Block means average under subdivision**: the block mean of `F` on `Z + {0, …, mN}^d` is the
average of its block means on the `N^d` children `Z + m y + {0, …, m}^d`, because the face weights
add (`sum_weighted_edgesOf_children`) and `(mN)^{-d} = N^{-d} m^{-d}`. -/
theorem blockMean_eq_avg_children (Z : Site d) (m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (F : Edge d → ℝ) :
    blockMean Z (m * N) F = ((N : ℝ) ^ d)⁻¹ •
      ∑ y ∈ Fintype.piFinset (fun _ : Fin d => Finset.range N),
        blockMean (Z + fun i => (m : ℤ) * (y i : ℤ)) m F := by
  funext j
  have key := sum_weighted_edgesOf_children Z m N hm hN (fun e => if e.2 = j then F e else 0)
  simp only [blockMean, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    sum_weighted_edgesOf_filter_direction, key]
  rw [Nat.cast_mul, mul_pow, mul_inv, ← Finset.mul_sum]
  ring

end LatticeHC

end
