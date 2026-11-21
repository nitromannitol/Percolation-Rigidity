/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/UnitScale.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.Lattice.Subdivision
import Rigidity.Vendor.LHCH.Support.WeakNorm.Multiscale

/-!
# Face-weighted averages at the unit scale

The face-weighted average of an edge function on a triadic cube is the average over its unit
subcubes of their face-weighted averages, and at the top scale the triadic cube is its own only
child.
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- **Face-weighted averages are averages over the unit cells.** The face-weighted average of `f`
on `Z + {0, …, 3^n}^d` is the average over its `3^{dn}` unit subcubes of their face-weighted
averages (`sum_weighted_edgesOf_children` with `m = 1`, `N = 3^n`). -/
theorem cubeAvg_eq_avg_unit (Z : Site d) (n : ℕ) (f : Edge d → ℝ) :
    cubeAvg Z (3 ^ n) f = ((triadicIndex d n).card : ℝ)⁻¹ *
      ∑ y ∈ triadicIndex d n, cubeAvg (triadicCorner Z 0 y) 1 f := by
  have key := sum_weighted_edgesOf_children Z 1 (3 ^ n) le_rfl (Nat.one_le_pow _ _ (by norm_num)) f
  rw [one_mul] at key
  have hcorner : ∀ y : Fin d → ℕ,
      triadicCorner Z 0 y = Z + fun i => ((1 : ℕ) : ℤ) * (y i : ℤ) := by
    intro y
    simp [triadicCorner]
  have hcard : ((triadicIndex d n).card : ℝ) = ((3 ^ n : ℕ) : ℝ) ^ d := by
    simp [triadicIndex, Fintype.card_piFinset]
  have hunit : ∀ y : Fin d → ℕ, cubeAvg (triadicCorner Z 0 y) 1 f =
      ∑ e ∈ edgesOf (Z + fun i => ((1 : ℕ) : ℤ) * (y i : ℤ)) 1,
        faceWeight (Z + fun i => ((1 : ℕ) : ℤ) * (y i : ℤ)) 1 e * f e := by
    intro y
    rw [hcorner]
    simp [cubeAvg]
  rw [Finset.sum_congr rfl (fun y _ => hunit y), hcard]
  rw [triadicIndex, ← key]
  simp [cubeAvg]

/-- At scale `n` the triadic cube is its own only child: `blockPair Z n n F G = (F)_□ · (G)_□`. -/
theorem blockPair_self (Z : Site d) (n : ℕ) (F G : Edge d → ℝ) :
    blockPair Z n n F G = blockMean Z (3 ^ n) F ⬝ᵥ blockMean Z (3 ^ n) G := by
  have hidx : triadicIndex d (n - n) = {fun _ => 0} := by
    ext y
    simp [triadicIndex, funext_iff]
  have hcorner : triadicCorner Z n (fun _ => 0) = Z := by
    funext i
    simp [triadicCorner]
  rw [blockPair, hidx, Finset.sum_singleton, hcorner]
  simp

end LatticeHC

end
