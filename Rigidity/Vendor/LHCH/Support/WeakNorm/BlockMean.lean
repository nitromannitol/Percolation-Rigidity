/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/BlockMean.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Coarse

/-!
# Face-weighted block means of edge fields

The vocabulary of the multiscale seminorms (AK25 §2 and Appendix A on the lattice). The block mean
of an edge field `F` on the lattice cube `z + {0, …, L}^d` is the vector whose `j`th coordinate is
the face-weighted average `L^{-d} Σ_{e ⊂ □, e ∥ e_j} w_□(e) F(e)`. For a gradient field it is the
mean gradient `𝒢_□` of (e:energy), and for the flux `c∇u` it is the mean flux of Step 1 of
`p:finite-range`. No property is proved here.
-/

namespace LatticeHC

open LatticeProb

noncomputable section

variable {d : ℕ}

/-- The face-weighted block mean `(F)_□ ∈ ℝ^d` of an edge field `F` on `□ = z + {0, …, L}^d`:
`(F)_□ · e_j = L^{-d} Σ_{e ⊂ □, e ∥ e_j} w_□(e) F(e)`. -/
def blockMean (z : Site d) (L : ℕ) (F : Edge d → ℝ) : Fin d → ℝ := fun j =>
  ((L : ℝ) ^ d)⁻¹ * ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * F e

/-- The block mean of the gradient of `u` is the mean gradient `𝒢_□(u)` of (e:energy). -/
theorem blockMean_grad (z : Site d) (L : ℕ) (u : Site d → ℝ) :
    blockMean z L (fun e => u e.tgt - u e.src) = cubeMeanGrad z L u := rfl

end

end LatticeHC
