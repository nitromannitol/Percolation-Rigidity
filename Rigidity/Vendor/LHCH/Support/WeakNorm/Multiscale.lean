/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/Multiscale.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.WeakNorm.BlockMean

/-!
# Multiscale block quantities on a triadic cube

The quantities of the multiscale seminorms (AK25 §2, Appendix A, on the lattice). The triadic cube
`Z + {0, …, 3^n}^d` has, at scale `k ≤ n`, the `3^{d(n−k)}` children
`Z + 3^k y + {0, …, 3^k}^d`, `y ∈ {0, …, 3^{n−k} − 1}^d`. For edge fields `F`, `G`:
* `cubeAvg z L f` is the face-weighted average `L^{-d} Σ_{e ⊂ □} w_□(e) f(e)`;
* `blockSq Z n k G` is the average over the children at scale `k` of `|(G)_□'|²`;
* `blockOsc Z n k F` is the average over the children `□''` at scale `k` of `|(F)_□'' − (F)_□'|²`,
  where `□'` is the parent of `□''` at scale `k + 1`;
* `blockPair Z n k F G` is the average over the children at scale `k` of `(F)_□'·(G)_□'`.
No property is proved here.
-/

namespace LatticeHC

open LatticeProb Matrix

noncomputable section

variable {d : ℕ}

/-- The face-weighted average `L^{-d} Σ_{e ⊂ □} w_□(e) f(e)` of an edge function on
`□ = z + {0, …, L}^d`. -/
def cubeAvg (z : Site d) (L : ℕ) (f : Edge d → ℝ) : ℝ :=
  ((L : ℝ) ^ d)⁻¹ * ∑ e ∈ edgesOf z L, faceWeight z L e * f e

/-- The index set `{0, …, 3^j − 1}^d` of the `3^{dj}` subcubes of side `3^k` of a cube of side
`3^{k+j}`. -/
def triadicIndex (d j : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun _ : Fin d => Finset.range (3 ^ j)

/-- The corner `Z + 3^k y` of the subcube of side `3^k` with index `y`. -/
def triadicCorner (Z : Site d) (k : ℕ) (y : Fin d → ℕ) : Site d :=
  Z + fun i => ((3 ^ k : ℕ) : ℤ) * (y i : ℤ)

/-- `blockPair Z n k F G`: the average over the children `□'` at scale `k` of
`Z + {0, …, 3^n}^d` of `(F)_□' · (G)_□'`. -/
def blockPair (Z : Site d) (n k : ℕ) (F G : Edge d → ℝ) : ℝ :=
  ((triadicIndex d (n - k)).card : ℝ)⁻¹ * ∑ y ∈ triadicIndex d (n - k),
    blockMean (triadicCorner Z k y) (3 ^ k) F ⬝ᵥ blockMean (triadicCorner Z k y) (3 ^ k) G

/-- `blockSq Z n k G = blockPair Z n k G G`, the mean square of the block means at scale `k`. -/
def blockSq (Z : Site d) (n k : ℕ) (G : Edge d → ℝ) : ℝ := blockPair Z n k G G

/-- `blockOsc Z n k F`: the average over the children `□'` at scale `k + 1` of `Z + {0, …, 3^n}^d`
of the average over their children `□''` at scale `k` of `|(F)_□'' − (F)_□'|²`. -/
def blockOsc (Z : Site d) (n k : ℕ) (F : Edge d → ℝ) : ℝ :=
  ((triadicIndex d (n - (k + 1))).card : ℝ)⁻¹ * ∑ y ∈ triadicIndex d (n - (k + 1)),
    ((triadicIndex d 1).card : ℝ)⁻¹ * ∑ y' ∈ triadicIndex d 1,
      (blockMean (triadicCorner (triadicCorner Z (k + 1) y) k y') (3 ^ k) F -
          blockMean (triadicCorner Z (k + 1) y) (3 ^ (k + 1)) F) ⬝ᵥ
        (blockMean (triadicCorner (triadicCorner Z (k + 1) y) k y') (3 ^ k) F -
          blockMean (triadicCorner Z (k + 1) y) (3 ^ (k + 1)) F)

end

end LatticeHC
