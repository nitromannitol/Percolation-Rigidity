/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/MultiscaleDuality.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.WeakNorm.AverageDotProduct
import Rigidity.Vendor.LHCH.Support.WeakNorm.BlockMeanSubdivision
import Rigidity.Vendor.LHCH.Support.WeakNorm.Multiscale
import Rigidity.Vendor.LHCH.Support.WeakNorm.TriadicRegroup
import Rigidity.Vendor.LHCH.Support.WeakNorm.UnitScale

/-!
# The multiscale duality bound

The face-weighted pairing of two edge fields on a triadic cube differs from the product of their
block means by at most a unit-scale term plus `Σ_{k<n} blockOsc_k(F)^{1/2} blockSq_k(G)^{1/2}`:
between consecutive scales the average of the products of block means changes by the average of
`((F)_□'' − (F)_□')·(G)_□''` (face weights add), which Cauchy–Schwarz bounds. This is the lattice
form of the duality between AK25's `B^{1/2}_{2,∞}` and `B^{-1/2}_{2,1}` seminorms.
-/

open LatticeProb Matrix

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- The average over a product of finsets is the iterated average. -/
theorem avg_product_eq_avg_avg {α β : Type*} (A : Finset α) (B : Finset β) (f : α × β → ℝ) :
    (((A ×ˢ B).card : ℕ) : ℝ)⁻¹ * ∑ p ∈ A ×ˢ B, f p =
      (A.card : ℝ)⁻¹ * ∑ a ∈ A, (B.card : ℝ)⁻¹ * ∑ b ∈ B, f (a, b) := by
  rw [Finset.sum_product, Finset.card_product, Nat.cast_mul, mul_inv, mul_assoc]
  congr 1
  rw [Finset.mul_sum]

/-- The block mean on a triadic cube of side `3^{k+1}` is the average of the block means of its
`3^d` children of side `3^k`. -/
theorem blockMean_succ_eq_avg_children (Z : Site d) (k : ℕ) (F : Edge d → ℝ) :
    blockMean Z (3 ^ (k + 1)) F = ((triadicIndex d 1).card : ℝ)⁻¹ •
      ∑ y ∈ triadicIndex d 1, blockMean (triadicCorner Z k y) (3 ^ k) F := by
  have h := blockMean_eq_avg_children Z (3 ^ k) 3 (Nat.one_le_pow _ _ (by norm_num))
    (by norm_num) F
  rw [← pow_succ] at h
  rw [h]
  have hcard : ((triadicIndex d 1).card : ℝ) = ((3 : ℕ) : ℝ) ^ d := by
    simp [triadicIndex, Fintype.card_piFinset]
  rw [hcard]
  rfl

/-- The average over the children at scale `k` of `Z + {0, …, 3^n}^d`, regrouped as an average
over the pairs (parent at scale `k + 1`, child of that parent). -/
theorem blockPair_eq_avg_product (Z : Site d) {n k : ℕ} (hkn : k < n) (F G : Edge d → ℝ) :
    blockPair Z n k F G =
      (((triadicIndex d (n - (k + 1)) ×ˢ triadicIndex d 1).card : ℕ) : ℝ)⁻¹ *
        ∑ p ∈ triadicIndex d (n - (k + 1)) ×ˢ triadicIndex d 1,
          blockMean (triadicCorner (triadicCorner Z (k + 1) p.1) k p.2) (3 ^ k) F ⬝ᵥ
            blockMean (triadicCorner (triadicCorner Z (k + 1) p.1) k p.2) (3 ^ k) G := by
  rw [blockPair, sum_triadicIndex_regroup Z hkn
    (fun Z' => blockMean Z' (3 ^ k) F ⬝ᵥ blockMean Z' (3 ^ k) G), card_triadicIndex_succ hkn,
    Finset.card_product, Finset.sum_product]

/-- **One step of the multiscale telescoping**: for
`k < n`, the change of the average of `(F)_□'·(G)_□'` from scale `k + 1` to scale `k` is the
average over the children `□''` at scale `k` of `((F)_□'' − (F)_□')·(G)_□''`, which by
Cauchy–Schwarz is at most `blockOsc^{1/2} · blockSq^{1/2}`. -/
theorem abs_blockPair_sub_succ_le (Z : Site d) {n k : ℕ} (hkn : k < n) (F G : Edge d → ℝ) :
    |blockPair Z n k F G - blockPair Z n (k + 1) F G| ≤
      Real.sqrt (blockOsc Z n k F) * Real.sqrt (blockSq Z n k G) := by
  have hF : ∀ y, blockMean (triadicCorner Z (k + 1) y) (3 ^ (k + 1)) F =
      ((triadicIndex d 1).card : ℝ)⁻¹ • ∑ y' ∈ triadicIndex d 1,
        blockMean (triadicCorner (triadicCorner Z (k + 1) y) k y') (3 ^ k) F :=
    fun y => blockMean_succ_eq_avg_children _ k F
  have hG : ∀ y, blockMean (triadicCorner Z (k + 1) y) (3 ^ (k + 1)) G =
      ((triadicIndex d 1).card : ℝ)⁻¹ • ∑ y' ∈ triadicIndex d 1,
        blockMean (triadicCorner (triadicCorner Z (k + 1) y) k y') (3 ^ k) G :=
    fun y => blockMean_succ_eq_avg_children _ k G
  have hdiff : blockPair Z n k F G - blockPair Z n (k + 1) F G =
      (((triadicIndex d (n - (k + 1)) ×ˢ triadicIndex d 1).card : ℕ) : ℝ)⁻¹ *
        ∑ p ∈ triadicIndex d (n - (k + 1)) ×ˢ triadicIndex d 1,
          (blockMean (triadicCorner (triadicCorner Z (k + 1) p.1) k p.2) (3 ^ k) F -
              blockMean (triadicCorner Z (k + 1) p.1) (3 ^ (k + 1)) F) ⬝ᵥ
            blockMean (triadicCorner (triadicCorner Z (k + 1) p.1) k p.2) (3 ^ k) G := by
    rw [blockPair_eq_avg_product Z hkn, avg_product_eq_avg_avg, avg_product_eq_avg_avg,
      blockPair, ← mul_sub, ← Finset.sum_sub_distrib]
    dsimp only
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hF y, hG y]
    exact avg_dotProduct_sub_dotProduct_avg (triadicIndex d 1) _ _
  rw [hdiff]
  refine (abs_avg_dotProduct_le _ _ _).trans_eq ?_
  rw [blockOsc, blockSq, blockPair_eq_avg_product Z hkn, avg_product_eq_avg_avg,
    avg_product_eq_avg_avg]

/-- **The multiscale duality bound**: the face-weighted pairing of `F` and `G` on
`Z + {0, …, 3^n}^d` differs from the product of their block means by at most the unit-scale term
plus `Σ_{k<n} blockOsc_k(F)^{1/2} blockSq_k(G)^{1/2}`. -/
theorem abs_cubeAvg_mul_sub_le (Z : Site d) (n : ℕ) (F G : Edge d → ℝ) :
    |cubeAvg Z (3 ^ n) (fun e => F e * G e) -
        blockMean Z (3 ^ n) F ⬝ᵥ blockMean Z (3 ^ n) G| ≤
      |((triadicIndex d n).card : ℝ)⁻¹ * ∑ y ∈ triadicIndex d n,
          (cubeAvg (triadicCorner Z 0 y) 1 (fun e => F e * G e) -
            blockMean (triadicCorner Z 0 y) 1 F ⬝ᵥ blockMean (triadicCorner Z 0 y) 1 G)| +
        ∑ k ∈ Finset.range n, Real.sqrt (blockOsc Z n k F) * Real.sqrt (blockSq Z n k G) := by
  have hunit : ((triadicIndex d n).card : ℝ)⁻¹ * ∑ y ∈ triadicIndex d n,
      (cubeAvg (triadicCorner Z 0 y) 1 (fun e => F e * G e) -
        blockMean (triadicCorner Z 0 y) 1 F ⬝ᵥ blockMean (triadicCorner Z 0 y) 1 G) =
      cubeAvg Z (3 ^ n) (fun e => F e * G e) - blockPair Z n 0 F G := by
    rw [cubeAvg_eq_avg_unit, blockPair, Finset.sum_sub_distrib, mul_sub]
    rfl
  have htel : blockPair Z n 0 F G - blockPair Z n n F G =
      ∑ k ∈ Finset.range n, (blockPair Z n k F G - blockPair Z n (k + 1) F G) :=
    (Finset.sum_range_sub' (fun k => blockPair Z n k F G) n).symm
  have hsplit : cubeAvg Z (3 ^ n) (fun e => F e * G e) -
        blockMean Z (3 ^ n) F ⬝ᵥ blockMean Z (3 ^ n) G =
      ((triadicIndex d n).card : ℝ)⁻¹ * ∑ y ∈ triadicIndex d n,
        (cubeAvg (triadicCorner Z 0 y) 1 (fun e => F e * G e) -
          blockMean (triadicCorner Z 0 y) 1 F ⬝ᵥ blockMean (triadicCorner Z 0 y) 1 G) +
        ∑ k ∈ Finset.range n, (blockPair Z n k F G - blockPair Z n (k + 1) F G) := by
    rw [hunit, ← htel, blockPair_self]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  exact abs_blockPair_sub_succ_le Z (Finset.mem_range.1 hk) F G

end LatticeHC

end
