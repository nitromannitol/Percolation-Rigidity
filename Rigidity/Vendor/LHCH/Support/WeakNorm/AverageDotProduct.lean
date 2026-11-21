/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/AverageDotProduct.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Mathlib

/-!
# Averages of dot products over the children of a cube

One step of the telescoping identity behind the duality of the multiscale seminorms: the average of
the products of the children's block means, minus the product of their averages, is the average of
`(F y − F̄)·G y`; and the Cauchy–Schwarz inequality for averages of dot products.
-/

open Matrix

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- A sum of dot products over a finset is a single sum over the product of the finset with the
coordinates. -/
theorem sum_dotProduct_eq_sum_product {ι : Type*} {n : ℕ} (s : Finset ι) (X Y : ι → Fin n → ℝ) :
    ∑ y ∈ s, X y ⬝ᵥ Y y = ∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin n)), X p.1 p.2 * Y p.1 p.2 := by
  rw [Finset.sum_product]
  rfl

/-- A sum of dot products of a family with itself is nonnegative. -/
theorem sum_dotProduct_self_nonneg {ι : Type*} {n : ℕ} (s : Finset ι) (X : ι → Fin n → ℝ) :
    0 ≤ ∑ y ∈ s, X y ⬝ᵥ X y :=
  Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun i _ => mul_self_nonneg (X y i)

/-- **Cauchy–Schwarz for sums of dot products**, in squared form. -/
theorem sq_sum_dotProduct_le {ι : Type*} {n : ℕ} (s : Finset ι) (X Y : ι → Fin n → ℝ) :
    (∑ y ∈ s, X y ⬝ᵥ Y y) ^ 2 ≤ (∑ y ∈ s, X y ⬝ᵥ X y) * ∑ y ∈ s, Y y ⬝ᵥ Y y := by
  have hXX : ∑ y ∈ s, X y ⬝ᵥ X y = ∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin n)), X p.1 p.2 ^ 2 := by
    rw [sum_dotProduct_eq_sum_product]
    exact Finset.sum_congr rfl fun p _ => (sq _).symm
  have hYY : ∑ y ∈ s, Y y ⬝ᵥ Y y = ∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin n)), Y p.1 p.2 ^ 2 := by
    rw [sum_dotProduct_eq_sum_product]
    exact Finset.sum_congr rfl fun p _ => (sq _).symm
  rw [hXX, hYY, sum_dotProduct_eq_sum_product]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ (fun p : ι × Fin n => X p.1 p.2)
    (fun p : ι × Fin n => Y p.1 p.2)

/-- **One step of the telescoping identity over scales.** If `Ḡ` and `F̄` are the averages of the
children's means `G y` and `F y`, then the average of the products minus the product of the
averages is the average of `(F y − F̄) · G y`. -/
theorem avg_dotProduct_sub_dotProduct_avg {ι : Type*} {n : ℕ} (s : Finset ι)
    (F G : ι → Fin n → ℝ) :
    (s.card : ℝ)⁻¹ * ∑ y ∈ s, F y ⬝ᵥ G y -
        ((s.card : ℝ)⁻¹ • ∑ y ∈ s, F y) ⬝ᵥ ((s.card : ℝ)⁻¹ • ∑ y ∈ s, G y) =
      (s.card : ℝ)⁻¹ * ∑ y ∈ s, (F y - (s.card : ℝ)⁻¹ • ∑ y' ∈ s, F y') ⬝ᵥ G y := by
  simp only [sub_dotProduct, Finset.sum_sub_distrib, ← dotProduct_sum, dotProduct_smul,
    smul_eq_mul]
  ring

/-- **Cauchy–Schwarz for averages of dot products**:
`|avg_y X y · Y y| ≤ (avg_y X y · X y)^{1/2} (avg_y Y y · Y y)^{1/2}`. -/
theorem abs_avg_dotProduct_le {ι : Type*} {n : ℕ} (s : Finset ι) (X Y : ι → Fin n → ℝ) :
    |(s.card : ℝ)⁻¹ * ∑ y ∈ s, X y ⬝ᵥ Y y| ≤
      Real.sqrt ((s.card : ℝ)⁻¹ * ∑ y ∈ s, X y ⬝ᵥ X y) *
        Real.sqrt ((s.card : ℝ)⁻¹ * ∑ y ∈ s, Y y ⬝ᵥ Y y) := by
  have hN : 0 ≤ (s.card : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  rw [← Real.sqrt_mul (mul_nonneg hN (sum_dotProduct_self_nonneg s X))]
  refine Real.abs_le_sqrt ?_
  calc ((s.card : ℝ)⁻¹ * ∑ y ∈ s, X y ⬝ᵥ Y y) ^ 2
      = ((s.card : ℝ)⁻¹) ^ 2 * (∑ y ∈ s, X y ⬝ᵥ Y y) ^ 2 := mul_pow _ _ _
    _ ≤ ((s.card : ℝ)⁻¹) ^ 2 * ((∑ y ∈ s, X y ⬝ᵥ X y) * ∑ y ∈ s, Y y ⬝ᵥ Y y) :=
        mul_le_mul_of_nonneg_left (sq_sum_dotProduct_le s X Y) (sq_nonneg _)
    _ = ((s.card : ℝ)⁻¹ * ∑ y ∈ s, X y ⬝ᵥ X y) * ((s.card : ℝ)⁻¹ * ∑ y ∈ s, Y y ⬝ᵥ Y y) := by
        ring

end LatticeHC

end
