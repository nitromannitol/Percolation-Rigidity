/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/Analysis/CauchySchwarz.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Mathlib

/-!
# Weighted Cauchy–Schwarz inequalities

The weighted Cauchy–Schwarz bound `(Σ_i a_i u_i h_i)² ≤ (Σ_i a_i u_i²)(Σ_i a_i h_i²)` for
nonnegative weights `a`, and its two specialisations `u ≡ 1` (with and without `Σ_i a_i = 1`) and
`h = √b`. They are used by the coarse-graining and cutoff estimates in `Support/WeakNorm` and
`Support/TwoScale`.
-/

namespace LatticeHC

/-- **Cauchy–Schwarz for a weighted average**: for weights `a ≥ 0`, the square of the weighted
average of a product is at most the product of the weighted averages of the squares. -/
theorem sq_sum_mul_mul_le {α : Type*} (s : Finset α) (a u h : α → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i * (u i * h i)) ^ 2 ≤ (∑ i ∈ s, a i * u i ^ 2) * ∑ i ∈ s, a i * h i ^ 2 := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (a i) * u i)
    (fun i => Real.sqrt (a i) * h i)
  have e1 : ∀ i ∈ s, Real.sqrt (a i) * u i * (Real.sqrt (a i) * h i) = a i * (u i * h i) := by
    intro i hi
    have := Real.mul_self_sqrt (ha i hi)
    calc _ = (Real.sqrt (a i) * Real.sqrt (a i)) * (u i * h i) := by ring
      _ = _ := by rw [this]
  have e2 : ∀ i ∈ s, (Real.sqrt (a i) * u i) ^ 2 = a i * u i ^ 2 := by
    intro i hi
    rw [mul_pow, Real.sq_sqrt (ha i hi)]
  have e3 : ∀ i ∈ s, (Real.sqrt (a i) * h i) ^ 2 = a i * h i ^ 2 := by
    intro i hi
    rw [mul_pow, Real.sq_sqrt (ha i hi)]
  rwa [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at key

/-- The general bound with `u ≡ 1`: `(Σ a_i X_i)² ≤ (Σ a_i)(Σ a_i X_i²)` for `a ≥ 0`. -/
theorem sq_sum_mul_le_sum_mul_sum_sq_mul {ι : Type*} (s : Finset ι) (a X : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i * X i) ^ 2 ≤ (∑ i ∈ s, a i) * ∑ i ∈ s, a i * X i ^ 2 := by
  simpa using sq_sum_mul_mul_le s a (fun _ => 1) X ha

/-- The general bound with `h = √b`: `(Σ w_i √b_i)² ≤ (Σ w_i)(Σ w_i b_i)` for `w, b ≥ 0`. -/
theorem sq_sum_mul_sqrt_le {ι : Type*} (s : Finset ι) (w b : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hb : ∀ i, 0 ≤ b i) :
    (∑ i ∈ s, w i * Real.sqrt (b i)) ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * b i := by
  have h := sq_sum_mul_le_sum_mul_sum_sq_mul s w (fun i => Real.sqrt (b i)) (fun i _ => hw i)
  simpa only [Real.sq_sqrt (hb _)] using h

/-- Jensen for a weighted average: for weights `a ≥ 0` with sum one,
`(Σ a_i h_i)² ≤ Σ a_i h_i²`. -/
theorem sq_sum_mul_le_sum_mul_sq {α : Type*} (s : Finset α) (a h : α → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (h1 : ∑ i ∈ s, a i = 1) :
    (∑ i ∈ s, a i * h i) ^ 2 ≤ ∑ i ∈ s, a i * h i ^ 2 := by
  calc (∑ i ∈ s, a i * h i) ^ 2 ≤ (∑ i ∈ s, a i) * ∑ i ∈ s, a i * h i ^ 2 :=
        sq_sum_mul_le_sum_mul_sum_sq_mul s a h ha
    _ = ∑ i ∈ s, a i * h i ^ 2 := by rw [h1, one_mul]

end LatticeHC
