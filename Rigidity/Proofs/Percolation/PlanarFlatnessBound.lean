import Rigidity.Proofs.Percolation.PlanarFlatnessInputs

/-!
# The multiscale Poincaré inequality in the form of the proof of Lemma 5.8

For a function `w` on the lattice points of a triadic cube `□_m` of the plane, a slope `ξ` and
`n ∈ [m/2, m]`, the multiscale Poincaré inequality (Armstrong and Dario, Proposition A.2, in the
form `exists_multiscalePoincare_affine`) gives, after the triangle inequality on the gradient of
`w - ℓ_ξ` and the Cauchy–Schwarz inequality `(∑_k 3^k X_k^{1/2})² ≤ 3^m ∑_k 3^k X_k`,

`‖w - ℓ_ξ - (w - ℓ_ξ)_{□_m}‖²_{L̲²} ≤ C 3^{2n} (‖∇w‖²_{L̲²} + |ξ|²)
  + C 3^m ∑_{k=n}^{m-1} 3^k (|3^k ℤ² ∩ □_m|⁻¹ ∑_y | |□_k|⁻¹ ⟨∇w⟩_{y+□_k} - ξ |² + 3^{-2k} |ξ|²)`.

This is the first display of the proof of Lemma 5.8 of Armstrong and Dario, combined with the
inequality `(∑_k 3^k X_k^{1/2})² ≤ C 3^n ∑_k 3^k X_k` used there.
-/

open Rigidity.Proofs.Multiscale LatticeProb.Percolation

namespace Rigidity.Percolation

/-- The squared gradient of `w - ℓ_ξ` is at most twice that of `w` plus `2 |ξ|²`. -/
theorem gradNormSq_sub_affineFun_le (A : Finset (Vertex 2)) (w : Vertex 2 → ℝ) (ξ : Fin 2 → ℝ)
    (x : Vertex 2) :
    gradNormSq A (fun y => w y - affineFun ξ y) x ≤
      2 * gradNormSq A w x + 2 * (ξ 0 ^ 2 + ξ 1 ^ 2) := by
  have hp : ∀ i : Fin 2, affineFun ξ x - affineFun ξ (x + unitVec i) = -ξ i := fun i => by
    linarith [affineFun_add_unitVec ξ x i]
  have hm : ∀ i : Fin 2, affineFun ξ x - affineFun ξ (x - unitVec i) = ξ i := fun i => by
    have h := affineFun_add_unitVec ξ (x - unitVec i) i
    rw [sub_add_cancel] at h
    exact h
  have key : ∀ i : Fin 2,
      ((if x + unitVec i ∈ A then
          ((w x - affineFun ξ x) - (w (x + unitVec i) - affineFun ξ (x + unitVec i))) ^ 2
        else 0) +
        (if x - unitVec i ∈ A then
          ((w x - affineFun ξ x) - (w (x - unitVec i) - affineFun ξ (x - unitVec i))) ^ 2
        else 0)) ≤
      2 * ((if x + unitVec i ∈ A then (w x - w (x + unitVec i)) ^ 2 else 0) +
        (if x - unitVec i ∈ A then (w x - w (x - unitVec i)) ^ 2 else 0)) + 4 * ξ i ^ 2 := by
    intro i
    have e1 : (w x - affineFun ξ x) - (w (x + unitVec i) - affineFun ξ (x + unitVec i)) =
        (w x - w (x + unitVec i)) + ξ i := by linarith [hp i]
    have e2 : (w x - affineFun ξ x) - (w (x - unitVec i) - affineFun ξ (x - unitVec i)) =
        (w x - w (x - unitVec i)) - ξ i := by linarith [hm i]
    rw [e1, e2]
    split_ifs <;>
      nlinarith [sq_nonneg (w x - w (x + unitVec i) - ξ i),
        sq_nonneg (w x - w (x - unitVec i) + ξ i), sq_nonneg (ξ i)]
  simp only [gradNormSq, Fin.sum_univ_two]
  nlinarith [key 0, key 1]

/-- **The multiscale Poincaré inequality in the form of the proof of Lemma 5.8** (Armstrong and
Dario, first display of the proof of Lemma 5.8, with Proposition A.2), in dimension two. -/
theorem exists_flatness_le_multiscale :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m n : ℕ, (m : ℝ) / 2 ≤ n → n ≤ m →
      ∀ (z : Vertex 2) (w : Vertex 2 → ℝ) (ξ : Fin 2 → ℝ),
        ((cube m z).card : ℝ)⁻¹ * ∑ x ∈ cube m z,
            (w x - affineFun ξ x - finsetMean (cube m z) (fun y => w y - affineFun ξ y)) ^ 2 ≤
          C * (9 : ℝ) ^ n * (((cube m z).card : ℝ)⁻¹ * ∑ x ∈ cube m z, gradNormSq (cube m z) w x +
            (ξ 0 ^ 2 + ξ 1 ^ 2)) +
          C * (3 : ℝ) ^ m * ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k *
            (((centers m z k).card : ℝ)⁻¹ * ∑ y ∈ centers m z k, ∑ j : Fin 2,
                (((9 : ℝ) ^ k)⁻¹ * gradSum (subcube k y) w j - ξ j) ^ 2 +
              ((9 : ℝ) ^ k)⁻¹ * (ξ 0 ^ 2 + ξ 1 ^ 2)) := by
  obtain ⟨C₀, hC₀, h⟩ := exists_multiscalePoincare_affine (d := 2)
  refine ⟨2 * C₀, by positivity, fun m n hmn hnm z w ξ => ?_⟩
  have hmain := h m n hmn hnm z w ξ
  set N : ℝ := ((cube m z).card : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast card_cube_pos m z
  set Ξ := ξ 0 ^ 2 + ξ 1 ^ 2 with hΞ
  have hΞ0 : 0 ≤ Ξ := by positivity
  -- the gradient term
  have hG : N⁻¹ * ∑ x ∈ cube m z, gradNormSq (cube m z) (fun y => w y - affineFun ξ y) x ≤
      2 * (N⁻¹ * ∑ x ∈ cube m z, gradNormSq (cube m z) w x + Ξ) := by
    have h1 : ∑ x ∈ cube m z, gradNormSq (cube m z) (fun y => w y - affineFun ξ y) x ≤
        ∑ x ∈ cube m z, (2 * gradNormSq (cube m z) w x + 2 * Ξ) :=
      Finset.sum_le_sum fun x _ => gradNormSq_sub_affineFun_le _ w ξ x
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hNpos.le)
    rw [← hN] at h2
    have e : N⁻¹ * (2 * ∑ x ∈ cube m z, gradNormSq (cube m z) w x + N * (2 * Ξ)) =
        2 * (N⁻¹ * ∑ x ∈ cube m z, gradNormSq (cube m z) w x + Ξ) := by
      field_simp
    linarith
  -- the block terms
  set Y : ℕ → ℝ := fun k => ((centers m z k).card : ℝ)⁻¹ * ∑ y ∈ centers m z k, ∑ j : Fin 2,
    ((((3 : ℝ) ^ k) ^ 2)⁻¹ * gradSum (subcube k y) w j - (1 - ((3 : ℝ) ^ k)⁻¹) * ξ j) ^ 2
    with hY
  set Z : ℕ → ℝ := fun k => ((centers m z k).card : ℝ)⁻¹ * ∑ y ∈ centers m z k, ∑ j : Fin 2,
    (((9 : ℝ) ^ k)⁻¹ * gradSum (subcube k y) w j - ξ j) ^ 2 with hZ
  have hY0 : ∀ k, 0 ≤ Y k := fun k => mul_nonneg (by positivity)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hYZ : ∀ k ∈ Finset.Ico n m, Y k ≤ 2 * (Z k + ((9 : ℝ) ^ k)⁻¹ * Ξ) := by
    intro k hk
    have hkm : k ≤ m := (Finset.mem_Ico.1 hk).2.le
    have h9 : ((3 : ℝ) ^ k) ^ 2 = 9 ^ k := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have hc : (0 : ℝ) < (centers m z k).card := by
      rw [card_centers hkm]
      positivity
    set t : ℝ := ((3 : ℝ) ^ k)⁻¹ with ht
    have ht2 : t ^ 2 = ((9 : ℝ) ^ k)⁻¹ := by rw [ht, inv_pow, h9]
    have hpt : ∀ y ∈ centers m z k, ∑ j : Fin 2,
        ((((3 : ℝ) ^ k) ^ 2)⁻¹ * gradSum (subcube k y) w j - (1 - t) * ξ j) ^ 2 ≤
        ∑ j : Fin 2, (2 * (((9 : ℝ) ^ k)⁻¹ * gradSum (subcube k y) w j - ξ j) ^ 2 +
          2 * (t ^ 2 * ξ j ^ 2)) := by
      intro y _
      refine Finset.sum_le_sum fun j _ => ?_
      rw [h9]
      nlinarith [sq_nonneg (((9 : ℝ) ^ k)⁻¹ * gradSum (subcube k y) w j - ξ j - t * ξ j)]
    have hsum := Finset.sum_le_sum hpt
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have hjs : ∑ i : Fin 2, ξ i ^ 2 = Ξ := by rw [Fin.sum_univ_two]
    rw [hjs, ht2] at hsum
    have h2 := mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hc.le)
    simp only [hY, hZ]
    have e : ((centers m z k).card : ℝ)⁻¹ * (2 * ∑ y ∈ centers m z k, ∑ j : Fin 2,
        (((9 : ℝ) ^ k)⁻¹ * gradSum (subcube k y) w j - ξ j) ^ 2 +
        2 * (((9 : ℝ) ^ k)⁻¹ * (((centers m z k).card : ℝ) * Ξ))) =
        2 * (((centers m z k).card : ℝ)⁻¹ * ∑ y ∈ centers m z k, ∑ j : Fin 2,
          (((9 : ℝ) ^ k)⁻¹ * gradSum (subcube k y) w j - ξ j) ^ 2 + ((9 : ℝ) ^ k)⁻¹ * Ξ) := by
      field_simp
    linarith
  -- Cauchy–Schwarz over the scales
  set S := ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (Y k) with hS
  have hCS : S ^ 2 ≤ (3 : ℝ) ^ m * ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Y k := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ico n m)
      (fun k => Real.sqrt ((3 : ℝ) ^ k)) (fun k => Real.sqrt ((3 : ℝ) ^ k) * Real.sqrt (Y k))
    have e1 : ∑ k ∈ Finset.Ico n m, Real.sqrt ((3 : ℝ) ^ k) *
        (Real.sqrt ((3 : ℝ) ^ k) * Real.sqrt (Y k)) = S := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, Real.mul_self_sqrt (by positivity)]
    have e2 : ∑ k ∈ Finset.Ico n m, Real.sqrt ((3 : ℝ) ^ k) ^ 2 =
        ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k :=
      Finset.sum_congr rfl fun k _ => Real.sq_sqrt (by positivity)
    have e3 : ∑ k ∈ Finset.Ico n m, (Real.sqrt ((3 : ℝ) ^ k) * Real.sqrt (Y k)) ^ 2 =
        ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Y k :=
      Finset.sum_congr rfl fun k _ => by
        rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (hY0 k)]
    rw [e1, e2, e3] at h1
    have h3 : ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k ≤ 3 ^ m :=
      (Finset.sum_le_sum_of_subset_of_nonneg
        (fun k hk => Finset.mem_range.2 (Finset.mem_Ico.1 hk).2)
        fun _ _ _ => by positivity).trans (sum_range_three_pow_le m)
    exact h1.trans (mul_le_mul_of_nonneg_right h3
      (Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (hY0 k)))
  have hYsum : ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Y k ≤
      2 * ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * (Z k + ((9 : ℝ) ^ k)⁻¹ * Ξ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have := mul_le_mul_of_nonneg_left (hYZ k hk) (show (0 : ℝ) ≤ 3 ^ k by positivity)
    linarith
  have h9n : (3 : ℝ) ^ (2 * n) = 9 ^ n := by
    rw [pow_mul]
    norm_num
  rw [h9n] at hmain
  have hS' : C₀ * S ^ 2 ≤ C₀ * ((3 : ℝ) ^ m *
      (2 * ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * (Z k + ((9 : ℝ) ^ k)⁻¹ * Ξ))) :=
    mul_le_mul_of_nonneg_left (hCS.trans (mul_le_mul_of_nonneg_left hYsum (by positivity))) hC₀
  have hG' := mul_le_mul_of_nonneg_left hG (show 0 ≤ C₀ * (9 : ℝ) ^ n by positivity)
  simp only [hZ] at hS'
  calc _ ≤ C₀ * 9 ^ n * (N⁻¹ *
          ∑ x ∈ cube m z, gradNormSq (cube m z) (fun y => w y - affineFun ξ y) x) +
        C₀ * S ^ 2 := hmain
    _ ≤ _ := by nlinarith

end Rigidity.Percolation
