import Rigidity.Proofs.Percolation.PlanarOmegaIntegrals

/-!
# Elementary rates for the proof of Lemma 5.9

All the error terms of the proof of Lemma 5.9 of Armstrong and Dario are bounded by a constant
times `3^{-n/10}`: `3^{-n}`, `3^{-n/2}`, `9^{-n}` and `exp(-c 3ⁿ)`; and `(3ⁿ - 1)⁻² ≤ 4 · 9^{-n}`
for `n ≥ 1`. The increment `τ_n` is at most `3^{-n} ∑_{k ≤ n} 3^k τ_k`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5

namespace Rigidity.Percolation

theorem inv_three_pow_le_rpow (n : ℕ) : ((3 : ℝ) ^ n)⁻¹ ≤ (3 : ℝ) ^ (-(n : ℝ) / 10) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem one_div_sqrt_three_pow_le_rpow (n : ℕ) :
    1 / Real.sqrt ((3 : ℝ) ^ n) ≤ (3 : ℝ) ^ (-(n : ℝ) / 10) := by
  rw [one_div_sqrt_three_pow]
  refine (inv_sqrt_three_pow_le n).trans ?_
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem inv_nine_pow_le_rpow (n : ℕ) : ((9 : ℝ) ^ n)⁻¹ ≤ (3 : ℝ) ^ (-(n : ℝ) / 10) := by
  refine le_trans ?_ (inv_three_pow_le_rpow n)
  refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) (by norm_num) n)

theorem exp_neg_le_rpow {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Real.exp (-c * (3 : ℝ) ^ n) ≤ c⁻¹ * (3 : ℝ) ^ (-(n : ℝ) / 10) := by
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have h := exp_neg_le_inv (mul_pos hc h3)
  rw [neg_mul]
  refine h.trans ?_
  rw [mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_three_pow_le_rpow n) (inv_nonneg.2 hc.le)

theorem inv_sq_three_pow_sub_one_le {n : ℕ} (hn : 1 ≤ n) :
    (((3 : ℝ) ^ n - 1) ^ 2)⁻¹ ≤ 4 * ((9 : ℝ) ^ n)⁻¹ := by
  have h3 : (3 : ℝ) ≤ 3 ^ n := by
    calc (3 : ℝ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h1 : (3 : ℝ) ^ n / 2 ≤ 3 ^ n - 1 := by linarith
  have h2 : ((3 : ℝ) ^ n / 2) ^ 2 ≤ ((3 : ℝ) ^ n - 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have h9 : ((3 : ℝ) ^ n / 2) ^ 2 = (9 : ℝ) ^ n / 4 := by
    rw [div_pow, ← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h9] at h2
  calc (((3 : ℝ) ^ n - 1) ^ 2)⁻¹ ≤ ((9 : ℝ) ^ n / 4)⁻¹ := inv_anti₀ (by positivity) h2
    _ = 4 * ((9 : ℝ) ^ n)⁻¹ := by rw [inv_div, div_eq_mul_inv]

theorem planarTau_le_weighted (p : unitInterval) (n : ℕ) :
    planarTau p n ≤ ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * planarTau p k := by
  have h := Finset.single_le_sum (f := fun k => (3 : ℝ) ^ k * planarTau p k)
    (fun k _ => mul_nonneg (by positivity) (planarTau_nonneg p k)) (Finset.self_mem_range_succ n)
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  calc planarTau p n = ((3 : ℝ) ^ n)⁻¹ * ((3 : ℝ) ^ n * planarTau p n) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.2 h3.le)

end Rigidity.Percolation
