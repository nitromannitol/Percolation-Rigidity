import Mathlib

/-!
# Power differences and resampling

The squared difference of two powers is controlled by the squared difference of their bases
and powers of the two endpoints.
-/

namespace Rigidity.Proofs.S2

/-- A power difference has a symmetric squared endpoint bound. -/
theorem sq_pow_sub_pow_le (a b : ℝ) (n : ℕ) :
    (a ^ n - b ^ n) ^ 2 ≤ (n : ℝ) ^ 2 * (a - b) ^ 2 *
      (|a| ^ (2 * (n - 1)) + |b| ^ (2 * (n - 1))) := by
  have h := abs_pow_sub_pow_le (a := a) (b := b) (n := n)
  have hprod : 0 ≤ |a - b| * (n : ℝ) * max |a| |b| ^ (n - 1) := by positivity
  have hsq := (sq_le_sq₀ (abs_nonneg _) hprod).2 h
  have hmaxsq : (max |a| |b| ^ (n - 1)) ^ 2 ≤
      |a| ^ (2 * (n - 1)) + |b| ^ (2 * (n - 1)) := by
    rw [← pow_mul, show (n - 1) * 2 = 2 * (n - 1) by omega]
    rcases le_total |a| |b| with hab | hba
    · rw [max_eq_right hab]
      exact le_add_of_nonneg_left (by positivity)
    · rw [max_eq_left hba]
      exact le_add_of_nonneg_right (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hmaxsq (show 0 ≤ (n : ℝ) ^ 2 * (a - b) ^ 2 by positivity)
  calc
    _ = |a ^ n - b ^ n| ^ 2 := (sq_abs _).symm
    _ ≤ (|a - b| * (n : ℝ) * max |a| |b| ^ (n - 1)) ^ 2 := hsq
    _ = ((n : ℝ) ^ 2 * (a - b) ^ 2) * (max |a| |b| ^ (n - 1)) ^ 2 := by
      simp only [mul_pow, sq_abs]
      ring
    _ ≤ _ := hmul

end Rigidity.Proofs.S2
