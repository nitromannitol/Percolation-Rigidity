import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Polynomial factors in exponential bounds

A polynomial factor can be absorbed into an exponential decay at the cost of
halving its rate, with an explicit constant.
-/

namespace Rigidity.Percolation

/-- A nonnegative power multiplied by exponential decay is bounded by a
slower exponential with an explicit constant. -/
theorem pow_mul_exp_neg_le (k : ℕ) {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    x ^ k * Real.exp (-c * x) ≤
      ((k.factorial : ℝ) / (c / 2) ^ k) * Real.exp (-(c / 2) * x) := by
  have hc2 : 0 < c / 2 := by positivity
  have hpow : 0 < (c / 2) ^ k := pow_pos hc2 _
  have hfac : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h := Real.pow_div_factorial_le_exp ((c / 2) * x) (mul_nonneg hc2.le hx) k
  have h' := (div_le_iff₀ hfac).mp h
  rw [mul_pow] at h'
  have hbound : x ^ k ≤
      ((k.factorial : ℝ) / (c / 2) ^ k) * Real.exp ((c / 2) * x) := by
    have hb : x ^ k ≤ ((k.factorial : ℝ) * Real.exp ((c / 2) * x)) /
        (c / 2) ^ k := by
      apply (le_div_iff₀ hpow).2
      simpa only [mul_comm] using h'
    convert hb using 1; ring
  calc
    _ ≤ (((k.factorial : ℝ) / (c / 2) ^ k) * Real.exp ((c / 2) * x)) *
        Real.exp (-c * x) := mul_le_mul_of_nonneg_right hbound (Real.exp_nonneg _)
    _ = ((k.factorial : ℝ) / (c / 2) ^ k) * Real.exp (-(c / 2) * x) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The polynomial test-cube count can be absorbed into an exponential in
the side length, with an explicit finite constant. -/
theorem testCube_count_mul_exp_neg_le (d n : ℕ) {c : ℝ} (hc : 0 < c) :
    (((3 : ℝ) ^ n + 1) * (6 * (3 : ℝ) ^ n + 1) ^ d) *
        Real.exp (-c * (3 : ℝ) ^ n) ≤
      (2 * 7 ^ d * ((d + 1).factorial : ℝ) / (c / 2) ^ (d + 1)) *
        Real.exp (-(c / 2) * (3 : ℝ) ^ n) := by
  let x : ℝ := (3 : ℝ) ^ n
  have hx : 1 ≤ x := one_le_pow₀ (by norm_num)
  have hx0 : 0 ≤ x := by linarith
  have hcount : (x + 1) * (6 * x + 1) ^ d ≤ (2 * 7 ^ d) * x ^ (d + 1) := by
    calc
      _ ≤ (2 * x) * (7 * x) ^ d := by gcongr <;> linarith
      _ = _ := by rw [mul_pow, pow_succ]; ring
  calc
    _ ≤ ((2 * 7 ^ d) * x ^ (d + 1)) * Real.exp (-c * x) :=
      mul_le_mul_of_nonneg_right hcount (Real.exp_nonneg _)
    _ = (2 * 7 ^ d) * (x ^ (d + 1) * Real.exp (-c * x)) := by ring
    _ ≤ (2 * 7 ^ d) * (((d + 1).factorial : ℝ) / (c / 2) ^ (d + 1) *
        Real.exp (-(c / 2) * x)) :=
      mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le (d + 1) hc hx0) (by positivity)
    _ = _ := by ring

end Rigidity.Percolation
