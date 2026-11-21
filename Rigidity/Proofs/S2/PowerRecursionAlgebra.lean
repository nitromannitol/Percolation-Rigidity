import Mathlib

/-!
# Algebra for a power recursion

A nonnegative quantity satisfying a power inequality is bounded by the previous term plus the
coefficient of the highest remaining power.
-/

namespace Rigidity.Proofs.S2

/-- An elementary comparison for a power recursion. -/
theorem le_add_of_pow_le_pow_add_mul {a b c : ℝ} (hb : 0 ≤ b)
    (hc : 0 ≤ c) (n : ℕ) (hn : 1 ≤ n)
    (h : a ^ n ≤ b ^ n + c * a ^ (n - 1)) : a ≤ b + c := by
  by_contra hnot
  have hab : b < a := lt_of_le_of_lt (le_add_of_nonneg_right hc) (lt_of_not_ge hnot)
  have ha0 : 0 < a := lt_of_le_of_lt hb hab
  have hpow : b ^ (n - 1) ≤ a ^ (n - 1) := pow_le_pow_left₀ hb hab.le _
  have hbn : b ^ n ≤ b * a ^ (n - 1) := by
    calc
      _ = b * b ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
      _ ≤ b * a ^ (n - 1) := mul_le_mul_of_nonneg_left hpow hb
  have han : a ^ n = a * a ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
  have hpos : 0 < a ^ (n - 1) := pow_pos ha0 _
  have hmul := mul_lt_mul_of_pos_right (lt_of_not_ge hnot) hpos
  rw [han] at h
  nlinarith

end Rigidity.Proofs.S2
