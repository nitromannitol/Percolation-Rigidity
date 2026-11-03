import Rigidity.Frozen.GadgetNumDenomRecsV1

/-!
# Exponential growth of the gadget numerator

The proved paired identities preserve positivity of the numerator and nonnegativity of
the denominator. They give the stronger bound `3 ^ n ≤ A (n + 1)`, and hence the strict
inequality at the exponent `n - 1` printed in the source.
-/

namespace Rigidity.Gadget

/-- The paired identities preserve a positive numerator and nonnegative denominator. -/
theorem A_succ_pos_and_B_nonneg (n : ℕ) : 0 < A (n + 1) ∧ 0 ≤ B n := by
  induction n with
  | zero => simp only [Nat.zero_add, A_one, B_zero]; omega
  | succ n ih =>
      obtain ⟨hB, hA⟩ := numDenomRecs n
      constructor <;> omega

/-- The numerator grows at least as fast as `3 ^ n`, with the original integer carrier. -/
theorem three_pow_le_A_succ (n : ℕ) : (3 : ℤ) ^ n ≤ A (n + 1) := by
  induction n with
  | zero => simp only [pow_zero, Nat.zero_add, A_one, le_refl]
  | succ n ih =>
      have hB := (A_succ_pos_and_B_nonneg n).2
      have hA := (numDenomRecs n).2
      rw [pow_succ]
      linarith

/-- The paper's exponential-growth lemma, including its strict inequality and exponent. -/
theorem three_pow_pred_lt_A_succ (n : ℕ) (hn : 1 ≤ n) :
    (3 : ℤ) ^ (n - 1) < A (n + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hpow : 0 < (3 : ℤ) ^ k := pow_pos (by norm_num) k
  have hA := three_pow_le_A_succ (k + 1)
  rw [pow_succ] at hA
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
    (show (3 : ℤ) ^ k < A (k + 1 + 1) by linarith)

end Rigidity.Gadget
