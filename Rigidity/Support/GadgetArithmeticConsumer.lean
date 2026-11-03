import Rigidity.Support.GadgetCoprime
import Rigidity.Support.GadgetGrowth

/-!
# Arithmetic data for the gadget fraction

At every positive source index the fraction has a positive denominator, coprime integer
numerator and denominator, and the stated strict numerator growth. The first index also
computes to the fraction `3 / 1`.
-/

namespace Rigidity.Gadget

/-- Positive source indices give a positive denominator and reduced, growing numerator. -/
theorem arithmetic_data (n : ℕ) (hn : 1 ≤ n) :
    0 < B n ∧ Nat.Coprime (A (n + 1)).natAbs (B n).natAbs ∧
      (3 : ℤ) ^ (n - 1) < A (n + 1) := by
  refine ⟨?_, A_succ_natAbs_coprime_B_natAbs n, three_pow_pred_lt_A_succ n hn⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  change 0 < B (k + 1)
  have hpos := A_succ_pos_and_B_nonneg k
  have hB := (numDenomRecs k).1
  omega

/-- The first source index has numerator three, denominator one, and both source conclusions. -/
theorem arithmetic_one :
    A 2 = 3 ∧ B 1 = 1 ∧ Int.gcd (A 2) (B 1) = 1 ∧ (3 : ℤ) ^ 0 < A 2 := by
  refine ⟨?_, B_one, reduced_rational 1 (by omega), ?_⟩
  · have hA := A_succ_succ 0
    norm_num only [Nat.zero_add, A_one, A_zero] at hA
    exact hA
  · exact three_pow_pred_lt_A_succ 1 (by omega)

end Rigidity.Gadget
