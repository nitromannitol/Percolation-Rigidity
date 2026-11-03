import Rigidity.Frozen.GadgetNumDenomRecsV1

/-!
# Coprimality of the gadget numerator and denominator

Consecutive terms of the integer denominator recurrence have gcd one. The proved
numerator-denominator identity then gives the reduced-rational lemma for the paper's
original integer sequences, with gcd valued in the natural numbers.
-/

namespace Rigidity.Gadget

/-- Consecutive denominator terms have integer gcd one, including the index zero. -/
theorem B_succ_gcd_B (n : ℕ) : Int.gcd (B (n + 1)) (B n) = 1 := by
  induction n with
  | zero =>
      change Int.gcd (B 1) (B 0) = 1
      rw [B_one, Int.one_gcd]
  | succ n ih =>
      rw [B_succ_succ, Int.gcd_mul_right_sub_left, Int.gcd_comm]
      exact ih

/-- The numerator and denominator have gcd one, even at the extra index zero. -/
theorem A_succ_gcd_B (n : ℕ) : Int.gcd (A (n + 1)) (B n) = 1 := by
  calc
    Int.gcd (A (n + 1)) (B n) = Int.gcd (A (n + 1) + B n) (B n) :=
      (Int.gcd_add_self_left (B n) (A (n + 1))).symm
    _ = Int.gcd (B (n + 1)) (B n) := by rw [(numDenomRecs n).1]
    _ = 1 := B_succ_gcd_B n

/-- The paper's reduced-rational lemma at every source index `n ≥ 1`. -/
theorem reduced_rational (n : ℕ) (hn : 1 ≤ n) : Int.gcd (A (n + 1)) (B n) = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact A_succ_gcd_B (k + 1)

/-- Coprimality of the natural absolute values uses exactly the integer gcd convention. -/
theorem A_succ_natAbs_coprime_B_natAbs (n : ℕ) :
    Nat.Coprime (A (n + 1)).natAbs (B n).natAbs := by
  exact A_succ_gcd_B n

end Rigidity.Gadget
