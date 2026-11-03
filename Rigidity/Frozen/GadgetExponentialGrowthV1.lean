import Rigidity.Support.GadgetGrowth

/-!
# Exponential growth of the gadget numerator

The paper's integer numerator strictly exceeds `3 ^ (n - 1)` for every positive index.
The exponent is natural subtraction and the power and comparison are over the integers.
-/

namespace Rigidity.Gadget

/-- The gadget numerator satisfies the strict exponential bound at every `n ≥ 1`. -/
theorem exponentialGrowth (n : ℕ) (hn : 1 ≤ n) :
    (3 : ℤ) ^ (n - 1) < A (n + 1) := by
  exact three_pow_pred_lt_A_succ n hn

end Rigidity.Gadget
