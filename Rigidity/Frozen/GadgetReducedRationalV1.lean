import Rigidity.Support.GadgetCoprime

/-!
# Reduced rational form of the gadget fraction

The paper's integer numerator and denominator are coprime at every positive source index.
This result exposes the proved arithmetic lemma with the exact source index restriction.
-/

namespace Rigidity.Gadget

/-- The gadget fraction has coprime numerator and denominator for every `n ≥ 1`. -/
theorem reducedRational (n : ℕ) (hn : 1 ≤ n) :
    Int.gcd (A (n + 1)) (B n) = 1 := by
  exact reduced_rational n hn

end Rigidity.Gadget
