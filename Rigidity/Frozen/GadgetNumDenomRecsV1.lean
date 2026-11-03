import Rigidity.Support.GadgetArithmetic

namespace Rigidity.Gadget

/-- The two identities of `lemma:num-denom-recs` at paper index `n = k + 1`. -/
theorem numDenomRecs (k : ℕ) :
    A (k + 1) + B k = B (k + 1) ∧
    3 * A (k + 1) + 2 * B k = A (k + 1 + 1) := by
  exact numDenomRecs_proof k

end Rigidity.Gadget
