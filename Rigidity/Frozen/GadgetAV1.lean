import Rigidity.Support.GadgetState

namespace Rigidity.Gadget

/-- The integer numerator sequence of the paper's recurrence. -/
def A (n : ℕ) : ℤ := (abState n).1.1

end Rigidity.Gadget
