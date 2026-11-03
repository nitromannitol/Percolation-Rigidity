import Rigidity.Frozen.GadgetAV1
import Rigidity.Frozen.GadgetBV1

namespace Rigidity.Gadget

theorem A_zero : A 0 = 1 := by rfl
theorem A_one : A 1 = 1 := by rfl
theorem A_succ_succ (k : ℕ) :
    A (k + 1 + 1) = 4 * A (k + 1) - A k := by rfl

theorem B_zero : B 0 = 0 := by rfl
theorem B_one : B 1 = 1 := by rfl
theorem B_succ_succ (k : ℕ) :
    B (k + 1 + 1) = 4 * B (k + 1) - B k := by rfl

theorem numDenomRecs_proof (k : ℕ) :
    A (k + 1) + B k = B (k + 1) ∧
    3 * A (k + 1) + 2 * B k = A (k + 1 + 1) := by
  simpa only [A, B, abState_succ, Prod.fst, Prod.snd] using (abState_rel k)

end Rigidity.Gadget
