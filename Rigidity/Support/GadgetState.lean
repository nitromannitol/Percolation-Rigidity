import Mathlib

namespace Rigidity.Gadget

/-- The paired state for the two integer recurrences in the paper. -/
def abState : ℕ → (ℤ × ℤ) × (ℤ × ℤ) :=
  Nat.rec (((1 : ℤ), (1 : ℤ)), ((0 : ℤ), (1 : ℤ)))
    (fun _ s =>
      ((s.1.2, 4 * s.1.2 - s.1.1),
       (s.2.2, 4 * s.2.2 - s.2.1)))

theorem abState_succ (k : ℕ) :
    abState (k + 1) =
      (((abState k).1.2, 4 * (abState k).1.2 - (abState k).1.1),
       ((abState k).2.2, 4 * (abState k).2.2 - (abState k).2.1)) := by
  rfl

theorem abState_rel (k : ℕ) :
    (abState k).1.2 + (abState k).2.1 = (abState k).2.2 ∧
    3 * (abState k).1.2 + 2 * (abState k).2.1 =
      4 * (abState k).1.2 - (abState k).1.1 := by
  induction k with
  | zero => norm_num [abState]
  | succ k ih =>
      rw [abState_succ]
      rcases h : abState k with ⟨⟨a, a₁⟩, ⟨b, b₁⟩⟩
      simp only [h] at ih ⊢
      omega

end Rigidity.Gadget
