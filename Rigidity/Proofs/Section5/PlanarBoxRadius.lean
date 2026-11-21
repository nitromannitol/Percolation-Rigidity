import Rigidity.Steps.Section5.FastDecayDichotomy
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Planar box radii

Two vertices lie in the inner half of a sufficiently large box whose radius grows at most
linearly with the distance of either vertex when the other is fixed.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

/-- Choose a box containing both vertices in its inner half, with a linearly bounded radius. -/
theorem exists_box_radius (y : Vertex 2) (N : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x : Vertex 2, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      (∀ i, 2 * |x i| ≤ (n : ℤ)) ∧ (∀ i, 2 * |y i| ≤ (n : ℤ)) ∧
      (n : ℝ) ≤ B * (eucl x + 1) := by
  let B : ℝ := (N : ℝ) + 2 * eucl y + 3
  have hy0 : 0 ≤ eucl y := norm_nonneg _
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hB : 1 ≤ B := by dsimp [B]; linarith
  refine ⟨B, hB, fun x => ?_⟩
  have hx0 : 0 ≤ eucl x := norm_nonneg _
  let r : ℝ := 2 * eucl x + 2 * eucl y + 2
  let n : ℕ := N + ⌈r⌉₊
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hlo : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
  have hhi : (⌈r⌉₊ : ℝ) < r + 1 := Nat.ceil_lt_add_one hr0
  have hnlo : r ≤ (n : ℝ) := by dsimp [n]; push_cast; linarith
  have hnhi : (n : ℝ) ≤ B * (eucl x + 1) := by
    dsimp [n, B, r] at *
    push_cast at *
    nlinarith
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := by dsimp [r] at hnlo; linarith
    exact_mod_cast this
  refine ⟨n, by dsimp [n]; omega, hn1, ?_, ?_, hnhi⟩
  · intro i
    have hi := abs_coord_le_eucl x i
    have hreal : (2 : ℝ) * |(x i : ℝ)| ≤ n := by dsimp [r] at hnlo; linarith
    exact_mod_cast hreal
  · intro i
    have hi := abs_coord_le_eucl y i
    have hreal : (2 : ℝ) * |(y i : ℝ)| ≤ n := by dsimp [r] at hnlo; linarith
    exact_mod_cast hreal

end Rigidity.Proofs.Section5
