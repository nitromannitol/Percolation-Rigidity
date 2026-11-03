import Rigidity.Support.OpenGadgetTransfer
import Rigidity.Support.GadgetGrowth

/-!
# Exponential integer oscillation on the corrected open gadget

A nonconstant integer voltage harmonic at every nonterminal has nonzero top difference.
Its absolute value is at least one, so the exact transfer identity yields the numerator
bound and hence `3 ^ n`. Explicit integer voltages at heights one and two consume the result.
-/

namespace Rigidity.OpenGadget

open LatticeProb.Network.OpenLadder

/-- The actual terminal oscillation dominates the positive paper numerator. -/
theorem A_le_abs_terminal_gap {n : ℕ} (hn : 1 ≤ n) {u : Vertex (n : ℤ) → ℤ}
    (hu : Harmonic (fun v => (u v : ℝ))) (hnonconstant : ∃ x y, u x ≠ u y) :
    Gadget.A (n + 1) ≤ |u (target n) - u (source n)| := by
  have htop := topDifference_ne_zero hn hu hnonconstant
  have hone : (1 : ℤ) ≤ |topDifference hn u| := by
    have hpos := abs_pos.mpr htop
    omega
  have hA := (Gadget.A_succ_pos_and_B_nonneg n).1
  rw [terminal_gap_integer hn hu, abs_mul, abs_of_pos hA]
  exact le_mul_of_one_le_right (le_of_lt hA) hone

/-- Corrected open-gadget exponential oscillation holds with source constant one. -/
theorem three_pow_le_abs_terminal_gap {n : ℕ} (hn : 1 ≤ n)
    {u : Vertex (n : ℤ) → ℤ} (hu : Harmonic (fun v => (u v : ℝ)))
    (hnonconstant : ∃ x y, u x ≠ u y) :
    (3 : ℤ) ^ n ≤ |u (target n) - u (source n)| := by
  exact (Gadget.three_pow_le_A_succ n).trans (A_le_abs_terminal_gap hn hu hnonconstant)

/-- The height-one integer voltage is the horizontal coordinate minus one. -/
def integerVoltageOne (v : Vertex 1) : ℤ := v.val.1 - 1

/-- Casting the explicit integer height-one voltage recovers the accepted real voltage. -/
theorem integerVoltageOne_cast :
    (fun v => (integerVoltageOne v : ℝ)) = voltageOne := by
  funext v
  simp only [integerVoltageOne, voltageOne, Int.cast_sub, Int.cast_one]

/-- Every actual nonterminal satisfies the height-one harmonic equation. -/
theorem integerVoltageOne_harmonic : Harmonic (fun v => (integerVoltageOne v : ℝ)) := by
  rw [integerVoltageOne_cast]
  exact voltageOne_harmonic

/-- The explicit height-one integer voltage is nonconstant on the actual carrier. -/
theorem integerVoltageOne_nonconstant : ∃ x y, integerVoltageOne x ≠ integerVoltageOne y := by
  refine ⟨source 1, target 1, ?_⟩
  norm_num [integerVoltageOne, source, target]

/-- The height-one integer terminal gap is three and its top difference is one. -/
theorem integerVoltageOne_gap :
    integerVoltageOne (target 1) - integerVoltageOne (source 1) = 3 ∧
      topDifference (n := 1) (by omega) integerVoltageOne = 1 := by
  norm_num [integerVoltageOne, source, target, topDifference, left, right]

/-- The height-one integer consumer attains the bound three. -/
theorem integerVoltageOne_growth :
    (3 : ℤ) ^ 1 ≤ |integerVoltageOne (target 1) - integerVoltageOne (source 1)| := by
  exact three_pow_le_abs_terminal_gap (n := 1) (by omega)
    integerVoltageOne_harmonic integerVoltageOne_nonconstant

/-- The six height-two integer values are 0, 4, 7, 11 on the bottom and 5, 6 on top. -/
def integerVoltageTwo (v : Vertex 2) : ℤ :=
  if v.val.2 = 2 then v.val.1 + 3
  else if v.val.1 ≤ 2 then 4 * (v.val.1 - 1) else 4 * v.val.1 - 5

/-- Casting the explicit height-two integers recovers the accepted real voltage. -/
theorem integerVoltageTwo_cast :
    (fun v => (integerVoltageTwo v : ℝ)) = voltageTwo := by
  funext v
  simp only [integerVoltageTwo, voltageTwo, Int.cast_ite, Int.cast_add,
    Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_one]

/-- All four actual nonterminals satisfy the height-two harmonic equations. -/
theorem integerVoltageTwo_harmonic : Harmonic (fun v => (integerVoltageTwo v : ℝ)) := by
  rw [integerVoltageTwo_cast]
  exact voltageTwo_harmonic

/-- The explicit height-two integer voltage is nonconstant on the actual carrier. -/
theorem integerVoltageTwo_nonconstant : ∃ x y, integerVoltageTwo x ≠ integerVoltageTwo y := by
  refine ⟨source 2, target 2, ?_⟩
  norm_num [integerVoltageTwo, source, target]

/-- The height-two integer terminal gap is eleven and its top difference is one. -/
theorem integerVoltageTwo_gap :
    integerVoltageTwo (target 2) - integerVoltageTwo (source 2) = 11 ∧
      topDifference (n := 2) (by omega) integerVoltageTwo = 1 := by
  norm_num [integerVoltageTwo, source, target, topDifference, left, right]

/-- The height-two integer consumer has gap eleven, which dominates nine. -/
theorem integerVoltageTwo_growth :
    (3 : ℤ) ^ 2 ≤ |integerVoltageTwo (target 2) - integerVoltageTwo (source 2)| := by
  exact three_pow_le_abs_terminal_gap (n := 2) (by omega)
    integerVoltageTwo_harmonic integerVoltageTwo_nonconstant

end Rigidity.OpenGadget
