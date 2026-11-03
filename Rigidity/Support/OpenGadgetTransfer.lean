import Rigidity.Support.GadgetArithmetic
import LatticeProb.Network.OpenLadderTransfer
import LatticeProb.Network.OpenLadderConnected
import LatticeProb.Network.FiniteBoundaryUniqueness

/-!
# The paper numerator transfers the actual open-gadget voltage

The literal recurrence defining `Gadget.A` supplies the scalar data for open-ladder
Kirchhoff elimination. Finite boundary uniqueness on this connected graph turns
nonconstancy into unequal terminal values. The terminal identity is then pulled back
from real voltages to integer voltages without a resistance assumption.
-/

namespace Rigidity.OpenGadget

open LatticeProb.Network
open LatticeProb.Network.OpenLadder

/-- Casting the paper's defining recurrence gives the real transfer coefficients. -/
theorem A_real_recurrence (k : ℕ) :
    (Gadget.A (k + 2) : ℝ) = 4 * (Gadget.A (k + 1) : ℝ) - (Gadget.A k : ℝ) := by
  exact_mod_cast Gadget.A_succ_succ k

/-- The actual real terminal gap is the paper numerator times the actual top difference. -/
theorem terminal_gap_real {n : ℕ} (hn : 1 ≤ n) {u : Vertex (n : ℤ) → ℝ}
    (hu : Harmonic u) :
    u (target n) - u (source n) =
      (Gadget.A (n + 1) : ℝ) * rungDifference u n ⟨by omega, by omega⟩ := by
  exact terminal_gap_transfer (fun k => (Gadget.A k : ℝ))
    (by rw [Gadget.A_zero]; norm_num) (by rw [Gadget.A_one]; norm_num)
    A_real_recurrence hn hu

/-- The top difference is the signed integer difference between the actual top sites. -/
def topDifference {n : ℕ} (hn : 1 ≤ n) (u : Vertex (n : ℤ) → ℤ) : ℤ :=
  u (right n n ⟨by omega, by omega⟩) - u (left n n ⟨by omega, by omega⟩)

/-- Real harmonicity of an integer voltage gives the literal integer terminal identity. -/
theorem terminal_gap_integer {n : ℕ} (hn : 1 ≤ n) {u : Vertex (n : ℤ) → ℤ}
    (hu : Harmonic (fun v => (u v : ℝ))) :
    u (target n) - u (source n) = Gadget.A (n + 1) * topDifference hn u := by
  have h := terminal_gap_real hn hu
  dsimp only [rungDifference] at h
  unfold topDifference
  exact_mod_cast h

/-- Actual nonconstancy forces unequal terminals by finite connected boundary uniqueness. -/
theorem terminal_ne_integer {n : ℕ} (hn : 1 ≤ n) {u : Vertex (n : ℤ) → ℤ}
    (hu : Harmonic (fun v => (u v : ℝ))) (hnonconstant : ∃ x y, u x ≠ u y) :
    u (source n) ≠ u (target n) := by
  have hnonconstantReal : ∃ x y, (u x : ℝ) ≠ (u y : ℝ) := by
    obtain ⟨x, y, hxy⟩ := hnonconstant
    exact ⟨x, y, fun h => hxy (by exact_mod_cast h)⟩
  have hne := terminal_ne_of_harmonic_off_terminals (connected (by omega : 1 ≤ (n : ℤ)))
    isCond_unitCond (fun x hs ht => hu x ⟨hs, ht⟩) hnonconstantReal
  exact fun h => hne (by exact_mod_cast h)

/-- The exact transfer identity forces a nonzero integer top difference. -/
theorem topDifference_ne_zero {n : ℕ} (hn : 1 ≤ n) {u : Vertex (n : ℤ) → ℤ}
    (hu : Harmonic (fun v => (u v : ℝ))) (hnonconstant : ∃ x y, u x ≠ u y) :
    topDifference hn u ≠ 0 := by
  intro hzero
  have hgap := terminal_gap_integer hn hu
  rw [hzero, mul_zero, sub_eq_zero] at hgap
  exact terminal_ne_integer hn hu hnonconstant hgap.symm

end Rigidity.OpenGadget
