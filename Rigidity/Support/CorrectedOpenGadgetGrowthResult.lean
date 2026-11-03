import Rigidity.Support.OpenGadgetIntegerGrowth

/-!
# Exponential growth on the corrected open gadget

The open ladder has a uniform positive exponential lower bound for the terminal
oscillation of every nonconstant integer voltage harmonic at every nonterminal.
This is the corrected open-carrier version of the gadget growth proposition.
-/

namespace Rigidity.OpenGadget

open LatticeProb.Network.OpenLadder

/-- A single positive real constant bounds terminal oscillation at every positive height
on the corrected open carrier. The accepted integer growth estimate gives constant one. -/
theorem corrected_open_gadget_exponential_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (u : Vertex (n : ℤ) → ℤ),
      Harmonic (fun v => (u v : ℝ)) → (∃ x y, u x ≠ u y) →
        C * (3 : ℝ) ^ n ≤ |(u (target (n : ℤ)) : ℝ) - (u (source (n : ℤ)) : ℝ)| := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro n hn u hu hnonconstant
  rw [one_mul]
  exact_mod_cast three_pow_le_abs_terminal_gap hn hu hnonconstant

end Rigidity.OpenGadget
