import Rigidity.Support.AmbientOpenGadgetGrowth

namespace Rigidity.OpenGadget

open LatticeProb.Network.OpenLadder.Embedding

/-- Uniform integer oscillation on the open nearest-neighbor gadget in every dimension ≥ two. -/
theorem exponential_growth_on_ambient_open_gadget :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (hd : 2 ≤ d) (n : ℕ), 1 ≤ n →
      ∀ (u : (Fin d → ℤ) → ℝ),
        (∀ x ∈ ambientSites hd (n : ℤ), ∃ z : ℤ, u x = (z : ℝ)) →
        Ambient.AmbientHarmonic hd (n : ℤ) u →
        (∃ x ∈ ambientSites hd (n : ℤ), ∃ y ∈ ambientSites hd (n : ℤ), u x ≠ u y) →
        C * (3 : ℝ) ^ n ≤ |u (Ambient.ambientTarget d) - u (Ambient.ambientSource d)| := by
  exact Ambient.ambient_open_gadget_exponential_growth

end Rigidity.OpenGadget
