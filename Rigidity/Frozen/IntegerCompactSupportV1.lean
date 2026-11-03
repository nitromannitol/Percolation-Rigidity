import Rigidity.Support.IntegerCompactSupportResult

namespace Rigidity

/-- A finitely supported real lattice function with integer-valued Laplacian is integer-valued. -/
theorem integer_valued_compact_support {d : ℕ} (hd : 2 ≤ d)
    (u : (Fin d → ℤ) → ℝ) (hs : (Function.support u).Finite)
    (hΔ : ∀ x, ∃ n : ℤ,
      LatticeProb.Graph.laplacian (LatticeProb.Percolation.nearestNeighborGraph d) u x =
        (n : ℝ)) :
    ∀ x, ∃ n : ℤ, u x = (n : ℝ) := by
  exact Support.integer_valued_compact_support hd u hs hΔ

end Rigidity
