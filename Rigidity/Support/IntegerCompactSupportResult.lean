import LatticeProb.Graph.Zd.IntegerLaplacian

/-!
# Compactly supported functions with integer full lattice Laplacian

This is Proposition `integer-valued-compact-support` of the pinned paper, lines 2841–2843.
The standing dimension assumption is retained. Compact support on the discrete integer
lattice is expressed as finite function support, and the Laplacian is the full neighbor sum.
-/

namespace Rigidity.Support

/-- A compactly supported real function on the full integer lattice with integer-valued
Laplacian is integer-valued, under the paper's standing dimension assumption. -/
theorem integer_valued_compact_support {d : ℕ} (hd : 2 ≤ d)
    (u : (Fin d → ℤ) → ℝ) (hs : (Function.support u).Finite)
    (hΔ : ∀ x, ∃ n : ℤ,
      LatticeProb.Graph.laplacian (LatticeProb.Percolation.nearestNeighborGraph d) u x =
        (n : ℝ)) :
    ∀ x, ∃ n : ℤ, u x = (n : ℝ) :=
  LatticeProb.Graph.Zd.integer_values_of_finite_support_integer_laplacian
    (by omega) u hs hΔ

end Rigidity.Support
