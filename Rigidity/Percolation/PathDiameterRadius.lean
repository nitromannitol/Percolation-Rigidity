import Rigidity.Percolation.OverlapPathCoalescence

/-!
# Path diameter and radius

A path with two coordinates separated by twice a threshold has a point at
least that threshold away from every prescribed center.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- Coordinate diameter at least `2 * r` forces a coordinate displacement
of at least `r` from every center. -/
theorem pathDiameterAtLeast.exists_far_from_center {d n : ℕ}
    {r : ℤ} {γ : Fin (n + 1) → Vertex d}
    (hdiam : pathDiameterAtLeast (2 * r) n γ) (z : Vertex d) :
    ∃ (i : Fin (n + 1)) (k : Fin d), r ≤ |γ i k - z k| := by
  obtain ⟨i, j, k, hfar⟩ := hdiam
  have htriangle := abs_sub_le (γ i k) (z k) (γ j k)
  rw [abs_sub_comm (z k) (γ j k)] at htriangle
  by_cases hi : r ≤ |γ i k - z k|
  · exact ⟨i, k, hi⟩
  · refine ⟨j, k, ?_⟩
    omega

/-- A diameter of `2 * t` dominates one tenth of the box radius `8 * t`
even after taking half the diameter. -/
theorem pathDiameterAtLeast.exists_far_from_center_at_scale {d n : ℕ}
    {t : ℕ} (ht : 0 < t) {γ : Fin (n + 1) → Vertex d}
    (hdiam : pathDiameterAtLeast (2 * (t : ℤ)) n γ) (z : Vertex d) :
    ∃ (i : Fin (n + 1)) (k : Fin d),
      8 * (t : ℤ) < 10 * |γ i k - z k| := by
  obtain ⟨i, k, hi⟩ := hdiam.exists_far_from_center z
  refine ⟨i, k, ?_⟩
  have ht' : (0 : ℤ) < t := by exact_mod_cast ht
  omega

end Rigidity.Percolation
