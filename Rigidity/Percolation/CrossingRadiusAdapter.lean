import Rigidity.Percolation.CrossingPathCoalescence
import Rigidity.Percolation.PathDiameterRadius

/-!
# Crossing events and path radii

A crossing component connecting all paths with a specified ℓ¹ radius also
connects paths of sufficiently large coordinate diameter.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- Paths with coordinate diameter at least twice `t` connect to the crossing
component when every path reaching beyond `8t/10` from each center does. -/
theorem HasCrossingComponentConnectingPaths.of_l1_radius {d : ℕ}
    {ω : Configuration d} {B : Set (Vertex d)} {lower upper : Fin d → Set (Vertex d)}
    (t : ℕ) (ht : 0 < t)
    (h : HasCrossingComponentConnectingPaths ω B lower upper
      (fun n γ => ∀ z : Vertex d, ∃ i : Fin (n + 1),
        8 * (t : ℤ) < 10 * ∑ k, |γ i k - z k|)) :
    HasCrossingComponentConnectingPaths ω B lower upper
      (pathDiameterAtLeast (2 * (t : ℤ))) := by
  obtain ⟨root, hroot, hpaths⟩ := h
  refine ⟨root, hroot, ?_⟩
  intro n γ hdiam hstart hadj
  apply hpaths n γ ?_ hstart hadj
  intro z
  exact hdiam.exists_l1_far_from_center_at_scale ht z


/-- The same conclusion holds if the radius threshold uses any scale at most
`8 * t`, including the two scales of the subcube cover. -/
theorem HasCrossingComponentConnectingPaths.of_l1_radius_le {d : ℕ}
    {ω : Configuration d} {B : Set (Vertex d)} {lower upper : Fin d → Set (Vertex d)}
    (t N : ℕ) (ht : 0 < t) (hN : N ≤ 8 * t)
    (h : HasCrossingComponentConnectingPaths ω B lower upper
      (fun n γ => ∀ z : Vertex d, ∃ i : Fin (n + 1),
        (N : ℤ) < 10 * ∑ k, |γ i k - z k|)) :
    HasCrossingComponentConnectingPaths ω B lower upper
      (pathDiameterAtLeast (2 * (t : ℤ))) := by
  obtain ⟨root, hroot, hpaths⟩ := h
  refine ⟨root, hroot, ?_⟩
  intro n γ hdiam hstart hadj
  apply hpaths n γ ?_ hstart hadj
  intro z
  obtain ⟨i, hi⟩ := hdiam.exists_l1_far_from_center_at_scale ht z
  refine ⟨i, ?_⟩
  have hN' : (N : ℤ) ≤ 8 * (t : ℤ) := by exact_mod_cast hN
  exact lt_of_le_of_lt hN' hi

end Rigidity.Percolation
