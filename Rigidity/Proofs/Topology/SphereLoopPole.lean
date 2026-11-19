import Rigidity.Proofs.Topology.ClosedPathCircle
import Rigidity.Proofs.Topology.SpherePunctures

/-!
# A projection point for a simple loop

A closed path that is injective away from its endpoint omits a point of the two-sphere.
-/

open Set

namespace Rigidity.Topology

open Rigidity.External

/-- A simple closed path on the sphere omits a point. -/
theorem exists_sphere_point_not_mem_range {q : S2} (β : Path q q)
    (hβ : InjOn β (Ico 0 1)) : ∃ x : S2, x ∉ range β := by
  obtain ⟨x, hx⟩ := exists_not_mem_range_circle (closedPathCircle β)
    (continuous_closedPathCircle β) (injective_closedPathCircle β hβ)
  rw [range_closedPathCircle] at hx
  exact ⟨x, hx⟩

end Rigidity.Topology
