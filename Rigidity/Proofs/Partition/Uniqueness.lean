import Rigidity.Proofs.Partition.Paths
import Rigidity.Proofs.Partition.AlmostSure

/-!
# Uniqueness of the infinite cluster from the partition

On the partition event the anchors of all partition cubes lie in one infinite open component,
and every vertex of an infinite open component is joined to the anchor of its partition cube.
Hence the infinite open component is unique. For supercritical bond percolation on `ℤᵈ`, `d ≥ 2`,
this gives, almost surely, exactly one infinite open component.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory

variable {d : ℕ}

/-- On the partition event there is exactly one infinite open component. -/
theorem hasUniqueInfiniteOpenComponent_of_partitionEvent (hd : 0 < d) {ω : Configuration d}
    (hP : PartitionEvent ω) : HasUniqueInfiniteOpenComponent ω := by
  have h0 := infinite_supp_partitionAnchor hd hP 0
  refine ⟨(openGraph ω).connectedComponentMk (partitionAnchor ω 0), h0, fun C hC => ?_⟩
  obtain ⟨x, hx⟩ := hC.nonempty
  have hCx : C = (openGraph ω).connectedComponentMk x :=
    ((SimpleGraph.ConnectedComponent.mem_supp_iff C x).1 hx).symm
  have hinf : ((openGraph ω).connectedComponentMk x).supp.Infinite := hCx ▸ hC
  have hxa : (openGraph ω).Reachable x (partitionAnchor ω x) := by
    refine (reachable_partitionAnchor_of_infinite hd hP hinf).mono ?_
    intro u v h
    exact h.1
  rw [hCx, SimpleGraph.ConnectedComponent.eq]
  exact hxa.trans (reachable_partitionAnchor hd hP x 0)

/-- **Uniqueness of the infinite cluster.** For supercritical bond percolation on `ℤᵈ`, `d ≥ 2`,
almost surely there is exactly one infinite open component. -/
theorem ae_hasUniqueInfiniteOpenComponent [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∀ᵐ ω ∂(latticeBondLaw d p), HasUniqueInfiniteOpenComponent ω := by
  filter_upwards [ae_partitionEvent hd hpc] with ω hP
  exact hasUniqueInfiniteOpenComponent_of_partitionEvent (by omega) hP

end Rigidity.Percolation
