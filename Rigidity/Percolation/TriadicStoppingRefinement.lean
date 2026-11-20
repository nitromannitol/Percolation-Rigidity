import Rigidity.Percolation.TriadicStopping

/-!
# Refinement of stopping partitions

Enlarging a collection of good cubes refines its maximal stopping partition.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- At a common point, the maximal stopping cube for a larger good collection
is contained in the maximal stopping cube for the smaller collection. -/
theorem TriadicCube.vertices_subset_of_maximalStopping_of_subset {d : ℕ}
    {G H : Set (TriadicCube d)} (hGH : G ⊆ H) {Q R : TriadicCube d} {x : Vertex d}
    (hxQ : x ∈ Q.vertices) (hxR : x ∈ R.vertices)
    (hQ : Q.IsMaximalStopping G) (hR : R.IsMaximalStopping H) :
    R.vertices ⊆ Q.vertices := by
  have hscale : R.scale ≤ Q.scale := by
    by_contra h
    have hQR : Q.scale ≤ R.scale := by omega
    have hsub := vertices_subset_of_mem_of_scale_le hxQ hxR hQR
    have hstable : R ∈ stableGood G := by
      rw [eq_ancestor_of_mem hxQ hxR hQR]
      exact ancestor_mem_stableGood hQ.1.1 _
    have hstop : R.IsStopping G := by
      refine ⟨hstable, ?_⟩
      rcases hR.1.2 with hz | ⟨digits, hbad⟩
      · exact Or.inl hz
      · exact Or.inr ⟨digits, fun hchild => hbad (hchild.trans hGH)⟩
    have := hQ.2 R hstop hsub
    omega
  exact vertices_subset_of_mem_of_scale_le hxR hxQ hscale

end Rigidity.Percolation
