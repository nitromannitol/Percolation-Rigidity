import Rigidity.Proofs.Percolation.BondLawComparison
import Rigidity.Vendor.CriticalPercolation.GraphGeometry.VertexBall

/-!
# The lattice as a bounded-degree bond graph

Genuine nearest-neighbor bonds form a connected locally finite bond graph whose incidence
degree is at most twice the dimension.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation OAI.CriticalPercolation _root_.Percolation.Literature

/-- The integer lattice with its genuine unordered bonds. -/
def labelledLattice (d : ℕ) : BondGraph (Vertex d) (Bond d) where
  ends := Subtype.val

/-- The underlying graph of the labelled lattice is the usual lattice graph. -/
theorem labelledLattice_fullGraph (d : ℕ) :
    (labelledLattice d).fullGraph = nearestNeighborGraph d := by
  have hrange : (Subtype.val : Bond d → Sym2 (Vertex d)) '' Set.univ =
      (LatticeModels.zdGraph d).edgeSet := by
    ext e
    constructor
    · rintro ⟨b, _, rfl⟩
      exact (bondEquiv d b).property
    · intro he
      exact ⟨(bondEquiv d).symm ⟨e, he⟩, Set.mem_univ _, rfl⟩
  change SimpleGraph.fromEdgeSet ((Subtype.val : Bond d → Sym2 (Vertex d)) '' Set.univ) = _
  rw [hrange, SimpleGraph.fromEdgeSet_edgeSet, nearestNeighborGraph_eq_zdGraph]

/-- Lattice bonds incident to a vertex are the inverse image of its incidence set. -/
theorem labelledLattice_incidentEdges (d : ℕ) (v : Vertex d) :
    (labelledLattice d).incidentEdges {v} =
      (Subtype.val : Bond d → Sym2 (Vertex d)) ⁻¹'
        ((LatticeModels.zdGraph d).incidenceSet v) := by
  ext e
  simp only [BondGraph.incidentEdges, Set.mem_setOf_eq, Set.mem_singleton_iff,
    exists_eq_left, Set.mem_preimage, SimpleGraph.incidenceSet]
  exact ⟨fun he => ⟨(bondEquiv d e).property, he⟩, fun he => he.2⟩

/-- The labelled lattice has finitely many bonds at each vertex. -/
theorem labelledLattice_locallyFinite (d : ℕ) : (labelledLattice d).LocallyFinite := by
  intro v
  have he : {e | v ∈ (labelledLattice d).ends e} =
      (labelledLattice d).incidentEdges {v} := by
    ext e
    simp [BondGraph.incidentEdges]
  rw [he, labelledLattice_incidentEdges]
  exact Set.Finite.preimage Subtype.val_injective.injOn (Set.toFinite _)

/-- Exactly `2d` bonds are incident to each lattice vertex. -/
theorem labelledLattice_incidentEdges_ncard (d : ℕ) (v : Vertex d) :
    ((labelledLattice d).incidentEdges {v}).ncard = 2 * d := by
  rw [labelledLattice_incidentEdges,
    Set.ncard_preimage_of_injective_subset_range Subtype.val_injective]
  · rw [← SimpleGraph.coe_incidenceFinset, Set.ncard_coe_finset,
      SimpleGraph.card_incidenceFinset_eq_degree]
    have hn : (LatticeModels.zdGraph d).neighborSet v =
        (nearestNeighborGraph d).neighborSet v := by rw [nearestNeighborGraph_eq_zdGraph]
    have hc := Fintype.card_congr (Equiv.setCongr hn)
    rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hc
    rw [hc]
    exact LatticeProb.Graph.Zd.degree_eq v
  · intro e he
    exact ⟨(bondEquiv d).symm ⟨e, he.1⟩, rfl⟩

end Rigidity.Percolation
