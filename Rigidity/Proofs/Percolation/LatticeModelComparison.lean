import LatticeProb.Prob.Percolation.LatticeUniqueClusterEvent
import Rigidity.Vendor.FormalMathPercolation.Literature.UniquenessInfiniteCluster

/-!
# Comparison of lattice bond models

The integer lattice and its genuine bonds agree with the lattice graph used in the
Burton–Keane uniqueness theorem in every dimension.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Percolation.Literature

/-- The two nearest-neighbor graphs on the integer lattice coincide. -/
theorem nearestNeighborGraph_eq_zdGraph (d : ℕ) :
    nearestNeighborGraph d = LatticeModels.zdGraph d := by
  ext x y
  rw [LatticeModels.zdGraph_adj_iff]
  rfl

/-- Genuine bonds are the edges of the lattice graph. -/
def bondEquiv (d : ℕ) : Bond d ≃ (LatticeModels.zdGraph d).edgeSet where
  toFun e := ⟨e.1, by
    obtain ⟨x, y, h, hxy⟩ := e.2
    rw [h, SimpleGraph.mem_edgeSet, ← nearestNeighborGraph_eq_zdGraph]
    exact lattice_adj_iff_l1Dist.mpr hxy⟩
  invFun e := ⟨e.1, by
    obtain ⟨x, y, h⟩ : ∃ x y, e.1 = s(x, y) :=
      Sym2.inductionOn e.1 (fun x y => ⟨x, y, rfl⟩)
    refine ⟨x, y, h, lattice_adj_iff_l1Dist.mp ?_⟩
    rw [nearestNeighborGraph_eq_zdGraph, ← SimpleGraph.mem_edgeSet, ← h]
    exact e.2⟩
  left_inv e := Subtype.ext rfl
  right_inv e := Subtype.ext rfl

end Rigidity.Percolation
