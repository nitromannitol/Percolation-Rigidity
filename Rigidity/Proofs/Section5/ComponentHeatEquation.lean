import Rigidity.Proofs.Section5.PlanarKernelLimit

/-!
# The heat equation on open components

The transition kernel satisfies the discrete heat equation with the component Laplacian.
-/

open Filter Topology LatticeProb.Percolation
open scoped Classical
namespace Rigidity.Proofs.Section5

/-- The heat equation on an infinite open component. -/
theorem componentLaplacian_heat {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (hC : C.supp.Infinite) (n : ℕ) (x y : C) :
    componentLaplacian C (fun z => LatticeProb.Graph.heat (componentGraph C) n z y) x =
      ((componentGraph C).degree x : ℝ) *
        (LatticeProb.Graph.heat (componentGraph C) (n + 1) x y -
          LatticeProb.Graph.heat (componentGraph C) n x y) := by
  letI : Infinite C := Set.infinite_coe_iff.mpr hC
  have hd : ((componentGraph C).degree x : ℝ) ≠ 0 := by
    exact_mod_cast (LatticeProb.Graph.degree_pos C.connected_toSimpleGraph x).ne'
  rw [LatticeProb.Graph.heat_succ, LatticeProb.Graph.walkOp]
  simp only [componentLaplacian, Finset.sum_sub_distrib, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  field_simp

end Rigidity.Proofs.Section5
