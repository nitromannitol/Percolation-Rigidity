import Rigidity.Proofs.S2.ClusterDensityInfluenceBound
import LatticeProb.Prob.Percolation.LatticeClusterLipschitzConsumer

/-!
# Geometric size of finite components

A finite connected component contains more vertices than the coordinate displacement between
any two of its vertices. This localizes the bonds that can influence a cluster-density count.
-/

namespace Rigidity.Proofs.S2

open LatticeProb.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

/-- Coordinate displacement between two vertices is strictly less than the component size. -/
theorem coordinate_displacement_lt_finiteComponent_card (C : OpenComponent ω)
    (hf : C.supp.Finite) (x y : C) (i : Fin d) :
    |(x.val i : ℝ) - (y.val i : ℝ)| < C.supp.ncard := by
  classical
  letI : Fintype C := hf.fintype
  obtain ⟨w, hw, hlen⟩ := C.connected_toSimpleGraph.exists_path_of_dist x y
  have hcard := hw.length_lt
  rw [hlen] at hcard
  change (componentGraph C).dist x y < Fintype.card ↥C.supp at hcard
  rw [Set.fintypeCard_eq_ncard] at hcard
  have hdist := component_coordinate_dist_bound C i x y
  simp only [one_mul] at hdist
  exact hdist.trans_lt (by exact_mod_cast hcard)

/-- If a bond is coordinate-separated from the counting cube, any nonzero influence requires a
finite endpoint component larger than the separation. -/
theorem nonzero_influence_large_finite_component (m : ℕ) (k : Vertex d)
    (ω η : Configuration d) (e : Bond d) (i : Fin d) (R : ℝ)
    (hsep : ∀ x ∈ triadicCube d m k, ∀ y ∈ e.val, R ≤ |(x i : ℝ) - (y i : ℝ)|)
    (hne : infiniteClusterCount (triadicCube d m k) ω ≠
      infiniteClusterCount (triadicCube d m k) (resampleBond ω η e)) :
    ∃ y ∈ e.val, R < (finiteComponentVertices ω y).card ∨
      R < (finiteComponentVertices (resampleBond ω η e) y).card := by
  obtain ⟨x, hx, y, hy, h⟩ := nonzero_influence_reaches_finite_component m k ω η e hne
  refine ⟨y, hy, ?_⟩
  rcases h with ⟨hxy, hf⟩ | ⟨hxy, hf⟩
  · left
    let C := (openGraph ω).connectedComponentMk y
    have hxC : x ∈ C.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
      (SimpleGraph.ConnectedComponent.sound hxy)
    have hyC : y ∈ C.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 rfl
    have hd := coordinate_displacement_lt_finiteComponent_card C hf ⟨x, hxC⟩ ⟨y, hyC⟩ i
    rw [card_finiteComponentVertices]
    exact (hsep x hx y hy).trans_lt hd
  · right
    let C := (openGraph (resampleBond ω η e)).connectedComponentMk y
    have hxC : x ∈ C.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
      (SimpleGraph.ConnectedComponent.sound hxy)
    have hyC : y ∈ C.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 rfl
    have hd := coordinate_displacement_lt_finiteComponent_card C hf ⟨x, hxC⟩ ⟨y, hyC⟩ i
    rw [card_finiteComponentVertices]
    exact (hsep x hx y hy).trans_lt hd

end Rigidity.Proofs.S2
