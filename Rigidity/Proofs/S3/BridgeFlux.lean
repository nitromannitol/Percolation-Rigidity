import Rigidity.Steps.S3.NotLipschitz
import LatticeProb.Network.FiniteBridgeRigidity

/-!
# `step:3.2-bridge-flux`: a harmonic function has zero gradient across a bridge

Step `step:3.2-bridge-flux` of Proposition 3.2 (corrected draft L1074-1080). Let `u` be harmonic on
an open cluster `C` and let `{x, y}` be an open edge of `C` whose removal disconnects `x` from `y`.
Deleting the edge from `C` maps every remaining walk of `C` into the open graph of the environment
in which the bond `{x, y}` is closed. Since that environment has a unique infinite cluster and `x`,
`y` lie in distinct clusters of it, one of them, say the cluster of `x`, is finite; the side of the
bridge containing `x` is then finite, and the flux of `u` out of this side, which is carried by the
single edge `(x, y)`, is the sum of the Laplacian of `u` over the side, hence zero
(`LatticeProb.Network.eq_of_harmonic_finite_deleted_component`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Rigidity.Proofs.S3

open LatticeProb LatticeProb.Percolation Rigidity.Section3 Rigidity.Steps.S3

variable {d : ℕ}

/-- The endpoints of a bond are adjacent in the lattice. -/
theorem lattice_adj_of_bond_eq {e : Bond d} {x y : Vertex d}
    (he : (e : Sym2 (Vertex d)) = s(x, y)) : (nearestNeighborGraph d).Adj x y := by
  obtain ⟨a, b, hab, h1⟩ := e.2
  rw [he, Sym2.eq_iff] at hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact lattice_adj_iff_l1Dist.mpr h1
  · exact (lattice_adj_iff_l1Dist.mpr h1).symm

/-- The bond of two adjacent vertices is the bond with these endpoints. -/
theorem bondOfAdjacent_eq_of_val {e : Bond d} {x y : Vertex d}
    (h : (nearestNeighborGraph d).Adj x y) (he : (e : Sym2 (Vertex d)) = s(x, y)) :
    bondOfAdjacent h = e :=
  Subtype.ext (by rw [he]; rfl)

/-- The inclusion of the cluster `C`, with the edge `{x, y}` deleted, into the open graph of the
environment in which the bond `e = {x, y}` is closed. -/
def deletedBridgeHom {ω : Configuration d} (C : OpenComponent ω) (e : Bond d) (x y : C)
    (he : (e : Sym2 (Vertex d)) = s(x.val, y.val)) :
    (componentGraph C).deleteEdges (({s(x, y)} : Finset (Sym2 C)) : Set (Sym2 C)) →g
      openGraph (closeBonds {e} ω) where
  toFun := Subtype.val
  map_rel' := by
    intro a b hab
    rw [SimpleGraph.deleteEdges_adj] at hab
    obtain ⟨⟨h, ho⟩, hne⟩ := hab
    refine ⟨h, ?_⟩
    have hb : bondOfAdjacent h ≠ e := by
      intro hbe
      apply hne
      rw [Finset.coe_singleton, Set.mem_singleton_iff]
      apply Sym2.map.injective Subtype.val_injective
      have hval := congrArg Subtype.val hbe
      rw [he] at hval
      rw [Sym2.map_mk, Sym2.map_mk]
      exact hval
    unfold closeBonds
    split_ifs with h'
    · exact absurd (Finset.mem_singleton.mp h') hb
    · exact ho

/-- Zero gradient across a bridge whose side containing `x` is finite. -/
theorem eq_of_bridge_side_finite {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ)
    (hu : ∀ x, componentLaplacian C u x = 0) (e : Bond d) (x y : C)
    (he : (e : Sym2 (Vertex d)) = s(x.val, y.val)) (hωe : ω e = true)
    (hsep : ¬ (openGraph (closeBonds {e} ω)).Reachable x.val y.val)
    (hfin : ((openGraph (closeBonds {e} ω)).connectedComponentMk x.val).supp.Finite) :
    u x = u y := by
  have hlat := lattice_adj_of_bond_eq he
  have hadj : (componentGraph C).Adj x y :=
    ⟨hlat, by convert hωe using 2; exact bondOfAdjacent_eq_of_val _ he⟩
  let φ := deletedBridgeHom C e x y he
  refine Network.eq_of_harmonic_finite_deleted_component (componentGraph C) hadj ?_
    (fun h => hsep (h.map φ)) u fun z => by rw [← componentLaplacian_eq_netLaplacian]; exact hu z
  refine (hfin.preimage Subtype.val_injective.injOn).subset fun b hb => ?_
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hb
  rw [Set.mem_preimage, SimpleGraph.ConnectedComponent.mem_supp_iff]
  exact SimpleGraph.ConnectedComponent.sound
    ((SimpleGraph.ConnectedComponent.exact hb).map φ)

/-- `step:3.2-bridge-flux`. -/
theorem bridgeFluxStep : BridgeFluxStep d := by
  intro ω C u hu e x y he hωe huniq hsep
  by_cases hx : ((openGraph (closeBonds {e} ω)).connectedComponentMk x.val).supp.Finite
  · exact eq_of_bridge_side_finite C u hu e x y he hωe hsep hx
  · have hy : ((openGraph (closeBonds {e} ω)).connectedComponentMk y.val).supp.Finite := by
      by_contra hy
      obtain ⟨D, -, hD⟩ := huniq
      exact hsep (SimpleGraph.ConnectedComponent.exact ((hD _ hx).trans (hD _ hy).symm))
    exact (eq_of_bridge_side_finite C u hu e y x (by rw [he, Sym2.eq_swap]) hωe
      (fun h => hsep h.symm) hy).symm

end Rigidity.Proofs.S3
