import Rigidity.Proofs.Percolation.PlanarCriticalUpper
import Rigidity.Proofs.Percolation.ClusterComparison

/-!
# Planar site paths and bond paths

Every nearest-neighbor path of good sites gives an open bond path.
-/

open MeasureTheory LatticeProb.Percolation

noncomputable section

namespace Rigidity.Percolation

open Rigidity.Steps.Section5

/-- A good site has both outgoing bonds open. -/
theorem outgoingBond_open_of_good (ω : Configuration 2) (z : PlanarCarrier)
    (hz : outgoingField ω z = true) (i : Fin 2) : ω (outgoingBond z i) = true := by
  have h : ∀ i : Fin 2, ω (outgoingBond z i) = true := by
    simpa only [outgoingField, decide_eq_true_eq] using hz
  exact h i

/-- A good-site edge maps to an open bond edge. -/
theorem outgoing_site_adj (ω : Configuration 2) {z w : PlanarCarrier}
    (h : (siteOpenGraph (outgoingField ω)).Adj z w) :
    (LatticeProb.Percolation.openGraph ω).Adj (toSite2 z) (toSite2 w) := by
  have hadj : (nearestNeighborGraph 2).Adj (toSite2 z) (toSite2 w) := by
    apply lattice_adj_iff_l1Dist.mpr
    simpa [latticeL1Dist, Fin.sum_univ_two, toSite2] using h.1
  refine ⟨hadj, ?_⟩
  have ha := hadj
  obtain ⟨i, hi | hi⟩ := ha
  · have he : bondOfAdjacent hadj = outgoingBond z i := by
      apply Subtype.ext
      change s(toSite2 z, toSite2 w) = s(toSite2 z, toSite2 z + LatticeProb.unit i)
      rw [hi]
    rw [he]
    exact outgoingBond_open_of_good ω z h.2.1 i
  · have he : bondOfAdjacent hadj = outgoingBond w i := by
      apply Subtype.ext
      change s(toSite2 z, toSite2 w) = s(toSite2 w, toSite2 w + LatticeProb.unit i)
      rw [hi]
      exact Sym2.eq_swap
    rw [he]
    exact outgoingBond_open_of_good ω w h.2.2 i

/-- An infinite good-site cluster gives an infinite bond cluster at the corresponding vertex. -/
theorem infiniteComponent_of_outgoingSite (ω : Configuration 2) (z : PlanarCarrier)
    (hz : InInfiniteSiteCluster (outgoingField ω) z) :
    ω ∈ infiniteComponentEvent (toSite2 z) := by
  let φ : siteOpenGraph (outgoingField ω) →g LatticeProb.Percolation.openGraph ω :=
    { toFun := toSite2
      map_rel' := fun {_ _} h => outgoing_site_adj ω h }
  change ((LatticeProb.Percolation.openGraph ω).connectedComponentMk (toSite2 z)).supp.Infinite
  rw [component_supp_eq_cluster]
  have hi : (toSite2 '' {w | (siteOpenGraph (outgoingField ω)).Reachable z w}).Infinite :=
    hz.2.image planarSiteEquiv.injective.injOn
  refine hi.mono ?_
  rintro _ ⟨w, hw, rfl⟩
  exact hw.map φ

end Rigidity.Percolation
