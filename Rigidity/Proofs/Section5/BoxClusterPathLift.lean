import Rigidity.Proofs.Section5.RenormalizedPathLift
import Rigidity.Draft.Section6Statements

/-!
# Lifted paths in box clusters

An open path in a box stays in its starting box cluster. This transfers anchored renormalized
walks to the corresponding finite cluster once one anchor is known to belong to it.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Section6 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5.Kesten

/-- An open lattice walk inside a box stays in the box cluster of its initial vertex. -/
theorem walk_support_reachable_in_box {d : ℕ} {ω : Configuration d} {n : ℕ}
    {u v : Vertex d} (P : (openGraph ω).Walk u v)
    (hP : ∀ z ∈ P.support, z ∈ Rigidity.Section6.cube d n) :
    ∀ z ∈ P.support, (boxOpenGraph ω n).Reachable u z := by
  have hE : ∀ e ∈ P.edges, e ∈ (boxOpenGraph ω n).edgeSet := by
    intro e
    refine Sym2.inductionOn e ?_
    intro a b he
    have hab : (openGraph ω).Adj a b := (openGraph ω).mem_edgeSet.1 (P.edges_subset_edgeSet he)
    have ha := P.fst_mem_support_of_mem_edges he
    have hb := P.snd_mem_support_of_mem_edges he
    exact (boxOpenGraph ω n).mem_edgeSet.2 ⟨hab, hP a ha, hP b hb⟩
  let Q := P.transfer (boxOpenGraph ω n) hE
  intro z hz
  have hzQ : z ∈ Q.support := by simpa only [Q, SimpleGraph.Walk.support_transfer] using hz
  exact ⟨Q.takeUntil z hzQ⟩

/-- A box-contained open walk starting in a box cluster is entirely contained in that cluster. -/
theorem walk_support_subset_largestBoxCluster {ω : Configuration 2} {n : ℕ}
    {V : Finset (Vertex 2)} (hV : IsLargestBoxCluster ω n V) {u v : Vertex 2}
    (P : (openGraph ω).Walk u v) (hP : ∀ z ∈ P.support, z ∈ Rigidity.Section6.cube 2 n) (hu : u ∈ V) :
    ∀ z ∈ P.support, z ∈ V := by
  obtain ⟨⟨r, _, hr⟩, _⟩ := hV
  have hu' : (boxOpenGraph ω n).Reachable r u := by
    have : u ∈ (V : Set (Vertex 2)) := hu
    rw [hr] at this
    exact this
  intro z hz
  have hz' : z ∈ (V : Set (Vertex 2)) := by
    rw [hr]
    exact hu'.trans (walk_support_reachable_in_box P hP z hz)
  exact hz'

/-- If the visited blocks are inside a box and the initial anchor belongs to its largest
cluster, the lifted anchor path stays in that cluster. -/
theorem renorm_walk_lifts_in_largestBoxCluster {ω : Configuration 2} {R n : ℕ}
    (hR : 3210 ≤ R) {V : Finset (Vertex 2)} (hV : IsLargestBoxCluster ω n V)
    {u v : PlanarCarrier} (w : (siteOpenGraph (renormField R ω)).Walk u v)
    (hu : renormField R ω u = true) (hv : renormField R ω v = true)
    (huV : renormChannelAnchor hR hu ∈ V)
    (hbox : renormPathRegion R w.support ⊆ Rigidity.Section6.cube 2 n) :
    ∃ P : (openGraph ω).Walk (renormChannelAnchor hR hu) (renormChannelAnchor hR hv),
      P.IsPath ∧ (∀ z ∈ P.support, z ∈ V) ∧
      P.length < (w.length + 1) * (2 * (11 * R / 10) + 1) ^ 2 := by
  obtain ⟨P, hP, hregion, hlen⟩ := renorm_walk_lifts_anchors hR w hu hv
  refine ⟨P, hP, ?_, hlen⟩
  exact walk_support_subset_largestBoxCluster hV P (fun z hz => hbox (hregion z hz)) huV

end Rigidity.Proofs.Section5.Kesten
