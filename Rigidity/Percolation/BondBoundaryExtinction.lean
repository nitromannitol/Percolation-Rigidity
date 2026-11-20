import Rigidity.Percolation.BondSeedFaceContacts
import Rigidity.Percolation.SlabAttachmentGeometry

/-!
# Extinction by closing boundary bonds

Closing the bonds leaving the part of a finite face reached from a seed
prevents that seed from reaching any point beyond the explored region.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- If every bond leaving a reached face contact is closed, the seed cannot
reach outside the explored region through the ambient region. -/
theorem not_seed_reachable_outside_of_closed_contacts {d : ℕ} {ω : Configuration d}
    {P D : Set (Vertex d)} {roots face : Finset (Vertex d)}
    (hroots : ∀ z ∈ roots, z ∈ P)
    (hface : ∀ x ∈ P, ∀ y, y ∉ P →
      (nearestNeighborGraph d).Adj x y → x ∈ face)
    (hclosed : ∀ x ∈ seedReachableContacts P roots face ω, ∀ y,
      y ∉ P → ∀ hxy : (nearestNeighborGraph d).Adj x y,
        ω (bondOfAdjacent hxy) = false)
    {z w : Vertex d} (hz : z ∈ roots) (hw : w ∉ P)
    (hzw : (openIn ω D).Reachable z w) : False := by
  have hPS : Disjoint P Pᶜ := by
    rw [Set.disjoint_left]
    intro x hx hxnot
    exact hxnot hx
  have hDS : D ⊆ P ∪ Pᶜ := by simp only [Set.union_compl_self, Set.subset_univ]
  obtain ⟨x, hx, y, hy, hxy, hzx, hopen⟩ :=
    exists_slab_attachment_of_reachable hPS hDS (hroots z hz) hw hzw
  have hxc : x ∈ seedReachableContacts P roots face ω :=
    (mem_seedReachableContacts P roots face ω x).mpr
      ⟨hface x hx y hy hxy, z, hz, hzx⟩
  rw [hclosed x hxc y hy hxy] at hopen
  cases hopen

/-- Once the outgoing bonds from reached contacts are closed, no contact
outside the explored region can be reached from the seed. -/
theorem seedReachableContacts_eq_empty_of_closed_contacts {d : ℕ} {ω : Configuration d}
    {P D : Set (Vertex d)} {roots face outer : Finset (Vertex d)}
    (hroots : ∀ z ∈ roots, z ∈ P)
    (hface : ∀ x ∈ P, ∀ y, y ∉ P →
      (nearestNeighborGraph d).Adj x y → x ∈ face)
    (hclosed : ∀ x ∈ seedReachableContacts P roots face ω, ∀ y,
      y ∉ P → ∀ hxy : (nearestNeighborGraph d).Adj x y,
        ω (bondOfAdjacent hxy) = false)
    (houter : ∀ w ∈ outer, w ∉ P) :
    seedReachableContacts D roots outer ω = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hwouter, z, hz, hzw⟩ := (mem_seedReachableContacts D roots outer ω w).mp hw
  exact not_seed_reachable_outside_of_closed_contacts hroots hface hclosed hz
    (houter w hwouter) hzw

end Rigidity.Percolation
