import Rigidity.Proofs.Section5.PlanarSiteIsometries

/-!
# Families of lifted crossings

Disjoint site crossings lift simultaneously to short lattice paths with bounded congestion.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5 Percolation.Literature

namespace Rigidity.Proofs.Section5.Kesten

/-- A finite linkage of site crossings lifts to self-avoiding lattice paths so that each
lattice vertex belongs to at most nine lifted paths. -/
theorem linkage_lifts_with_bounded_congestion {ω : Configuration 2} {R m n : ℕ}
    (hR : 3210 ≤ R) (hm : 0 < m) (η : PlanarCarrier → Bool)
    (φ : siteOpenGraph η →g siteOpenGraph (renormField R ω))
    (hφ : ∀ z, η z = true → renormField R ω (φ z) = true)
    (hinj : Function.Injective (fun z : LatticeModels.Site 2 => φ (z 0, z 1)))
    (L : Finset (List (LatticeModels.Site 2)))
    (hL : Menger.IsLinkage
      (Menger.edgesIn (planarOpenSiteGraph η) (Finset.finite_toSet (rectangle m n)))
      (↑(leftSide m n)) (↑(rightSide m n)) L) :
    ∃ (x y : L → Vertex 2) (P : ∀ l : L, (openGraph ω).Walk (x l) (y l)),
      (∀ l : L,
        x l ∈ cubeAt (renormCentre R (φ (l.1.head (hL.1 l l.2).1.ne_nil 0,
          l.1.head (hL.1 l l.2).1.ne_nil 1))) (11 * R / 10) ∧
        y l ∈ cubeAt (renormCentre R (φ (l.1.getLast (hL.1 l l.2).1.ne_nil 0,
          l.1.getLast (hL.1 l l.2).1.ne_nil 1))) (11 * R / 10) ∧
        (P l).IsPath ∧
        (∀ z ∈ (P l).support, z ∈ renormPathRegion R (l.1.map fun a => φ (a 0, a 1))) ∧
        (P l).length < l.1.length * (2 * (11 * R / 10) + 1) ^ 2) ∧
      (∀ z : Vertex 2, (Finset.univ.filter fun l : L => z ∈ (P l).support).card ≤ 9) ∧
      ∀ a b : Vertex 2, (Finset.univ.filter fun l : L => s(a, b) ∈ (P l).edges).card ≤ 9 := by
  classical
  have hlift : ∀ l : L,
      ∃ x ∈ cubeAt (renormCentre R (φ (l.1.head (hL.1 l l.2).1.ne_nil 0,
          l.1.head (hL.1 l l.2).1.ne_nil 1))) (11 * R / 10),
        ∃ y ∈ cubeAt (renormCentre R (φ (l.1.getLast (hL.1 l l.2).1.ne_nil 0,
          l.1.getLast (hL.1 l l.2).1.ne_nil 1))) (11 * R / 10),
          ∃ P : (openGraph ω).Walk x y, P.IsPath ∧
            (∀ z ∈ P.support, z ∈ renormPathRegion R (l.1.map fun a => φ (a 0, a 1))) ∧
            P.length < l.1.length * (2 * (11 * R / 10) + 1) ^ 2 := fun l =>
    horizontal_crossing_lifts_of_site_hom hR hm η φ hφ (hL.1 l l.2).1
  choose x hx y hy P hP hsupport hlen using hlift
  refine ⟨x, y, P, fun l => ⟨hx l, hy l, hP l, hsupport l, hlen l⟩, ?_⟩
  have hv : ∀ z : Vertex 2, (Finset.univ.filter fun l : L => z ∈ (P l).support).card ≤ 9 := by
    intro z
    let S := L.filter fun l => z ∈ renormPathRegion R (l.map fun a => φ (a 0, a 1))
    have hS : S.card ≤ 9 := card_injective_path_regions_meeting_le_nine _ hinj S (by
      intro l hl l' hl' hne a ha
      exact hL.2 l (Finset.mem_filter.1 hl).1 l' (Finset.mem_filter.1 hl').1 hne a ha)
        (fun l hl => (Finset.mem_filter.1 hl).2)
    have hcard : (Finset.univ.filter fun l : L => z ∈ (P l).support).card ≤ S.card := by
      apply Finset.card_le_card_of_injOn (fun l : L => l.1)
      · intro l hl
        have hz : z ∈ (P l).support := (Finset.mem_filter.1 hl).2
        exact Finset.mem_filter.2 ⟨l.2, hsupport l z hz⟩
      · intro l _ l' _ heq
        exact Subtype.ext heq
    exact hcard.trans hS
  refine ⟨hv, fun a b => ?_⟩
  apply (Finset.card_le_card ?_).trans (hv a)
  intro l hl
  have he : s(a, b) ∈ (P l).edges := (Finset.mem_filter.1 hl).2
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (P l).fst_mem_support_of_mem_edges he⟩

end Rigidity.Proofs.Section5.Kesten
