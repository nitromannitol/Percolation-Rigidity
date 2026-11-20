import Rigidity.Proofs.Section5.PlanarSiteIsometries
import Rigidity.Proofs.Section5.RectangleCrossingIntersection

/-!
# Intersections of translated strip crossings

Site-graph homomorphisms transport link walks between finite planar regions.
-/

open LatticeProb.Percolation Rigidity.Steps.Section5 Percolation.Literature

namespace Rigidity.Proofs.Section5.Kesten

/-- A site-graph homomorphism maps link walks between finite regions when it maps the region
and the endpoint sets into their targets. -/
theorem siteHom_linkWalk_map {η η' : PlanarCarrier → Bool}
    (φ : siteOpenGraph η →g siteOpenGraph η') {D D' A B A' B' : Set (LatticeModels.Site 2)}
    (hD : D.Finite) (hD' : D'.Finite) {l : List (LatticeModels.Site 2)}
    (hl : Menger.IsLinkWalk (Menger.edgesIn (planarOpenSiteGraph η) hD) A B l)
    (hregion : ∀ z ∈ D, toSite2 (φ (z 0, z 1)) ∈ D')
    (hA : ∀ z ∈ A, toSite2 (φ (z 0, z 1)) ∈ A')
    (hB : ∀ z ∈ B, toSite2 (φ (z 0, z 1)) ∈ B') :
    Menger.IsLinkWalk (Menger.edgesIn (planarOpenSiteGraph η') hD') A' B'
      (l.map fun z => toSite2 (φ (z 0, z 1))) := by
  apply linkWalk_map (fun z => toSite2 (φ (z 0, z 1))) hl ?_ hA hB
  intro a b hab
  obtain ⟨hab', haD, hbD⟩ := Menger.mem_edgesIn.1 hab
  have hp := (planarOpenSiteHom η).map_rel hab'
  have hq := φ.map_rel hp
  have hr := (siteOpenPlanarHom η').map_rel hq
  exact Menger.mem_edgesIn.2 ⟨hr, hregion a haD, hregion b hbD⟩

/-- The lattice site obtained by adding a planar displacement. -/
def translateLatticeSite (a : PlanarCarrier) (z : LatticeModels.Site 2) : LatticeModels.Site 2 :=
  toSite2 (a + (z 0, z 1))

/-- A translated horizontal strip lies inside the larger square. -/
theorem translate_strip_mem_square {M n : ℕ} {a : PlanarCarrier}
    (ha0 : a.1 = 0) (ha1 : 0 ≤ a.2) (hatop : a.2 + n ≤ M)
    {z : LatticeModels.Site 2} (hz : z ∈ rectangle M n) :
    translateLatticeSite a z ∈ rectangle M M := by
  have hz' := mem_rectangle_iff.1 hz
  apply mem_rectangle_iff.2
  simp only [translateLatticeSite, toSite2, Prod.fst_add, Prod.snd_add, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  omega

/-- A translated horizontal strip crossing is a horizontal crossing of its enclosing square. -/
theorem translated_strip_link_in_square {η : PlanarCarrier → Bool} {M n : ℕ}
    {a : PlanarCarrier} (ha0 : a.1 = 0) (ha1 : 0 ≤ a.2) (hatop : a.2 + n ≤ M)
    {l : List (LatticeModels.Site 2)}
    (hl : Menger.IsLinkWalk
      (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField a η))
        (Finset.finite_toSet (rectangle M n))) (↑(leftSide M n)) (↑(rightSide M n)) l) :
    Menger.IsLinkWalk (Menger.edgesIn (planarOpenSiteGraph η)
      (Finset.finite_toSet (rectangle M M))) (↑(leftSide M M)) (↑(rightSide M M))
        (l.map (translateLatticeSite a)) := by
  apply siteHom_linkWalk_map (translateOpenSiteHom a η) _ _ hl
  · intro z hz
    exact translate_strip_mem_square ha0 ha1 hatop hz
  · intro z hz
    obtain ⟨hzR, hzL⟩ := Finset.mem_filter.1 hz
    refine Finset.mem_filter.2 ⟨translate_strip_mem_square ha0 ha1 hatop hzR, ?_⟩
    change a.1 + z 0 = _
    omega
  · intro z hz
    obtain ⟨hzR, hzR'⟩ := Finset.mem_filter.1 hz
    refine Finset.mem_filter.2 ⟨translate_strip_mem_square ha0 ha1 hatop hzR, ?_⟩
    change a.1 + z 0 = _
    omega

/-- The lattice site obtained by translating and then exchanging axes. -/
def swapTranslateLatticeSite (a : PlanarCarrier) (z : LatticeModels.Site 2) : LatticeModels.Site 2 :=
  toSite2 (Prod.swap (a + (z 0, z 1)))

/-- A translated strip with exchanged axes lies inside the larger square. -/
theorem swap_translate_strip_mem_square {M n : ℕ} {a : PlanarCarrier}
    (ha0 : a.1 = 0) (ha1 : 0 ≤ a.2) (hatop : a.2 + n ≤ M)
    {z : LatticeModels.Site 2} (hz : z ∈ rectangle M n) :
    swapTranslateLatticeSite a z ∈ rectangle M M := by
  have hz' := mem_rectangle_iff.1 hz
  apply mem_rectangle_iff.2
  simp only [swapTranslateLatticeSite, toSite2, Prod.fst_swap, Prod.snd_swap,
    Prod.fst_add, Prod.snd_add, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

/-- A translated crossing with exchanged axes is a vertical crossing of its enclosing square. -/
theorem swapped_strip_link_in_square {η : PlanarCarrier → Bool} {M n : ℕ}
    {a : PlanarCarrier} (ha0 : a.1 = 0) (ha1 : 0 ≤ a.2) (hatop : a.2 + n ≤ M)
    {l : List (LatticeModels.Site 2)}
    (hl : Menger.IsLinkWalk
      (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField a (swapPlanarField η)))
        (Finset.finite_toSet (rectangle M n))) (↑(leftSide M n)) (↑(rightSide M n)) l) :
    Menger.IsLinkWalk (Menger.edgesIn (planarOpenSiteGraph η)
      (Finset.finite_toSet (rectangle M M))) (↑(bottomSide M M)) (↑(topSide M M))
        (l.map (swapTranslateLatticeSite a)) := by
  apply siteHom_linkWalk_map ((swapOpenSiteHom η).comp (translateOpenSiteHom a _)) _ _ hl
  · intro z hz
    exact swap_translate_strip_mem_square ha0 ha1 hatop hz
  · intro z hz
    obtain ⟨hzR, hzL⟩ := Finset.mem_filter.1 hz
    refine Finset.mem_filter.2 ⟨swap_translate_strip_mem_square ha0 ha1 hatop hzR, ?_⟩
    change a.1 + z 0 = _
    omega
  · intro z hz
    obtain ⟨hzR, hzR'⟩ := Finset.mem_filter.1 hz
    refine Finset.mem_filter.2 ⟨swap_translate_strip_mem_square ha0 ha1 hatop hzR, ?_⟩
    change a.1 + z 0 = _
    omega

/-- A horizontal translated strip crossing and a vertical translated strip crossing inside
the same square share a lattice site. -/
theorem translated_strip_crossings_intersect {η : PlanarCarrier → Bool} {M n : ℕ}
    {a b : PlanarCarrier} (ha0 : a.1 = 0) (ha1 : 0 ≤ a.2) (hatop : a.2 + n ≤ M)
    (hb0 : b.1 = 0) (hb1 : 0 ≤ b.2) (hbtop : b.2 + n ≤ M)
    {H V : List (LatticeModels.Site 2)}
    (hH : Menger.IsLinkWalk
      (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField a η))
        (Finset.finite_toSet (rectangle M n))) (↑(leftSide M n)) (↑(rightSide M n)) H)
    (hV : Menger.IsLinkWalk
      (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField b (swapPlanarField η)))
        (Finset.finite_toSet (rectangle M n))) (↑(leftSide M n)) (↑(rightSide M n)) V) :
    ∃ z ∈ H.map (translateLatticeSite a), z ∈ V.map (swapTranslateLatticeSite b) :=
  rectangle_link_crossings_intersect (translated_strip_link_in_square ha0 ha1 hatop hH)
    (swapped_strip_link_in_square hb0 hb1 hbtop hV)

end Rigidity.Proofs.Section5.Kesten
