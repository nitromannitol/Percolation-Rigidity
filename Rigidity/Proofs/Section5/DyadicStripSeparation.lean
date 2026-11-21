import Rigidity.Proofs.Section5.DyadicCrossingGrid

/-!
# Separation of dyadic crossing strips

Crossings in distinct strips of the same orientation do not share sites after translation.
-/

open LatticeProb.Percolation Rigidity.Steps.Section5 Percolation.Literature
open scoped Classical

namespace Rigidity.Proofs.Section5.Kesten

/-- Crossings of distinct horizontal dyadic strips have disjoint translated site lists. -/
theorem dyadic_translated_crossings_disjoint {η : PlanarCarrier → Bool} {j : ℕ}
    {a b : PlanarCarrier} (ha : a ∈ dyadicStripStarts j) (hb : b ∈ dyadicStripStarts j)
    (hne : a ≠ b) {H V : List (LatticeModels.Site 2)}
    (hH : Menger.IsLinkWalk
      (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField a η))
        (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
      (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) H)
    (hV : Menger.IsLinkWalk
      (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField b η))
        (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
      (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) V) :
    ∀ z ∈ H.map (translateLatticeSite a), z ∉ V.map (translateLatticeSite b) := by
  intro z hz hz'
  obtain ⟨x, hx, hzx⟩ := List.mem_map.1 hz
  obtain ⟨y, hy, hzy⟩ := List.mem_map.1 hz'
  have hxR : x ∈ rectangle (2 ^ j) (j + 1) :=
    linkWalk_mem_region _ (fun _ h => (Finset.mem_filter.1 h).1) hH x hx
  have hyR : y ∈ rectangle (2 ^ j) (j + 1) :=
    linkWalk_mem_region _ (fun _ h => (Finset.mem_filter.1 h).1) hV y hy
  have hxcoord := mem_rectangle_iff.1 hxR
  have hycoord := mem_rectangle_iff.1 hyR
  have heq := congrArg (fun q : LatticeModels.Site 2 => q 1) (hzx.trans hzy.symm)
  have heq' : a.2 + x 1 = b.2 + y 1 := by
    simpa only [translateLatticeSite, toSite2, Prod.snd_add, Matrix.cons_val_one,
      Matrix.cons_val_zero] using heq
  apply hne
  apply dyadicStripStarts_eq_of_overlap ha hb (t := a.2 + x 1)
  · omega
  · omega

/-- Coordinate exchange preserves disjointness of site lists. -/
theorem dyadic_swapped_crossings_disjoint {η : PlanarCarrier → Bool} {j : ℕ}
    {a b : PlanarCarrier} (ha : a ∈ dyadicStripStarts j) (hb : b ∈ dyadicStripStarts j)
    (hne : a ≠ b) {H V : List (LatticeModels.Site 2)}
    (hH : Menger.IsLinkWalk
      (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField a (swapPlanarField η)))
        (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
      (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) H)
    (hV : Menger.IsLinkWalk
      (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField b (swapPlanarField η)))
        (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
      (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) V) :
    ∀ z ∈ H.map (swapTranslateLatticeSite a), z ∉ V.map (swapTranslateLatticeSite b) := by
  intro z hz hz'
  obtain ⟨x, hx, hzx⟩ := List.mem_map.1 hz
  obtain ⟨y, hy, hzy⟩ := List.mem_map.1 hz'
  have hxR : x ∈ rectangle (2 ^ j) (j + 1) :=
    linkWalk_mem_region _ (fun _ h => (Finset.mem_filter.1 h).1) hH x hx
  have hyR : y ∈ rectangle (2 ^ j) (j + 1) :=
    linkWalk_mem_region _ (fun _ h => (Finset.mem_filter.1 h).1) hV y hy
  have hxcoord := mem_rectangle_iff.1 hxR
  have hycoord := mem_rectangle_iff.1 hyR
  have heq := congrArg (fun q : LatticeModels.Site 2 => q 0) (hzx.trans hzy.symm)
  have heq' : a.2 + x 1 = b.2 + y 1 := by
    simpa only [swapTranslateLatticeSite, toSite2, Prod.fst_swap, Prod.snd_add,
      Matrix.cons_val_zero] using heq
  apply hne
  apply dyadicStripStarts_eq_of_overlap ha hb (t := a.2 + x 1)
  · omega
  · omega

/-- All horizontal crossing paths chosen from disjoint dyadic strips are pairwise site-disjoint
after translation. -/
theorem dyadic_horizontal_grid_paths_disjoint {η : PlanarCarrier → Bool} {j : ℕ}
    (H : dyadicStripStarts j → Finset (List (LatticeModels.Site 2)))
    (hH : ∀ a : dyadicStripStarts j, Menger.IsLinkage
      (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField a η))
        (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
      (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) (H a)) :
    ∀ (i k : Σ a : dyadicStripStarts j, H a), i ≠ k → ∀ z ∈
      (i.2.1.map fun q => (i.1 : PlanarCarrier) + (q 0, q 1)), z ∉
        (k.2.1.map fun q => (k.1 : PlanarCarrier) + (q 0, q 1)) := by
  intro i k hik z hz hz'
  obtain ⟨x, hx, hzx⟩ := List.mem_map.1 hz
  obtain ⟨y, hy, hzy⟩ := List.mem_map.1 hz'
  by_cases ha : i.1 = k.1
  · have hp : i.2.1 ≠ k.2.1 := by
      intro hp
      apply hik
      cases i with
      | mk a p =>
        cases k with
        | mk b q =>
          dsimp only at ha hp
          subst b
          have heq : p = q := Subtype.ext hp
          subst q
          rfl
    have heq : (x 0, x 1) = (y 0, y 1) := by
      apply add_left_cancel (a := (i.1 : PlanarCarrier))
      simpa only [ha] using hzx.trans hzy.symm
    have hxy : x = y := LatticeModels.Site.eq_iff_two.2
      ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
    subst y
    have hdis := (hH i.1).2 i.2.1 i.2.2 k.2.1 (by simpa only [ha] using k.2.2) hp x hx
    exact hdis hy
  · have ha' : (i.1 : PlanarCarrier) ≠ (k.1 : PlanarCarrier) := fun h => ha (Subtype.ext h)
    have hdis := dyadic_translated_crossings_disjoint i.1.2 k.1.2 ha'
      ((hH i.1).1 i.2.1 i.2.2).1 ((hH k.1).1 k.2.1 k.2.2).1
    apply hdis (toSite2 z)
    · exact List.mem_map.2 ⟨x, hx, congrArg toSite2 hzx⟩
    · exact List.mem_map.2 ⟨y, hy, congrArg toSite2 hzy⟩

/-- A common translation preserves disjointness of all horizontal grid paths. -/
theorem dyadic_horizontal_grid_paths_disjoint_offset {η : PlanarCarrier → Bool} {j : ℕ}
    (c : PlanarCarrier) (H : dyadicStripStarts j → Finset (List (LatticeModels.Site 2)))
    (hH : ∀ a : dyadicStripStarts j, Menger.IsLinkage
      (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField a η))
        (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
      (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) (H a)) :
    ∀ (i k : Σ a : dyadicStripStarts j, H a), i ≠ k → ∀ z ∈
      (i.2.1.map fun q => c + ((i.1 : PlanarCarrier) + (q 0, q 1))), z ∉
        (k.2.1.map fun q => c + ((k.1 : PlanarCarrier) + (q 0, q 1))) := by
  intro i k hik z hz hz'
  obtain ⟨x, hx, hzx⟩ := List.mem_map.1 hz
  obtain ⟨y, hy, hzy⟩ := List.mem_map.1 hz'
  have heq : (i.1 : PlanarCarrier) + (x 0, x 1) = (k.1 : PlanarCarrier) + (y 0, y 1) :=
    add_left_cancel (hzx.trans hzy.symm)
  apply dyadic_horizontal_grid_paths_disjoint H hH i k hik ((i.1 : PlanarCarrier) + (x 0, x 1))
  · exact List.mem_map.2 ⟨x, hx, rfl⟩
  · exact List.mem_map.2 ⟨y, hy, heq.symm⟩

/-- Across all horizontal strips, at most nine crossing regions contain a fixed lattice
vertex, including after a common translation of the grid. -/
theorem card_dyadic_horizontal_regions_le_nine {η : PlanarCarrier → Bool} {j R : ℕ}
    (c : PlanarCarrier) (H : dyadicStripStarts j → Finset (List (LatticeModels.Site 2)))
    (hH : ∀ a : dyadicStripStarts j, Menger.IsLinkage
      (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField a η))
        (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
      (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) (H a))
    (I : Finset (Σ a : dyadicStripStarts j, H a)) (x : Vertex 2) :
    (I.filter fun i => x ∈ renormPathRegion R
      (i.2.1.map fun q => c + ((i.1 : PlanarCarrier) + (q 0, q 1)))).card ≤ 9 := by
  apply card_disjoint_indexed_regions_meeting_le_nine _
    (fun i => i.2.1.map fun q => c + ((i.1 : PlanarCarrier) + (q 0, q 1)))
  · intro i hi k hk hik z hz
    exact dyadic_horizontal_grid_paths_disjoint_offset c H hH i k hik z hz
  · intro i hi
    exact (Finset.mem_filter.1 hi).2

/-- A common translation preserves disjointness of all vertical grid paths. -/
theorem dyadic_vertical_grid_paths_disjoint_offset {η : PlanarCarrier → Bool} {j : ℕ}
    (c : PlanarCarrier) (V : dyadicStripStarts j → Finset (List (LatticeModels.Site 2)))
    (hV : ∀ a : dyadicStripStarts j, Menger.IsLinkage
      (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField a (swapPlanarField η)))
        (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
      (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) (V a)) :
    ∀ (i k : Σ a : dyadicStripStarts j, V a), i ≠ k → ∀ z ∈
      (i.2.1.map fun q => c + Prod.swap ((i.1 : PlanarCarrier) + (q 0, q 1))), z ∉
        (k.2.1.map fun q => c + Prod.swap ((k.1 : PlanarCarrier) + (q 0, q 1))) := by
  intro i k hik z hz hz'
  obtain ⟨x, hx, hzx⟩ := List.mem_map.1 hz
  obtain ⟨y, hy, hzy⟩ := List.mem_map.1 hz'
  have heq : (i.1 : PlanarCarrier) + (x 0, x 1) = (k.1 : PlanarCarrier) + (y 0, y 1) :=
    Prod.swap_injective (add_left_cancel (hzx.trans hzy.symm))
  apply dyadic_horizontal_grid_paths_disjoint V hV i k hik ((i.1 : PlanarCarrier) + (x 0, x 1))
  · exact List.mem_map.2 ⟨x, hx, rfl⟩
  · exact List.mem_map.2 ⟨y, hy, heq.symm⟩

/-- Across all vertical strips, at most nine crossing regions contain a fixed lattice vertex. -/
theorem card_dyadic_vertical_regions_le_nine {η : PlanarCarrier → Bool} {j R : ℕ}
    (c : PlanarCarrier) (V : dyadicStripStarts j → Finset (List (LatticeModels.Site 2)))
    (hV : ∀ a : dyadicStripStarts j, Menger.IsLinkage
      (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField a (swapPlanarField η)))
        (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
      (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) (V a))
    (I : Finset (Σ a : dyadicStripStarts j, V a)) (x : Vertex 2) :
    (I.filter fun i => x ∈ renormPathRegion R
      (i.2.1.map fun q => c + Prod.swap ((i.1 : PlanarCarrier) + (q 0, q 1)))).card ≤ 9 := by
  apply card_disjoint_indexed_regions_meeting_le_nine _
    (fun i => i.2.1.map fun q => c + Prod.swap ((i.1 : PlanarCarrier) + (q 0, q 1)))
  · intro i hi k hk hik z hz
    exact dyadic_vertical_grid_paths_disjoint_offset c V hV i k hik z hz
  · intro i hi
    exact (Finset.mem_filter.1 hi).2

/-- At most eighteen horizontal or vertical crossing regions of a translated dyadic grid
contain a given lattice vertex. -/
theorem card_dyadic_grid_regions_le_eighteen {η : PlanarCarrier → Bool} {j R : ℕ}
    (c : PlanarCarrier)
    (H V : dyadicStripStarts j → Finset (List (LatticeModels.Site 2)))
    (hH : ∀ a : dyadicStripStarts j, Menger.IsLinkage
      (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField a η))
        (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
      (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) (H a))
    (hV : ∀ a : dyadicStripStarts j, Menger.IsLinkage
      (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField a (swapPlanarField η)))
        (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
      (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) (V a))
    (I : Finset (Σ a : dyadicStripStarts j, H a))
    (J : Finset (Σ a : dyadicStripStarts j, V a)) (x : Vertex 2) :
    (I.filter fun i => x ∈ renormPathRegion R
      (i.2.1.map fun q => c + ((i.1 : PlanarCarrier) + (q 0, q 1)))).card +
    (J.filter fun i => x ∈ renormPathRegion R
      (i.2.1.map fun q => c + Prod.swap ((i.1 : PlanarCarrier) + (q 0, q 1)))).card ≤ 18 := by
  have h₁ := card_dyadic_horizontal_regions_le_nine (R := R) c H hH I x
  have h₂ := card_dyadic_vertical_regions_le_nine (R := R) c V hV J x
  omega

end Rigidity.Proofs.Section5.Kesten
