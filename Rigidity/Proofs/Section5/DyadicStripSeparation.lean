import Rigidity.Proofs.Section5.DyadicCrossingGrid

/-!
# Separation of dyadic crossing strips

Crossings in distinct strips of the same orientation do not share sites after translation.
-/

open LatticeProb.Percolation Rigidity.Steps.Section5 Percolation.Literature

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

end Rigidity.Proofs.Section5.Kesten
