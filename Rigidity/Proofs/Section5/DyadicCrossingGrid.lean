import Rigidity.Proofs.Section5.PlanarGridRenormalized
import Rigidity.Proofs.Section5.StripIntersections

/-!
# Intersections in dyadic renormalized crossing grids

At large dyadic scales, the disjoint horizontal and vertical site crossings form an intersecting
grid of open renormalized sites.
-/

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Steps.Section5
  Rigidity.Section5 Percolation.Literature

namespace Rigidity.Proofs.Section5.Kesten

/-- The first coordinate of each dyadic horizontal strip start is zero. -/
theorem dyadicStripStarts_fst_eq_zero {j : ℕ} {a : PlanarCarrier} (ha : a ∈ dyadicStripStarts j) :
    a.1 = 0 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
  rfl

/-- Almost surely, at every large dyadic scale each horizontal strip and each vertical strip
have disjoint open crossings, and every horizontal crossing meets every vertical crossing. -/
theorem ae_eventually_dyadic_crossing_grid {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∀ᶠ R : ℕ in atTop, ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ᶠ j : ℕ in atTop,
      0 < (j + 1) / 2 ∧
      ∃ H V : dyadicStripStarts j → Finset (List (LatticeModels.Site 2)),
        (∀ a : dyadicStripStarts j, Menger.IsLinkage
            (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField a (renormField R ω)))
              (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
            (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) (H a) ∧
          (H a).card = (j + 1) / 2) ∧
        (∀ b : dyadicStripStarts j, Menger.IsLinkage
            (Menger.edgesIn (planarOpenSiteGraph
              (translatePlanarField b (swapPlanarField (renormField R ω))))
              (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
            (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) (V b) ∧
          (V b).card = (j + 1) / 2) ∧
        ∀ (a b : dyadicStripStarts j), ∀ h ∈ H a, ∀ v ∈ V b,
          ∃ z ∈ h.map (translateLatticeSite a), z ∈ v.map (swapTranslateLatticeSite b) := by
  classical
  filter_upwards [ae_eventually_dyadic_square_strip_crossings hpc] with R hR
  filter_upwards [hR] with ω hω
  filter_upwards [hω, eventually_ge_atTop 1] with j hj hj1
  have hH : ∀ a : dyadicStripStarts j, ∃ H : Finset (List (LatticeModels.Site 2)),
      Menger.IsLinkage
        (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField a (renormField R ω)))
          (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
        (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) H ∧
      H.card = (j + 1) / 2 := fun a => not_not.1 (hj.1 a a.2)
  have hV : ∀ b : dyadicStripStarts j, ∃ V : Finset (List (LatticeModels.Site 2)),
      Menger.IsLinkage
        (Menger.edgesIn (planarOpenSiteGraph
          (translatePlanarField b (swapPlanarField (renormField R ω))))
          (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
        (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) V ∧
      V.card = (j + 1) / 2 := fun b => not_not.1 (hj.2 b b.2)
  choose H hH hHcard using hH
  choose V hV hVcard using hV
  refine ⟨by omega, H, V, (fun a => ⟨hH a, hHcard a⟩), (fun b => ⟨hV b, hVcard b⟩), ?_⟩
  intro a b h hh v hv
  have ha0 := dyadicStripStarts_fst_eq_zero a.2
  have hb0 := dyadicStripStarts_fst_eq_zero b.2
  obtain ⟨ha1, hatop⟩ := dyadicStripStarts_vertical_bound a.2
  obtain ⟨hb1, hbtop⟩ := dyadicStripStarts_vertical_bound b.2
  exact translated_strip_crossings_intersect ha0 ha1 hatop hb0 hb1 hbtop
    ((hH a).1 h hh).1 ((hV b).1 v hv).1

end Rigidity.Proofs.Section5.Kesten
