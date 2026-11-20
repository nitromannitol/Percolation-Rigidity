import Rigidity.Proofs.Section5.SiteRectangleDuality

/-!
# Disjoint site crossings of rectangles

Small separators of open horizontal crossings force sparse vertical star connections.
-/

open MeasureTheory Percolation.Literature Rigidity.Steps.Section5 LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

/-- The nearest-neighbor lattice graph restricted to open sites. -/
def planarOpenSiteGraph (η : PlanarCarrier → Bool) : SimpleGraph (LatticeModels.Site 2) where
  Adj x y := (LatticeModels.zdGraph 2).Adj x y ∧ η (x 0, x 1) = true ∧ η (y 0, y 1) = true
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- The open sites of a horizontal rectangle separator together with all closed sites separate
all horizontal lattice walks in the rectangle. -/
theorem rectangle_separator_with_closed_sites (m n : ℕ) (η : PlanarCarrier → Bool)
    (T : Finset (LatticeModels.Site 2))
    (hT : Menger.Separates
      (Menger.edgesIn (planarOpenSiteGraph η) (Finset.finite_toSet (rectangle m n)))
      (↑(leftSide m n)) (↑(rightSide m n)) (↑T)) :
    Menger.Separates
      (Menger.edgesIn (LatticeModels.zdGraph 2) (Finset.finite_toSet (rectangle m n)))
      (↑(leftSide m n)) (↑(rightSide m n))
      {x | η (x 0, x 1) = false ∨ x ∈ T} := by
  classical
  intro l hl
  by_contra hnone
  have hav : ∀ x ∈ l, η (x 0, x 1) = true ∧ x ∉ T := by
    intro x hx
    have h := fun h => hnone ⟨x, hx, h⟩
    have hopen : η (x 0, x 1) = true := by
      cases hh : η (x 0, x 1) <;> simp_all
    exact ⟨hopen, fun hxT => h (Or.inr hxT)⟩
  have hl' : Menger.IsLinkWalk
      (Menger.edgesIn (planarOpenSiteGraph η) (Finset.finite_toSet (rectangle m n)))
      (↑(leftSide m n)) (↑(rightSide m n)) l := by
    refine ⟨hl.1.imp_of_mem_imp ?_, hl.2⟩
    intro x y hx hy he
    obtain ⟨hxy, hxR, hyR⟩ := Menger.mem_edgesIn.1 he
    exact Menger.mem_edgesIn.2 ⟨⟨hxy, (hav x hx).1, (hav y hy).1⟩, hxR, hyR⟩
  obtain ⟨x, hx, hxT⟩ := hT l hl'
  exact (hav x hx).2 hxT

/-- Failure of `k` disjoint open left-to-right paths has exponentially small probability
when the rectangle height is at least `2k`. -/
theorem measure_no_disjoint_open_crossings_le {ν : Measure (PlanarCarrier → Bool)}
    [IsProbabilityMeasure ν] (hν : KDependentPlanar 1 ν)
    (hcl : ∀ z, ν {η | η z = false} ≤ ENNReal.ofReal ((1 / 144 : ℝ) ^ 18))
    (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 2 * k ≤ n) :
    ν {η | ¬∃ L : Finset (List (LatticeModels.Site 2)),
      Menger.IsLinkage
        (Menger.edgesIn (planarOpenSiteGraph η) (Finset.finite_toSet (rectangle m n)))
        (↑(leftSide m n)) (↑(rightSide m n)) L ∧ L.card = k} ≤
      ENNReal.ofReal (4 * (((topSide m n).image (fun x => (x 0, x 1))).card : ℝ) *
        (1 / 8 : ℝ) ^ n) := by
  classical
  let U := (topSide m n).image (fun x => (x 0, x 1))
  apply (measure_mono ?_).trans (measure_exists_star_connection_with_exceptions_le hν hcl U hn)
  rintro η hno
  let E := Menger.edgesIn (planarOpenSiteGraph η) (Finset.finite_toSet (rectangle m n))
  have hsmall : ∃ T : Finset (LatticeModels.Site 2),
      Menger.Separates E (↑(leftSide m n)) (↑(rightSide m n)) (↑T) ∧ T.card < k := by
    by_contra hnone
    apply hno
    apply Menger.exists_linkage E (↑(leftSide m n)) (↑(rightSide m n)) k
    intro T hT
    by_contra hle
    exact hnone ⟨T, hT, Nat.lt_of_not_ge hle⟩
  obtain ⟨T, hT, hTk⟩ := hsmall
  let F := T.image (fun x => (x 0, x 1))
  let A : Set PlanarCarrier := {z | η z = false} ∪ ↑F
  have hsep : Menger.Separates
      (Menger.edgesIn (LatticeModels.zdGraph 2) (Finset.finite_toSet (rectangle m n)))
      (↑(leftSide m n)) (↑(rightSide m n)) {x | (x 0, x 1) ∈ A} := by
    intro l hl
    obtain ⟨x, hx, hxA⟩ := rectangle_separator_with_closed_sites m n η T hT l hl
    refine ⟨x, hx, ?_⟩
    rcases hxA with hclosed | hT'
    · exact Or.inl hclosed
    · exact Or.inr (Finset.mem_image.2 ⟨x, hT', rfl⟩)
  obtain ⟨x, y, hx, hx1, hxA, hyA, hxy, hconn⟩ :=
    star_connection_of_rectangle_separator m n hm A hsep
  refine ⟨F, (x 0, x 1), ?_, (y 0, y 1), ?_, hxy, hconn⟩
  · exact Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨hx, hx1⟩, rfl⟩
  · have hcard : F.card ≤ T.card := Finset.card_image_le
    omega

end Rigidity.Proofs.Section5
