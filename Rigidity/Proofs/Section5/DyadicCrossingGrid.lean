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

/-- The number of dyadic strips is the integer quotient of side length by strip spacing. -/
theorem card_dyadicStripStarts (j : ℕ) : (dyadicStripStarts j).card = 2 ^ j / (j + 2) := by
  classical
  rw [dyadicStripStarts, Finset.card_image_of_injective, Finset.card_range]
  intro a b h
  have hs := congrArg Prod.snd h
  have hs' : (a : ℤ) * (j + 2) = (b : ℤ) * (j + 2) := hs
  have hj : (j : ℤ) + 2 ≠ 0 := by omega
  exact_mod_cast (mul_right_cancel₀ hj hs')

/-- Every dyadic square of side length at least four contains one of the chosen strips. -/
theorem dyadicStripStarts_nonempty {j : ℕ} (hj : 2 ≤ j) : (dyadicStripStarts j).Nonempty := by
  have hp : ∀ n : ℕ, 2 ≤ n → n + 2 ≤ 2 ^ n := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases hn' : 2 ≤ n
      · have h := ih hn'
        rw [pow_succ]
        omega
      · have : n = 1 := by omega
        subst n
        norm_num
  apply Finset.card_pos.1
  rw [card_dyadicStripStarts]
  exact Nat.div_pos (hp j hj) (by omega)

/-- The lower-left corner of the dyadic square centered at the origin. -/
def dyadicCenteredOffset (j : ℕ) : PlanarCarrier :=
  (-((2 ^ j / 2 : ℕ) : ℤ), -((2 ^ j / 2 : ℕ) : ℤ))

/-- Strip starting points in the dyadic square centered at the origin. -/
def dyadicCenteredStarts (j : ℕ) : Finset PlanarCarrier :=
  (dyadicStripStarts j).image fun a => dyadicCenteredOffset j + a

/-- The centered dyadic strip family has at most `2^j` members. -/
theorem card_dyadicCenteredStarts_le (j : ℕ) : (dyadicCenteredStarts j).card ≤ 2 ^ j :=
  Finset.card_image_le.trans (card_dyadicStripStarts_le j)

/-- Field translations compose in the same order as their displacements. -/
theorem translatePlanarField_translate (a b : PlanarCarrier) (η : PlanarCarrier → Bool) :
    translatePlanarField a (translatePlanarField b η) = translatePlanarField (b + a) η := by
  funext z
  simp only [translatePlanarField, add_assoc]

/-- Coordinate exchange commutes with translation by a diagonal displacement. -/
theorem swapPlanarField_translate_diagonal (b : PlanarCarrier) (hb : b.1 = b.2)
    (η : PlanarCarrier → Bool) :
    swapPlanarField (translatePlanarField b η) = translatePlanarField b (swapPlanarField η) := by
  funext z
  change η (b + Prod.swap z) = η (Prod.swap (b + z))
  congr 1
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_swap, Prod.snd_swap] <;> omega

/-- At large block scales, every strip in each sufficiently large centered dyadic square has
many disjoint crossings in both orientations, almost surely. -/
theorem ae_eventually_centered_dyadic_strips {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∀ᶠ R : ℕ in atTop, ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ᶠ j : ℕ in atTop,
      (∀ a ∈ dyadicCenteredStarts j, translatePlanarField a (renormField R ω) ∉
        disjointCrossingFailure (2 ^ j) (j + 1) ((j + 1) / 2)) ∧
      ∀ a ∈ dyadicCenteredStarts j, translatePlanarField a (swapPlanarField (renormField R ω)) ∉
        disjointCrossingFailure (2 ^ j) (j + 1) ((j + 1) / 2) := by
  filter_upwards [ae_eventually_planar_renormalized_dyadic_strip_crossings hpc] with R hR
  apply hR dyadicCenteredStarts (fun j => 2 ^ j) (fun j => j + 1) (fun j => (j + 1) / 2)
  · intro j
    positivity
  · intro j
    omega
  · intro j
    omega
  · exact card_dyadicCenteredStarts_le
  · intro j
    exact le_rfl
  · intro j
    omega

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

/-- Almost surely, every sufficiently large centered dyadic square contains coherent horizontal
and vertical families of disjoint open site crossings, with every perpendicular pair meeting.
The crossing coordinates are expressed relative to the square's lower-left corner. -/
theorem ae_eventually_centered_dyadic_crossing_grid {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∀ᶠ R : ℕ in atTop, ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ᶠ j : ℕ in atTop,
      0 < (j + 1) / 2 ∧
      ∃ H V : dyadicStripStarts j → Finset (List (LatticeModels.Site 2)),
        (∀ a : dyadicStripStarts j, Menger.IsLinkage
            (Menger.edgesIn (planarOpenSiteGraph
              (translatePlanarField a (translatePlanarField (dyadicCenteredOffset j) (renormField R ω))))
              (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
            (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) (H a) ∧
          (H a).card = (j + 1) / 2) ∧
        (∀ b : dyadicStripStarts j, Menger.IsLinkage
            (Menger.edgesIn (planarOpenSiteGraph
              (translatePlanarField b (swapPlanarField
                (translatePlanarField (dyadicCenteredOffset j) (renormField R ω)))))
              (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
            (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) (V b) ∧
          (V b).card = (j + 1) / 2) ∧
        ∀ (a b : dyadicStripStarts j), ∀ h ∈ H a, ∀ v ∈ V b,
          ∃ z ∈ h.map (translateLatticeSite a), z ∈ v.map (swapTranslateLatticeSite b) := by
  classical
  filter_upwards [ae_eventually_centered_dyadic_strips hpc] with R hR
  filter_upwards [hR] with ω hω
  filter_upwards [hω, eventually_ge_atTop 1] with j hj hj1
  have hH : ∀ a : dyadicStripStarts j, ∃ H : Finset (List (LatticeModels.Site 2)),
      Menger.IsLinkage
        (Menger.edgesIn (planarOpenSiteGraph
          (translatePlanarField a (translatePlanarField (dyadicCenteredOffset j) (renormField R ω))))
          (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
        (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) H ∧
      H.card = (j + 1) / 2 := by
    intro a
    rw [translatePlanarField_translate]
    apply not_not.1
    apply hj.1
    exact Finset.mem_image.2 ⟨a, a.2, rfl⟩
  have hV : ∀ b : dyadicStripStarts j, ∃ V : Finset (List (LatticeModels.Site 2)),
      Menger.IsLinkage
        (Menger.edgesIn (planarOpenSiteGraph
          (translatePlanarField b (swapPlanarField
            (translatePlanarField (dyadicCenteredOffset j) (renormField R ω)))))
          (Finset.finite_toSet (rectangle (2 ^ j) (j + 1))))
        (↑(leftSide (2 ^ j) (j + 1))) (↑(rightSide (2 ^ j) (j + 1))) V ∧
      V.card = (j + 1) / 2 := by
    intro b
    rw [swapPlanarField_translate_diagonal _ (by rfl), translatePlanarField_translate]
    apply not_not.1
    apply hj.2
    exact Finset.mem_image.2 ⟨b, b.2, rfl⟩
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
