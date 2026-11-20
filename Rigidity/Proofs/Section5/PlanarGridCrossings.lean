import Rigidity.Proofs.Section5.PlanarFieldTranslation

/-!
# Almost-sure strip crossings

Summable bounds for families of rectangles yield simultaneous crossings at all large scales.
-/

open MeasureTheory Filter LatticeProb.Percolation Percolation.Literature

namespace Rigidity.Proofs.Section5

/-- Failure to find the specified number of disjoint horizontal open site crossings. -/
def disjointCrossingFailure (m n k : ℕ) : Set (PlanarCarrier → Bool) :=
  {η | ¬∃ L : Finset (List (LatticeModels.Site 2)), Menger.IsLinkage
    (Menger.edgesIn (planarOpenSiteGraph η) (Finset.finite_toSet (rectangle m n)))
    (↑(leftSide m n)) (↑(rightSide m n)) L ∧ L.card = k}

/-- Almost surely, all rectangles in both orientations have the prescribed disjoint crossings
at every sufficiently large scale whenever their union bounds are summable. -/
theorem ae_eventually_disjoint_crossings_in_strips {ν : Measure (PlanarCarrier → Bool)}
    [IsProbabilityMeasure ν] (hν : KDependentPlanar 1 ν)
    (hcl : ∀ z, ν {η | η z = false} ≤ ENNReal.ofReal ((1 / 144 : ℝ) ^ 18))
    (T : ℕ → Finset PlanarCarrier) (m n k : ℕ → ℕ)
    (hm : ∀ j, 0 < m j) (hn : ∀ j, 0 < n j) (hk : ∀ j, 2 * k j ≤ n j)
    (hs : Summable fun j => 4 * ((T j).card : ℝ) * (m j + 1 : ℝ) * (1 / 8 : ℝ) ^ n j) :
    ∀ᵐ η ∂ν, ∀ᶠ j : ℕ in atTop,
      (∀ a ∈ T j, translatePlanarField a η ∉ disjointCrossingFailure (m j) (n j) (k j)) ∧
      ∀ a ∈ T j, translatePlanarField a (swapPlanarField η) ∉
        disjointCrossingFailure (m j) (n j) (k j) := by
  let B : ℕ → Set (PlanarCarrier → Bool) := fun j =>
    ⋃ a ∈ T j, translatePlanarField a ⁻¹' disjointCrossingFailure (m j) (n j) (k j)
  let f : ℕ → ℝ := fun j => 4 * ((T j).card : ℝ) * (m j + 1 : ℝ) * (1 / 8 : ℝ) ^ n j
  have hfinite : (∑' j, ENNReal.ofReal (f j)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hs]
    exact ENNReal.ofReal_ne_top
  have hsum : (∑' j, ν (B j)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfinite (ENNReal.tsum_le_tsum fun j => ?_)
    exact measure_exists_no_disjoint_crossings_translate_le hν hcl (T j) (m j) (n j) (k j)
      (hm j) (hn j) (hk j)
  have hsum' : (∑' j, ν (swapPlanarField ⁻¹' B j)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfinite (ENNReal.tsum_le_tsum fun j => ?_)
    exact measure_exists_no_disjoint_crossings_swap_translate_le hν hcl (T j) (m j) (n j) (k j)
      (hm j) (hn j) (hk j)
  filter_upwards [ae_eventually_notMem hsum, ae_eventually_notMem hsum'] with η hη hη'
  filter_upwards [hη, hη'] with j hj hj'
  constructor <;> intro a ha hbad
  · exact hj (Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨ha, hbad⟩⟩)
  · exact hj' (Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨ha, hbad⟩⟩)

end Rigidity.Proofs.Section5
