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

/-- The strip failure bounds are summable when the number of strips and their lengths grow
at most as `2^j` and their widths are at least `j`. -/
theorem summable_dyadic_strip_bounds (T : ℕ → Finset PlanarCarrier) (m n : ℕ → ℕ)
    (hT : ∀ j, (T j).card ≤ 2 ^ j) (hm : ∀ j, m j ≤ 2 ^ j)
    (hn : ∀ j, j ≤ n j) :
    Summable fun j => 4 * ((T j).card : ℝ) * (m j + 1 : ℝ) * (1 / 8 : ℝ) ^ n j := by
  have hg : Summable (fun j : ℕ => 8 * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left 8
  apply Summable.of_nonneg_of_le (fun j => by positivity) ?_ hg
  intro j
  have hT' : ((T j).card : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hT j
  have hm' : (m j : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hm j
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hn' : (1 / 8 : ℝ) ^ n j ≤ (1 / 8 : ℝ) ^ j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (hn j)
  calc
    _ ≤ 4 * (2 : ℝ) ^ j * (2 * (2 : ℝ) ^ j) * (1 / 8 : ℝ) ^ j := by
      gcongr
      linarith
    _ = 8 * (((2 : ℝ) ^ j * 2 ^ j) * (1 / 8 : ℝ) ^ j) := by ring
    _ = 8 * (1 / 2 : ℝ) ^ j := by
      rw [← mul_pow, ← mul_pow]
      norm_num

end Rigidity.Proofs.Section5
