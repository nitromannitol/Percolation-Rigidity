import Rigidity.Proofs.Section5.PlanarGridCrossings
import Rigidity.Proofs.Section5.PlanarSparsePaths

/-!
# Almost-sure renormalized strip crossings

At sufficiently large block scales, summable strip families have disjoint crossings in both
orientations almost surely at all sufficiently large scales.
-/

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

/-- Summable families of renormalized strips have disjoint crossings in both orientations
at all sufficiently large scales, almost surely. -/
theorem ae_eventually_planar_renormalized_strip_crossings {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∀ᶠ R : ℕ in atTop, ∀ (T : ℕ → Finset PlanarCarrier) (m n k : ℕ → ℕ),
      (∀ j, 0 < m j) → (∀ j, 0 < n j) → (∀ j, 2 * k j ≤ n j) →
      Summable (fun j => 4 * ((T j).card : ℝ) * (m j + 1 : ℝ) * (1 / 8 : ℝ) ^ n j) →
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ᶠ j : ℕ in atTop,
        (∀ a ∈ T j, translatePlanarField a (Rigidity.Section5.renormField R ω) ∉
          disjointCrossingFailure (m j) (n j) (k j)) ∧
        ∀ a ∈ T j, translatePlanarField a
          (swapPlanarField (Rigidity.Section5.renormField R ω)) ∉
            disjointCrossingFailure (m j) (n j) (k j) := by
  filter_upwards [planar_renormalized_closed_marginal hpc] with R hsmall T m n k hm hn hk hs
  have hmeas := renormFieldMeasurableStep R
  haveI : IsProbabilityMeasure ((latticeBondLaw 2 p).map (Rigidity.Section5.renormField R)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have h := ae_eventually_disjoint_crossings_in_strips (renormFieldOneDependentStep p R) hsmall
    T m n k hm hn hk hs
  exact ae_of_ae_map hmeas.aemeasurable h

/-- Dyadic strip families of logarithmic width have the same almost-sure crossings. -/
theorem ae_eventually_planar_renormalized_dyadic_strip_crossings {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∀ᶠ R : ℕ in atTop, ∀ (T : ℕ → Finset PlanarCarrier) (m n k : ℕ → ℕ),
      (∀ j, 0 < m j) → (∀ j, 0 < n j) → (∀ j, 2 * k j ≤ n j) →
      (∀ j, (T j).card ≤ 2 ^ j) → (∀ j, m j ≤ 2 ^ j) → (∀ j, j ≤ n j) →
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ᶠ j : ℕ in atTop,
        (∀ a ∈ T j, translatePlanarField a (Rigidity.Section5.renormField R ω) ∉
          disjointCrossingFailure (m j) (n j) (k j)) ∧
        ∀ a ∈ T j, translatePlanarField a
          (swapPlanarField (Rigidity.Section5.renormField R ω)) ∉
            disjointCrossingFailure (m j) (n j) (k j) := by
  filter_upwards [ae_eventually_planar_renormalized_strip_crossings hpc] with R hR
    T m n k hm hn hk hT hm' hn'
  exact hR T m n k hm hn hk (summable_dyadic_strip_bounds T m n hT hm' hn')

/-- Lower-left corners of disjoint horizontal strips of width `j + 1` in a dyadic square. -/
def dyadicStripStarts (j : ℕ) : Finset PlanarCarrier :=
  (Finset.range (2 ^ j / (j + 2))).image fun (i : ℕ) => (0, (i : ℤ) * (j + 2))

/-- The number of these strips is at most the side length of the square. -/
theorem card_dyadicStripStarts_le (j : ℕ) : (dyadicStripStarts j).card ≤ 2 ^ j := by
  refine Finset.card_image_le.trans ?_
  simpa only [Finset.card_range] using Nat.div_le_self (2 ^ j) (j + 2)

/-- Every strip ends before the top of the dyadic square. -/
theorem dyadicStripStarts_vertical_bound {j : ℕ} {a : PlanarCarrier}
    (ha : a ∈ dyadicStripStarts j) :
    0 ≤ a.2 ∧ a.2 + (j + 1 : ℤ) ≤ (2 ^ j : ℕ) := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
  have hi' : i + 1 ≤ 2 ^ j / (j + 2) := by simpa using hi
  have hm := (Nat.mul_le_mul_right (j + 2) hi').trans (Nat.div_mul_le_self (2 ^ j) (j + 2))
  constructor
  · positivity
  · have hm' : ((i + 1 : ℕ) : ℤ) * ((j + 2 : ℕ) : ℤ) ≤ (2 ^ j : ℕ) := by exact_mod_cast hm
    push_cast at hm' ⊢
    nlinarith

/-- With probability one, each strip in every sufficiently large dyadic square has at least
`⌊(j + 1)/2⌋` disjoint renormalized crossings in each orientation. -/
theorem ae_eventually_dyadic_square_strip_crossings {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∀ᶠ R : ℕ in atTop, ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ᶠ j : ℕ in atTop,
      (∀ a ∈ dyadicStripStarts j, translatePlanarField a (Rigidity.Section5.renormField R ω) ∉
        disjointCrossingFailure (2 ^ j) (j + 1) ((j + 1) / 2)) ∧
      ∀ a ∈ dyadicStripStarts j, translatePlanarField a
        (swapPlanarField (Rigidity.Section5.renormField R ω)) ∉
          disjointCrossingFailure (2 ^ j) (j + 1) ((j + 1) / 2) := by
  filter_upwards [ae_eventually_planar_renormalized_dyadic_strip_crossings hpc] with R hR
  apply hR dyadicStripStarts (fun j => 2 ^ j) (fun j => j + 1) (fun j => (j + 1) / 2)
  · intro j
    positivity
  · intro j
    omega
  · intro j
    omega
  · exact card_dyadicStripStarts_le
  · intro j
    exact le_rfl
  · intro j
    omega

end Rigidity.Proofs.Section5
