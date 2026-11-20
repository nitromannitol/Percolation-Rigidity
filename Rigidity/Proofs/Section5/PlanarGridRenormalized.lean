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

end Rigidity.Proofs.Section5
