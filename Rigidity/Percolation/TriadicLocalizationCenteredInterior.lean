import Rigidity.Percolation.TriadicLocalizationCenteredProbability
import Rigidity.Percolation.TriadicLocalizationInterior

/-!
# Interior localization with centered support

A stretched-exponential bad-cube estimate controls the discrepancy between
the global stopping partition and the partition localized using concentric
threefold cubes.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- The centered-support local stopping partition differs from the global
partition on an interior subset only with stretched-exponentially small probability. -/
theorem TriadicCube.measure_localGoodCentered_stopping_discrepancy_le {d : ℕ} (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → Set (TriadicCube d)) (U : Set (Vertex d)) (A : TriadicCube d)
    (V : Set (Vertex d)) (hVA : V ⊆ A.vertices) (n : ℕ) (hn : 3 ≤ n)
    (hdist : ∀ x ∈ V, ∀ y ∉ U, ∃ i, (3 : ℤ) ^ n ≤ |x i - y i|)
    (C : ℝ≥0∞) (b c : ℝ) (hb : 1 < b) (hc : 0 < c)
    (hprob : ∀ T : TriadicCube d,
      μ {ω | T ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ T.scale))) :
    μ {ω | ∃ x ∈ V, ∃ Q R : TriadicCube d,
      x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
        R.IsMaximalStopping (localGoodCentered (G ω) U) ∧ Q ≠ R} ≤
      max 1 (C * ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k) *
        ((2 * 3 ^ (A.scale - (n - 3 + 1)) + 29 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp ((-c * b ^ (n - 3 + 1)) / d)) := by
  apply measure_centered_stopping_discrepancy_le_stretched_linear hd μ G
    (fun ω => localGoodCentered (G ω) U) U A V hVA (n - 3)
  · intro ω
    exact subset_localGoodCentered (G ω) U
  · intro ω T hT hmem
    exact mem_of_mem_localGoodCentered hT hmem
  · intro x hx y hy
    obtain ⟨i, hi⟩ := hdist x hx y hy
    exact ⟨i, (triadic_interior_scale_bound hn).trans hi⟩
  · exact hb
  · exact hc
  · exact hprob

end Rigidity.Percolation
