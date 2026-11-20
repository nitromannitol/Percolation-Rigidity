import Rigidity.Percolation.TriadicLocalizationParentProbability
import Rigidity.Percolation.TriadicStoppingMeasurable

/-!
# Interior localization of stopping partitions

The stopping partition built using only good-cube events supported in a
region agrees with the global partition at interior points with high probability.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- A triadic interior distance at scale `n` exceeds fourteen times the side
length at scale `n - 3`, provided `n ≥ 3`. -/
theorem triadic_interior_scale_bound {n : ℕ} (hn : 3 ≤ n) :
    14 * (3 : ℤ) ^ (n - 3) ≤ (3 : ℤ) ^ n := by
  have h : n = (n - 3) + 3 := by omega
  conv_rhs => rw [h, pow_add]
  have hp : 0 ≤ (3 : ℤ) ^ (n - 3) := by positivity
  norm_num
  nlinarith

/-- The localized maximal stopping partition differs from the global one
on an interior subset only with stretched-exponentially small probability. -/
theorem TriadicCube.measure_local_stopping_discrepancy_le {d : ℕ} (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → Set (TriadicCube d)) (U : Set (Vertex d)) (A : TriadicCube d)
    (V : Set (Vertex d)) (hVA : V ⊆ A.vertices) (n : ℕ) (hn : 3 ≤ n)
    (hdist : ∀ x ∈ V, ∀ y ∉ U, ∃ i, (3 : ℤ) ^ n ≤ |x i - y i|)
    (C : ℝ≥0∞) (b c : ℝ) (hb : 1 < b) (hc : 0 < c)
    (hprob : ∀ T : TriadicCube d,
      μ {ω | T ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ T.scale))) :
    μ {ω | ∃ x ∈ V, ∃ Q R : TriadicCube d,
      x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
        R.IsMaximalStopping (localGood (G ω) U) ∧ Q ≠ R} ≤
      max 1 (C * ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k) *
        ((2 * 3 ^ (A.scale - (n - 3 + 1)) + 29 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp ((-c * b ^ (n - 3 + 1)) / d)) := by
  apply measure_parent_stopping_discrepancy_le_stretched_linear hd μ G
    (fun ω => localGood (G ω) U) U A V hVA (n - 3)
  · intro ω
    exact subset_localGood (G ω) U
  · intro ω T hT hmem
    exact mem_of_mem_localGood hT hmem
  · intro x hx y hy
    obtain ⟨i, hi⟩ := hdist x hx y hy
    exact ⟨i, (triadic_interior_scale_bound hn).trans hi⟩
  · exact hb
  · exact hc
  · exact hprob

end Rigidity.Percolation
