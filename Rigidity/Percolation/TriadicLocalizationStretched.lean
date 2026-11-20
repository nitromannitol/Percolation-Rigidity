import Rigidity.Percolation.TriadicLocalizationProbability
import Rigidity.Percolation.TriadicStretchedTail

/-!
# Stretched-exponential localization of stopping partitions

Stretched-exponential bad-cube bounds imply a quantitative bound for the
probability of a discrepancy between two stopping partitions.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- A stretched-exponential bad-cube bound yields a stretched-exponential
estimate for changes in the stopping partition inside a cube. -/
theorem TriadicCube.measure_stopping_discrepancy_le_stretched {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (G H : Ω → Set (TriadicCube d))
    (U : Set (Vertex d)) (A : TriadicCube d) (n : ℕ)
    (hGH : ∀ ω, G ω ⊆ H ω)
    (hlocal : ∀ ω T, T.vertices ⊆ U → T ∈ H ω → T ∈ G ω)
    (hdist : ∀ x ∈ A.vertices, ∀ y ∉ U, ∃ i, 12 * (3 : ℤ) ^ n ≤ |x i - y i|)
    (C : ℝ≥0∞) (b c : ℝ) (hb : 1 < b) (hc : 0 < c)
    (hprob : ∀ T : TriadicCube d,
      μ {ω | T ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ T.scale))) :
    μ {ω | ∃ x ∈ A.vertices, ∃ Q R : TriadicCube d,
      x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
        R.IsMaximalStopping (H ω) ∧ Q ≠ R} ≤
      (((2 * 3 ^ (A.scale - (n + 1)) + 29) ^ d : ℕ) : ℝ≥0∞) * C *
        ENNReal.ofReal (Real.exp (-c * b ^ (n + 1))) *
        ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k := by
  calc
    _ ≤ ∑' k : ℕ, (((2 * 3 ^ (A.scale - (n + 1 + k)) + 29) ^ d : ℕ) : ℝ≥0∞) *
        (C * ENNReal.ofReal (Real.exp (-c * b ^ (n + 1 + k)))) :=
      measure_stopping_discrepancy_le μ G H U A n hGH hlocal hdist
        (fun j => C * ENNReal.ofReal (Real.exp (-c * b ^ j))) hprob
    _ ≤ ∑' k : ℕ, (((2 * 3 ^ (A.scale - (n + 1)) + 29) ^ d : ℕ) : ℝ≥0∞) *
        (C * (ENNReal.ofReal (Real.exp (-c * b ^ (n + 1))) *
          ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k)) := by
      apply ENNReal.tsum_le_tsum
      intro k
      have hcount : (2 * 3 ^ (A.scale - (n + 1 + k)) + 29) ^ d ≤
          (2 * 3 ^ (A.scale - (n + 1)) + 29) ^ d := by
        apply pow_le_pow_left'
        apply Nat.add_le_add_right
        apply Nat.mul_le_mul_left
        exact pow_le_pow_right₀ (by omega) (by omega)
      have hexp := ENNReal.ofReal_le_ofReal (stretched_exp_scale_le b c hb hc (n + 1) k)
      simp only [ENNReal.ofReal_mul (Real.exp_nonneg _),
        ENNReal.ofReal_pow (Real.exp_nonneg _) k] at hexp
      have hcount' : (((2 * 3 ^ (A.scale - (n + 1 + k)) + 29) ^ d : ℕ) : ℝ≥0∞) ≤
          (((2 * 3 ^ (A.scale - (n + 1)) + 29) ^ d : ℕ) : ℝ≥0∞) := by
        exact_mod_cast hcount
      exact mul_le_mul' hcount' (mul_le_mul' le_rfl hexp)
    _ = _ := by
      simp_rw [← mul_assoc, ENNReal.tsum_mul_left]

end Rigidity.Percolation
