import Rigidity.Percolation.TriadicLocalizationStretched
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# A one-power localization bound

The probability-one bound reduces the polynomial prefactor in a
stretched-exponential estimate to a single power.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- A quantity bounded by one and by a positive power of `a` is bounded by `a`. -/
theorem le_of_le_one_of_le_pow {m a : ℝ≥0∞} {d : ℕ} (hd : 0 < d)
    (hm : m ≤ 1) (hpow : m ≤ a ^ d) : m ≤ a := by
  rcases le_total a 1 with ha | ha
  · have hp : a ^ d ≤ a := by
      simpa only [pow_one] using (pow_le_pow_right_of_le_one' ha hd)
    exact hpow.trans hp
  · exact hm.trans ha

/-- Under a probability measure, the localization bound has a linear scale
ratio at the cost of weakening the stretched-exponential rate by `d`. -/
theorem TriadicCube.measure_stopping_discrepancy_le_stretched_linear {d : ℕ} (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G H : Ω → Set (TriadicCube d)) (U : Set (Vertex d)) (A : TriadicCube d) (n : ℕ)
    (hGH : ∀ ω, G ω ⊆ H ω)
    (hlocal : ∀ ω T, T.vertices ⊆ U → T ∈ H ω → T ∈ G ω)
    (hdist : ∀ x ∈ A.vertices, ∀ y ∉ U, ∃ i, 12 * (3 : ℤ) ^ n ≤ |x i - y i|)
    (C : ℝ≥0∞) (b c : ℝ) (hb : 1 < b) (hc : 0 < c)
    (hprob : ∀ T : TriadicCube d,
      μ {ω | T ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ T.scale))) :
    μ {ω | ∃ x ∈ A.vertices, ∃ Q R : TriadicCube d,
      x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
        R.IsMaximalStopping (H ω) ∧ Q ≠ R} ≤
      max 1 (C * ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k) *
        ((2 * 3 ^ (A.scale - (n + 1)) + 29 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp ((-c * b ^ (n + 1)) / d)) := by
  let K : ℝ≥0∞ := max 1 (C * ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k)
  let B : ℝ≥0∞ := ((2 * 3 ^ (A.scale - (n + 1)) + 29 : ℕ) : ℝ≥0∞)
  let z : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((-c * b ^ (n + 1)) / d))
  have hK : 1 ≤ K := le_max_left _ _
  have hKpow : K ≤ K ^ d := by
    simpa only [pow_one] using (pow_le_pow_right' hK hd)
  have hD : C * ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k ≤ K ^ d :=
    (le_max_right _ _).trans hKpow
  have hz : z ^ d = ENNReal.ofReal (Real.exp (-c * b ^ (n + 1))) := by
    dsimp only [z]
    rw [← ENNReal.ofReal_pow (Real.exp_nonneg _) d, ← Real.exp_nat_mul]
    congr 2
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    field_simp
  apply le_of_le_one_of_le_pow hd
  · calc
      _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  · calc
      _ ≤ (((2 * 3 ^ (A.scale - (n + 1)) + 29) ^ d : ℕ) : ℝ≥0∞) * C *
          ENNReal.ofReal (Real.exp (-c * b ^ (n + 1))) *
          ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k :=
        measure_stopping_discrepancy_le_stretched μ G H U A n hGH hlocal hdist C b c hb hc hprob
      _ = B ^ d * (C * ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k) * z ^ d := by
        rw [hz]
        simp only [B, Nat.cast_pow]
        ac_rfl
      _ ≤ B ^ d * K ^ d * z ^ d := by gcongr
      _ = (K * B * z) ^ d := by rw [mul_pow, mul_pow]; ac_rfl

end Rigidity.Percolation
