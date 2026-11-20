import Rigidity.Percolation.TriadicLocalizationUniform
import Rigidity.Percolation.TriadicInteriorEmpty

/-!
# Localization with finite uniform constants

The discrepancy probability has a stretched-exponential bound with finite
constants independent of the cube and its interior scale.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- A stretched-exponential good-cube estimate yields localization with
finite constants independent of the cube and interior scale. -/
theorem TriadicCube.exists_measure_localGoodCentered_boundaryInterior_discrepancy_le
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : Ω → Set (TriadicCube d))
    (C : ℝ≥0∞) (hC : C ≠ ∞) (b c : ℝ) (hb : 1 < b) (hc : 0 < c)
    (hprob : ∀ T : TriadicCube d,
      μ {ω | T ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ T.scale))) :
    ∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ (A : TriadicCube d) (n : ℕ),
      μ {ω | ∃ x ∈ A.boundaryInterior n, ∃ Q R : TriadicCube d,
        x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
          R.IsMaximalStopping (localGoodCentered (G ω) A.vertices) ∧ Q ≠ R} ≤
        ENNReal.ofReal (K * (3 : ℝ) ^ ((A.scale : ℝ) - n) * Real.exp (-k * b ^ n)) := by
  let D : ℝ≥0∞ := (47 : ℝ≥0∞) *
    max 1 (C * ∑' j : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ j) *
    ENNReal.ofReal (Real.exp (c / d))
  have hsum : (∑' j : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ j) ≠ ∞ :=
    stretched_exp_geometric_sum_ne_top b c hb hc
  have hmax : max 1 (C * ∑' j : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ j) ≠ ∞ := by
    apply ne_of_lt
    rw [max_lt_iff]
    exact ⟨by simp, lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hC hsum)⟩
  have hD : D ≠ ∞ := by
    dsimp only [D]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hmax) ENNReal.ofReal_ne_top
  let K : ℝ := max 1 D.toReal
  let k : ℝ := c / ((d : ℝ) * b ^ 2)
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hk : 0 < k := by dsimp only [k]; positivity
  have hDK : D ≤ ENNReal.ofReal K := by
    rw [← ENNReal.ofReal_toReal hD]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  refine ⟨K, k, hK, hk, ?_⟩
  intro A n
  by_cases hn : A.scale ≤ n
  · rw [A.measure_localGoodCentered_boundaryInterior_discrepancy_eq_zero hd μ G n hn]
    exact bot_le
  · have hnm : n ≤ A.scale := by omega
    have hrpow : (3 : ℝ) ^ ((A.scale : ℝ) - n) = (3 : ℝ) ^ (A.scale - n) := by
      rw [← Nat.cast_sub hnm, Real.rpow_natCast]
    rw [hrpow]
    calc
      _ ≤ D * (3 ^ (A.scale - n) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-k * b ^ n)) := by
        exact A.measure_localGoodCentered_boundaryInterior_discrepancy_le_uniform hd μ G n C b c hb hc hprob
      _ ≤ ENNReal.ofReal K * (3 ^ (A.scale - n) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-k * b ^ n)) := by gcongr
      _ = ENNReal.ofReal (K * (3 : ℝ) ^ (A.scale - n) * Real.exp (-k * b ^ n)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hK.le (by positivity)),
          ENNReal.ofReal_mul hK.le, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num

end Rigidity.Percolation
