import Rigidity.Percolation.TriadicBoundary

/-!
# Uniform interior localization

A shifted localization estimate yields a uniform stretched-exponential bound
at every triadic scale.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

private theorem count_scale_shift_le (m n : ℕ) :
    2 * 3 ^ (m - (n - 3 + 1)) + 29 ≤ 47 * 3 ^ (m - n) := by
  have hn : m - (n - 3 + 1) ≤ (m - n) + 2 := by omega
  have hp : 3 ^ (m - (n - 3 + 1)) ≤ 3 ^ ((m - n) + 2) :=
    Nat.pow_le_pow_right (by omega) hn
  have hq : 1 ≤ 3 ^ (m - n) := Nat.one_le_pow _ _ (by omega)
  rw [pow_add] at hp
  norm_num at hp
  nlinarith

private theorem exp_scale_shift (b c : ℝ) (d n : ℕ) (hb : 1 < b)
    (hd : 0 < d) (hn : 3 ≤ n) :
    (-c * b ^ (n - 3 + 1)) / d = -(c / ((d : ℝ) * b ^ 2)) * b ^ n := by
  have h : n = (n - 3 + 1) + 2 := by omega
  conv_rhs => rw [h, pow_add]
  have hb0 : b ≠ 0 := by linarith
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  field_simp

/-- A centered local stopping partition agrees with the global partition in
an interior cube except with a uniformly stretched-exponential probability. -/
theorem TriadicCube.measure_localGoodCentered_boundaryInterior_discrepancy_le_uniform
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : Ω → Set (TriadicCube d)) (A : TriadicCube d)
    (n : ℕ) (C : ℝ≥0∞) (b c : ℝ) (hb : 1 < b) (hc : 0 < c)
    (hprob : ∀ T : TriadicCube d,
      μ {ω | T ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ T.scale))) :
    μ {ω | ∃ x ∈ A.boundaryInterior n, ∃ Q R : TriadicCube d,
      x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
        R.IsMaximalStopping (localGoodCentered (G ω) A.vertices) ∧ Q ≠ R} ≤
      (47 : ℝ≥0∞) *
        max 1 (C * ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k) *
        ENNReal.ofReal (Real.exp (c / d)) * (3 ^ (A.scale - n) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(c / ((d : ℝ) * b ^ 2)) * b ^ n)) := by
  let K : ℝ≥0∞ := max 1 (C * ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k)
  let E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (c / d))
  let Z : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(c / ((d : ℝ) * b ^ 2)) * b ^ n))
  have hK : 1 ≤ K := le_max_left _ _
  have hE : 1 ≤ E := by
    dsimp only [E]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    exact Real.one_le_exp (by positivity)
  have hP : (1 : ℝ≥0∞) ≤ 3 ^ (A.scale - n) := one_le_pow₀ (by norm_num)
  by_cases hn : 3 ≤ n
  · have hcount : ((2 * 3 ^ (A.scale - (n - 3 + 1)) + 29 : ℕ) : ℝ≥0∞) ≤
        47 * (3 ^ (A.scale - n) : ℝ≥0∞) := by
      exact_mod_cast count_scale_shift_le A.scale n
    have hexp : ENNReal.ofReal (Real.exp ((-c * b ^ (n - 3 + 1)) / d)) = Z := by
      rw [exp_scale_shift b c d n hb hd hn]
    calc
      _ ≤ K * ((2 * 3 ^ (A.scale - (n - 3 + 1)) + 29 : ℕ) : ℝ≥0∞) * Z := by
        rw [← hexp]
        exact A.measure_localGoodCentered_boundaryInterior_discrepancy_le hd μ G n hn C b c hb hc hprob
      _ ≤ K * (47 * (3 ^ (A.scale - n) : ℝ≥0∞)) * Z := by gcongr
      _ ≤ 47 * K * E * (3 ^ (A.scale - n) : ℝ≥0∞) * Z := by
        calc
          _ = 47 * K * 1 * (3 ^ (A.scale - n) : ℝ≥0∞) * Z := by ac_rfl
          _ ≤ _ := by gcongr
  · have hn2 : n ≤ 2 := by omega
    have hp : b ^ n ≤ b ^ 2 := pow_le_pow_right₀ (by linarith) hn2
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hb' : 0 < b ^ 2 := by positivity
    have hreal : 0 ≤ c / d + (-(c / ((d : ℝ) * b ^ 2)) * b ^ n) := by
      have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hd'
      have hb0 : b ^ 2 ≠ 0 := ne_of_gt hb'
      have heq : c / d + (-(c / ((d : ℝ) * b ^ 2)) * b ^ n) =
          (c * (b ^ 2 - b ^ n)) / ((d : ℝ) * b ^ 2) := by
        field_simp
        ring
      rw [heq]
      exact div_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hp)) (mul_nonneg hd'.le hb'.le)
    have hEZ : 1 ≤ E * Z := by
      dsimp only [E, Z]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hreal)
    calc
      _ ≤ 1 := (measure_mono (Set.subset_univ _)).trans_eq measure_univ
      _ ≤ (47 : ℝ≥0∞) * K * E * (3 ^ (A.scale - n) : ℝ≥0∞) * Z := by
        calc
          _ ≤ E * Z := hEZ
          _ = 1 * 1 * E * 1 * Z := by simp only [one_mul, mul_one]
          _ ≤ _ := by
            gcongr
            norm_num

end Rigidity.Percolation
