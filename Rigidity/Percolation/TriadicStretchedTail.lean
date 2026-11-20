import Rigidity.Percolation.TriadicStoppingTail
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Stretched-exponential bounds for stopping cubes

An exponential bound in the side length raised to a positive power gives a
stretched-exponential tail for the scale of a stopping cube.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- A stretched exponential at a later scale is bounded by its value at the
initial scale times a geometric factor. -/
theorem stretched_exp_scale_le (b c : ℝ) (hb : 1 < b) (hc : 0 < c) (n m : ℕ) :
    Real.exp (-c * b ^ (n + m)) ≤
      Real.exp (-c * b ^ n) * Real.exp (-c * (b - 1)) ^ m := by
  have hn : 1 ≤ b ^ n := one_le_pow₀ hb.le
  have hm : 1 + (m : ℝ) * (b - 1) ≤ b ^ m :=
    one_add_mul_sub_le_pow (by linarith) m
  have hmul := mul_le_mul_of_nonneg_left hm (show 0 ≤ b ^ n by positivity)
  have hnm : b ^ n + (m : ℝ) * (b - 1) ≤ b ^ (n + m) := by
    rw [pow_add]
    have hpos : 0 ≤ (m : ℝ) * (b - 1) := by positivity
    nlinarith
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Stretched-exponential bad-cube probabilities give a stretched-exponential
upper tail for the scale of a stopping cube containing a fixed point. -/
theorem TriadicCube.measure_exists_large_stopping_le_stretched {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (G : Ω → Set (TriadicCube d))
    (C : ℝ≥0∞) (b c : ℝ) (hb : 1 < b) (hc : 0 < c)
    (hprob : ∀ R : TriadicCube d,
      μ {ω | R ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ R.scale)))
    (x : Vertex d) (n : ℕ) :
    μ {ω | ∃ R : TriadicCube d, x ∈ R.vertices ∧ R.IsStopping (G ω) ∧ n + 1 < R.scale} ≤
      (19 ^ d : ℝ≥0∞) * C * ENNReal.ofReal (Real.exp (-c * b ^ n)) *
        ∑' m : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ m := by
  calc
    _ ≤ ∑' m : ℕ, (19 ^ d : ℝ≥0∞) *
        (C * ENNReal.ofReal (Real.exp (-c * b ^ (n + m)))) :=
      measure_exists_large_stopping_le μ G
        (fun k => C * ENNReal.ofReal (Real.exp (-c * b ^ k))) hprob x n
    _ ≤ ∑' m : ℕ, (19 ^ d : ℝ≥0∞) *
        (C * (ENNReal.ofReal (Real.exp (-c * b ^ n)) *
          ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ m)) := by
      apply ENNReal.tsum_le_tsum
      intro m
      gcongr
      have h := ENNReal.ofReal_le_ofReal (stretched_exp_scale_le b c hb hc n m)
      simpa only [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_pow (Real.exp_nonneg _) m] using h
    _ = _ := by
      simp_rw [← mul_assoc, ENNReal.tsum_mul_left]

/-- The geometric factor in the stretched-exponential estimate is finite. -/
theorem stretched_exp_geometric_sum_ne_top (b c : ℝ) (hb : 1 < b) (hc : 0 < c) :
    (∑' m : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ m) ≠ ∞ := by
  apply ne_of_lt (tsum_geometric_lt_top.mpr ?_)
  rw [ENNReal.ofReal_lt_one, Real.exp_lt_one_iff]
  have : 0 < b - 1 := by linarith
  nlinarith

/-- Stretched-exponential bad-cube bounds imply almost-sure existence of the
maximal stopping partition. -/
theorem TriadicCube.ae_existsUnique_maximal_stopping_of_stretched {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (G : Ω → Set (TriadicCube d))
    (C : ℝ≥0∞) (hC : C ≠ ∞) (b c : ℝ) (hb : 1 < b) (hc : 0 < c)
    (hprob : ∀ R : TriadicCube d,
      μ {ω | R ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ R.scale))) :
    ∀ᵐ ω ∂μ, ∀ x : Vertex d,
      ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω) := by
  let r : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-c * (b - 1)))
  have hr : r < 1 := by
    change ENNReal.ofReal (Real.exp (-c * (b - 1))) < 1
    rw [ENNReal.ofReal_lt_one, Real.exp_lt_one_iff]
    have : 0 < b - 1 := by linarith
    nlinarith
  apply ae_existsUnique_maximal_stopping_of_geometric μ G
    (C * ENNReal.ofReal (Real.exp (-c))) r
    (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hr
  intro R
  calc
    _ ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ R.scale)) := hprob R
    _ ≤ (C * ENNReal.ofReal (Real.exp (-c))) * r ^ R.scale := by
      have h := ENNReal.ofReal_le_ofReal (stretched_exp_scale_le b c hb hc 0 R.scale)
      simp only [zero_add, pow_zero, mul_one, ENNReal.ofReal_mul (Real.exp_nonneg _),
        ENNReal.ofReal_pow (Real.exp_nonneg _) R.scale] at h
      calc
        _ ≤ C * (ENNReal.ofReal (Real.exp (-c)) * r ^ R.scale) := by gcongr
        _ = _ := by simp only [mul_assoc]

end Rigidity.Percolation
