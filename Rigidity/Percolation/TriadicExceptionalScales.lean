import Rigidity.Percolation.TriadicStretchedTail
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Exceptional triadic scales

A sequence of events whose probabilities decay stretched exponentially in
the triadic scale has a summable tail, with the same decay after a union bound.
-/

namespace Rigidity.Percolation

open MeasureTheory
open scoped ENNReal

/-- A union of events at and above a scale inherits the first event's
stretched-exponential rate, up to a finite geometric factor. -/
theorem measure_exists_large_index_le_stretched {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : ℕ → Set Ω) (C : ℝ≥0∞) (b c : ℝ)
    (hb : 1 < b) (hc : 0 < c)
    (hE : ∀ n : ℕ, μ (E n) ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ n)))
    (N : ℕ) :
    μ {ω | ∃ n : ℕ, N ≤ n ∧ ω ∈ E n} ≤
      C * ENNReal.ofReal (Real.exp (-c * b ^ N)) *
        ∑' m : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ m := by
  have hsubset : {ω | ∃ n : ℕ, N ≤ n ∧ ω ∈ E n} ⊆ ⋃ m : ℕ, E (N + m) := by
    intro ω hω
    obtain ⟨n, hn, hω⟩ := hω
    refine Set.mem_iUnion.mpr ⟨n - N, ?_⟩
    simpa only [Nat.add_sub_of_le hn] using hω
  calc
    _ ≤ μ (⋃ m : ℕ, E (N + m)) := measure_mono hsubset
    _ ≤ ∑' m : ℕ, μ (E (N + m)) := measure_iUnion_le _
    _ ≤ ∑' m : ℕ, C * (ENNReal.ofReal (Real.exp (-c * b ^ N)) *
        ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ m) := by
      apply ENNReal.tsum_le_tsum
      intro m
      calc
        _ ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ (N + m))) := hE (N + m)
        _ ≤ C * (ENNReal.ofReal (Real.exp (-c * b ^ N)) *
            ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ m) := by
          gcongr
          have h := ENNReal.ofReal_le_ofReal (stretched_exp_scale_le b c hb hc N m)
          simpa only [ENNReal.ofReal_mul (Real.exp_nonneg _),
            ENNReal.ofReal_pow (Real.exp_nonneg _) m] using h
    _ = _ := by simp_rw [← mul_assoc, ENNReal.tsum_mul_left]

/-- Stretched-exponentially rare events occur at only finitely many scales
almost surely. -/
theorem ae_eventually_notMem_of_stretched {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : ℕ → Set Ω) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (b c : ℝ) (hb : 1 < b) (hc : 0 < c)
    (hE : ∀ n : ℕ, μ (E n) ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ n))) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop, ω ∉ E n := by
  have hsum : (∑' n : ℕ, μ (E n)) ≤
      (C * ENNReal.ofReal (Real.exp (-c))) *
        ∑' n : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ n := by
    calc
      _ ≤ ∑' n : ℕ, (C * ENNReal.ofReal (Real.exp (-c))) *
          ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ n := by
        apply ENNReal.tsum_le_tsum
        intro n
        calc
          _ ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ n)) := hE n
          _ ≤ (C * ENNReal.ofReal (Real.exp (-c))) *
              ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ n := by
            have h := ENNReal.ofReal_le_ofReal (stretched_exp_scale_le b c hb hc 0 n)
            simp only [zero_add, pow_zero, mul_one, ENNReal.ofReal_mul (Real.exp_nonneg _),
              ENNReal.ofReal_pow (Real.exp_nonneg _) n] at h
            calc
              _ ≤ C * (ENNReal.ofReal (Real.exp (-c)) *
                  ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ n) := by gcongr
              _ = _ := by simp only [mul_assoc]
      _ = _ := ENNReal.tsum_mul_left
  have hfinite : (∑' n : ℕ, μ (E n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ hsum
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top)
      (stretched_exp_geometric_sum_ne_top b c hb hc)
  exact ae_eventually_notMem hfinite

end Rigidity.Percolation
