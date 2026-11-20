import Rigidity.Percolation.TriadicExceptionalScales
import Rigidity.Percolation.TriadicStochasticMoment

/-!
# Moments of exceptional scales

A measurable scale bounded by the size of an exceptional triadic cube has
a stretched-exponential moment when the exceptional events have the same tail.
-/

namespace Rigidity.Percolation

open LatticeProb MeasureTheory
open scoped ENNReal

/-- A scale controlled by exceptional events has a stretched-exponential
moment with the same exponent as their triadic probability bound. -/
theorem exp_moment_of_exceptional_scales {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : ℕ → Set Ω) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (s c : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hE : ∀ n : ℕ, μ (E n) ≤ C * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ n) ^ s)))
    (M : Ω → ℝ) (hM : Measurable M) (hM0 : ∀ ω, 0 ≤ M ω)
    (hbound : ∀ ω, 0 < M ω → ∃ n : ℕ, ω ∈ E n ∧ M ω ≤ (3 : ℝ) ^ n) :
    ∃ θ : ℝ, 0 < θ ∧ Integrable (fun ω => Real.exp ((M ω / θ) ^ s)) μ ∧
      (∫ ω, Real.exp ((M ω / θ) ^ s) ∂μ) ≤ 2 := by
  let b : ℝ := (3 : ℝ) ^ s
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) hs
  let D : ℝ≥0∞ := C * ∑' n : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ n
  have hD : D ≠ ∞ := ENNReal.mul_ne_top hC (stretched_exp_geometric_sum_ne_top b c hb hc)
  let B : ℝ := max 1 D.toReal
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hDB : D ≤ ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_toReal hD]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hE' : ∀ n : ℕ, μ (E n) ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ n)) := by
    intro n
    simpa only [b, Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3)] using hE n
  obtain ⟨θ, hθ, ht⟩ := osBound_of_triadic_tail B c s hB hc hs
  have htriadic (n : ℕ) : μ {ω | (3 : ℝ) ^ (n + 2) < M ω} ≤
      ENNReal.ofReal (B * Real.exp (-c * ((3 : ℝ) ^ n) ^ s)) := by
    calc
      _ ≤ μ {ω | ∃ j : ℕ, n ≤ j ∧ ω ∈ E j} := by
        apply measure_mono
        intro ω hω
        change (3 : ℝ) ^ (n + 2) < M ω at hω
        have hp : 0 < (3 : ℝ) ^ (n + 2) := by positivity
        obtain ⟨j, hj, hsize⟩ := hbound ω (hp.trans hω)
        refine ⟨j, ?_, hj⟩
        by_contra h
        have hjn : j ≤ n + 2 := by omega
        have hpw : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ (n + 2) :=
          pow_le_pow_right₀ (by norm_num) hjn
        linarith
      _ ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ n)) *
          ∑' m : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ m :=
        measure_exists_large_index_le_stretched μ E C b c hb hc hE' n
      _ = D * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ n) ^ s)) := by
        dsimp only [D, b]
        rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3)]
        ac_rfl
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ n) ^ s)) :=
        mul_le_mul_left hDB _
      _ = ENNReal.ofReal (B * Real.exp (-c * ((3 : ℝ) ^ n) ^ s)) :=
        (ENNReal.ofReal_mul hB.le).symm
  exact OsBound.exists_exp_rpow_integrable_le_two μ hs hθ hM hM0 (ht μ M hM0 htriadic)

end Rigidity.Percolation
