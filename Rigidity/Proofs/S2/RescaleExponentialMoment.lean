import Rigidity.Proofs.S2.StochasticBoundExponentialMoment
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Rescaling stretched-exponential moments

Convexity of the exponential converts a bounded half-exponential moment into a unit stochastic
moment after a fixed rescaling.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory

/-- A stochastic tail bound yields an exponential moment bounded by two after rescaling. -/
theorem integrable_scaled_exponential_of_osBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (s θ : ℝ)
    (hs : 0 < s) (hθ : 0 < θ) (hXm : Measurable X) (hX : LatticeProb.OsBound μ s θ X) :
    Integrable (fun ω => Real.exp ((max (X ω) 0 / θ) ^ s / 16)) μ ∧
      (∫ ω, Real.exp ((max (X ω) 0 / θ) ^ s / 16) ∂μ) ≤ 2 := by
  let Z : Ω → ℝ := fun ω => (max (X ω) 0 / θ) ^ s
  have hZm : Measurable Z := ((hXm.max measurable_const).div_const θ).pow_const s
  obtain ⟨hInt, hBound⟩ := integrable_half_exponential_of_osBound μ X s θ hs hθ hXm hX
  have hmajor : Integrable (fun ω => (7 / 8 : ℝ) + (1 / 8 : ℝ) * Real.exp (Z ω / 2)) μ :=
    (integrable_const _).add (hInt.const_mul _)
  have hpoint (ω : Ω) : Real.exp (Z ω / 16) ≤
      (7 / 8 : ℝ) + (1 / 8 : ℝ) * Real.exp (Z ω / 2) := by
    have h := convexOn_exp.2 (show (0 : ℝ) ∈ Set.univ from Set.mem_univ _)
      (show Z ω / 2 ∈ Set.univ from Set.mem_univ _)
      (show (0 : ℝ) ≤ 7 / 8 by norm_num) (show (0 : ℝ) ≤ 1 / 8 by norm_num)
      (show (7 / 8 : ℝ) + 1 / 8 = 1 by norm_num)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
    convert h using 1; congr 1; ring
  have hsmall : Integrable (fun ω => Real.exp (Z ω / 16)) μ := by
    refine hmajor.mono' ((hZm.div_const 16).exp).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact hpoint ω
  have hexp : Real.exp 2 ≤ 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  refine ⟨hsmall, ?_⟩
  calc
    _ ≤ ∫ ω, (7 / 8 : ℝ) + (1 / 8 : ℝ) * Real.exp (Z ω / 2) ∂μ :=
      integral_mono hsmall hmajor hpoint
    _ = (7 / 8 : ℝ) + (1 / 8 : ℝ) * ∫ ω, Real.exp (Z ω / 2) ∂μ := by
      rw [integral_add (integrable_const _) (hInt.const_mul _), integral_const_mul]
      simp [Z]
    _ ≤ 2 := by linarith

end Rigidity.Proofs.S2
