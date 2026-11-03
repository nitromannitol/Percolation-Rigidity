import Rigidity.Support.MixedGreenScaleTransport
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Moment transport for a deterministic enlargement of a random scale -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace Rigidity.Support

/-- Enlarging a scale and its deterministic normalization preserves its exponential moment. -/
theorem scaled_exp_moment_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (M : Ω → ℝ) (a C β scale : ℝ) (ha : 0 < a) (hC : 0 < C) (hβ : 0 < β)
    (hscale1 : 1 ≤ scale) (hscale : scale * a ≤ C) (hM : Measurable M) (hM1 : ∀ ω, 1 ≤ M ω)
    (hi : Integrable (fun ω => Real.exp (Real.rpow (M ω / a) β)) μ)
    (hb : (∫ ω, Real.exp (Real.rpow (M ω / a) β) ∂μ) ≤ 2) :
    Measurable (fun ω => scale * M ω) ∧ (∀ ω, 1 ≤ scale * M ω) ∧
      Integrable (fun ω => Real.exp (Real.rpow (scale * M ω / C) β)) μ ∧
      (∫ ω, Real.exp (Real.rpow (scale * M ω / C) β) ∂μ) ≤ 2 := by
  have hscale0 : 0 ≤ scale := le_trans zero_le_one hscale1
  have hpoint (ω : Ω) : Real.exp (Real.rpow (scale * M ω / C) β) ≤
      Real.exp (Real.rpow (M ω / a) β) := by
    apply Real.exp_le_exp.mpr
    apply Real.rpow_le_rpow (div_nonneg (mul_nonneg hscale0 (by linarith [hM1 ω])) hC.le) _ hβ.le
    apply (div_le_div_iff₀ hC ha).2
    have := mul_le_mul_of_nonneg_right hscale (show 0 ≤ M ω by linarith [hM1 ω])
    nlinarith
  have hm : Measurable (fun ω => Real.exp (Real.rpow (scale * M ω / C) β)) := by
    simp only [Real.rpow_eq_pow]
    fun_prop
  have hj : Integrable (fun ω => Real.exp (Real.rpow (scale * M ω / C) β)) μ := by
    apply hi.mono' hm.aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hpoint ω
  refine ⟨measurable_const.mul hM, ?_, hj, ?_⟩
  · intro ω
    nlinarith [hM1 ω, hscale1]
  · exact (integral_mono hj hi hpoint).trans hb

end Rigidity.Support
