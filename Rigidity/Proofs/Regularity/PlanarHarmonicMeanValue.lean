import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Mean value property of planar harmonic functions on discs

For `f : ℂ → ℝ` harmonic in a neighbourhood of the closed disc `B̄_ρ(c)`,
`∫_{B_ρ(c)} f = π ρ² f(c)` (`integral_ball_eq_of_harmonicOnNhd`): the mean value property on
circles (`HarmonicOnNhd.circleAverage_eq`) integrated in polar coordinates.
-/

open MeasureTheory Metric Real Set

namespace Rigidity.Proofs.Regularity

theorem integral_ball_eq_integral_indicator_add (f : ℂ → ℝ) (c : ℂ) (ρ : ℝ) :
    ∫ x in ball c ρ, f x = ∫ x, (ball (0 : ℂ) ρ).indicator (fun z => f (z + c)) x := by
  rw [← integral_indicator measurableSet_ball,
    ← integral_add_right_eq_self (μ := volume) (fun x => (ball c ρ).indicator f x) c]
  congr 1
  funext x
  have hmem : x + c ∈ ball c ρ ↔ x ∈ ball (0 : ℂ) ρ := by
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero]
  by_cases hx : x ∈ ball (0 : ℂ) ρ
  · rw [indicator_of_mem (hmem.2 hx), indicator_of_mem hx]
  · rw [indicator_of_notMem (fun h => hx (hmem.1 h)), indicator_of_notMem hx]

theorem continuous_polarCoord_symm_complex :
    Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
  have e : (fun p : ℝ × ℝ => Complex.polarCoord.symm p) =
      fun p => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) :=
    funext Complex.polarCoord_symm_apply
  rw [e]
  fun_prop

/-- Polar coordinates for the integral over a disc centred at `0`. -/
theorem integral_indicator_ball_eq_polar (F : ℂ → ℝ) {ρ : ℝ} :
    ∫ x, (ball (0 : ℂ) ρ).indicator F x =
      ∫ p in Ioo 0 ρ ×ˢ Ioo (-π) π, p.1 * F (Complex.polarCoord.symm p) := by
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have hS : Ioo 0 ρ ×ˢ Ioo (-π) π = (Ioi 0 ×ˢ Ioo (-π) π) ∩ (Iio ρ ×ˢ univ) := by
    ext p
    simp only [mem_prod, mem_Ioo, mem_Ioi, mem_inter_iff, mem_Iio, mem_univ, and_true]
    tauto
  rw [hS, ← setIntegral_indicator (measurableSet_Iio.prod MeasurableSet.univ)]
  refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
  have hp1 : 0 < p.1 := hp.1
  have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
  by_cases h : p.1 < ρ
  · have h1 : Complex.polarCoord.symm p ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball, dist_zero_right, hnorm]; exact h
    have h2 : p ∈ Iio ρ ×ˢ (univ : Set ℝ) := ⟨h, trivial⟩
    simp only [indicator_of_mem h1, indicator_of_mem h2, smul_eq_mul]
  · have h1 : Complex.polarCoord.symm p ∉ ball (0 : ℂ) ρ := by
      rw [mem_ball, dist_zero_right, hnorm]; exact h
    have h2 : p ∉ Iio ρ ×ˢ (univ : Set ℝ) := fun hh => h hh.1
    simp only [indicator_of_notMem h1, indicator_of_notMem h2, smul_zero]

theorem polarCoord_symm_add_eq_circleMap (c : ℂ) (t θ : ℝ) :
    Complex.polarCoord.symm (t, θ) + c = circleMap c t θ := by
  simp only [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  ring

/-- The angular integral is `2 π` times the circle average. -/
theorem integral_Ioo_polar_eq_circleAverage (f : ℂ → ℝ) (c : ℂ) (t : ℝ) :
    ∫ θ in Ioo (-π) π, f (Complex.polarCoord.symm (t, θ) + c) = 2 * π * circleAverage f c t := by
  simp_rw [polarCoord_symm_add_eq_circleMap]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  have hper : Function.Periodic (fun θ => f (circleMap c t θ)) (2 * π) :=
    fun θ => by simp only [periodic_circleMap c t θ]
  have h := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at h
  rw [h, circleAverage_def, smul_eq_mul]
  field_simp

/-- **Mean value property on discs.** -/
theorem integral_ball_eq_of_harmonicOnNhd {f : ℂ → ℝ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : InnerProductSpace.HarmonicOnNhd f (closedBall c ρ)) :
    ∫ x in ball c ρ, f x = π * ρ ^ 2 * f c := by
  rw [integral_ball_eq_integral_indicator_add, integral_indicator_ball_eq_polar]
  have hfc : ContinuousOn f (closedBall c ρ) := fun x hx =>
    (hf x hx).1.continuousAt.continuousWithinAt
  set G : ℝ × ℝ → ℝ := fun p => p.1 * f (Complex.polarCoord.symm p + c) with hGdef
  have hcont : ContinuousOn G (Icc 0 ρ ×ˢ Icc (-π) π) := by
    refine continuous_fst.continuousOn.mul (hfc.comp
      ((continuous_polarCoord_symm_complex.add continuous_const).continuousOn) ?_)
    intro p hp
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right, Complex.norm_polarCoord_symm,
      abs_of_nonneg hp.1.1]
    exact hp.1.2
  have hint : IntegrableOn G (Ioo 0 ρ ×ˢ Ioo (-π) π) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [Measure.volume_eq_prod, setIntegral_prod G hint]
  have hin : ∀ t ∈ Ioo 0 ρ, ∫ θ in Ioo (-π) π, G (t, θ) = t * (2 * π * f c) := by
    intro t ht
    simp only [hGdef]
    rw [integral_const_mul, integral_Ioo_polar_eq_circleAverage]
    have hsub : closedBall c |t| ⊆ closedBall c ρ :=
      closedBall_subset_closedBall (by rw [abs_of_pos ht.1]; exact ht.2.le)
    rw [HarmonicOnNhd.circleAverage_eq (f := f) fun x hx => hf x (hsub hx)]
  rw [setIntegral_congr_fun measurableSet_Ioo hin, integral_mul_const,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ.le, integral_id]
  ring

end Rigidity.Proofs.Regularity
