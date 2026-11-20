import Rigidity.Percolation.TriadicStochasticBound

/-!
# Exponential moments of stopping-cube sizes

A stochastic stretched-exponential tail gives the exponential-moment form
of the same estimate after increasing the scale.
-/

namespace Rigidity.Percolation

open LatticeProb MeasureTheory
open scoped ENNReal

private theorem integrable_exp_of_osBound_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hm : Measurable Y) (hn : ∀ ω, 0 ≤ Y ω) (ht : OsBound μ 1 1 Y) :
    Integrable (fun ω => Real.exp (Y ω / 32)) μ ∧
      (∫ ω, Real.exp (Y ω / 32) ∂μ) ≤ 2 := by
  have hbig := ht.lintegral_exp_half hm hn
  have hbigint : Integrable (fun ω => Real.exp (Y ω / 2)) μ := by
    refine ⟨?_, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (Real.exp_pos _).le)).2 ?_⟩
    · exact (by fun_prop : Measurable (fun ω => Real.exp (Y ω / 2))).aestronglyMeasurable
    · exact lt_of_le_of_lt hbig ENNReal.ofReal_lt_top
  have hbigbound : (∫ ω, Real.exp (Y ω / 2) ∂μ) ≤ Real.exp 2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)).mp
    rw [ofReal_integral_eq_lintegral_ofReal hbigint (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    exact hbig
  have hchord (ω : Ω) : Real.exp (Y ω / 32) ≤
      (15 / 16 : ℝ) + (1 / 16 : ℝ) * Real.exp (Y ω / 2) := by
    have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (Y ω / 2))
      (by norm_num : (0 : ℝ) ≤ 15 / 16) (by norm_num : (0 : ℝ) ≤ 1 / 16)
      (by norm_num : (15 / 16 : ℝ) + 1 / 16 = 1)
    have heq : (1 / 16 : ℝ) * (Y ω / 2) = Y ω / 32 := by ring
    simpa only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one, heq] using h
  have hsmall : Integrable (fun ω => Real.exp (Y ω / 32)) μ := by
    refine (hbigint.const_mul (1 / 16)).add (integrable_const (15 / 16 : ℝ)) |>.mono'
      (by fun_prop : Measurable (fun ω => Real.exp (Y ω / 32))).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simpa only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply] using (by linarith [hchord ω] :
      Real.exp (Y ω / 32) ≤ (1 / 16 : ℝ) * Real.exp (Y ω / 2) + 15 / 16)
  refine ⟨hsmall, ?_⟩
  have hi := integral_mono hsmall ((integrable_const (15 / 16 : ℝ)).add
    (hbigint.const_mul (1 / 16))) hchord
  change (∫ ω, Real.exp (Y ω / 32) ∂μ) ≤
    ∫ ω, ((15 / 16 : ℝ) + (1 / 16 : ℝ) * Real.exp (Y ω / 2)) ∂μ at hi
  rw [integral_add (integrable_const _) (hbigint.const_mul _), integral_const,
    integral_const_mul] at hi
  have hexp : Real.exp 2 ≤ 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hi
  linarith

/-- A measurable nonnegative variable with a stretched-exponential stochastic
bound has an exponential moment bounded by two at a larger scale. -/
theorem OsBound.exists_exp_rpow_integrable_le_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {s θ : ℝ} {X : Ω → ℝ}
    (hs : 0 < s) (hθ : 0 < θ) (hm : Measurable X) (hn : ∀ ω, 0 ≤ X ω)
    (ht : OsBound μ s θ X) :
    ∃ C : ℝ, 0 < C ∧ Integrable (fun ω => Real.exp ((X ω / C) ^ s)) μ ∧
      (∫ ω, Real.exp ((X ω / C) ^ s) ∂μ) ≤ 2 := by
  let C := θ * (32 : ℝ) ^ (1 / s)
  have hC : 0 < C := mul_pos hθ (Real.rpow_pos_of_pos (by norm_num) _)
  let Y : Ω → ℝ := fun ω => (max (X ω) 0 / θ) ^ s
  have hY : OsBound μ 1 1 Y := ht.normalized_rpow hs hθ
  have hYm : Measurable Y := by dsimp [Y]; fun_prop
  have hYn (ω : Ω) : 0 ≤ Y ω :=
    Real.rpow_nonneg (div_nonneg (le_max_right _ _) hθ.le) _
  obtain ⟨hi, hb⟩ := integrable_exp_of_osBound_one μ Y hYm hYn hY
  have heq (ω : Ω) : (X ω / C) ^ s = Y ω / 32 := by
    dsimp only [Y]
    rw [max_eq_left (hn ω)]
    dsimp [C]
    rw [div_mul_eq_div_div, Real.div_rpow (div_nonneg (hn ω) hθ.le)
      (Real.rpow_nonneg (by norm_num) _), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 32)]
    have h : (1 / s) * s = 1 := by field_simp
    rw [h, Real.rpow_one]
  refine ⟨C, hC, ?_, ?_⟩
  · simp_rw [heq]
    exact hi
  · simp_rw [heq]
    exact hb

end Rigidity.Percolation
