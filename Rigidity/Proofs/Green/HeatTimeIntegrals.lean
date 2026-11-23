import Rigidity.Proofs.Green.FrullaniGaussian

/-!
# Elementary bounds on time integrals of heat kernels

Bounds used in Dario–Gu, §5 (proof of Theorem 2):

* a function bounded by `B` on `(0, S]` and by `A t^{-β}` on `(S, ∞)`, `β > 1`, is integrable on
  `(0, ∞)`, with `∫ |h| ≤ B S + A S^{1-β}/(β - 1)`;
* bounds on the planar Gaussian kernel: `p̄(t, z) ≤ e^{-|z|/(4σ)}/|z|²` for `t ≤ |z|`,
  `p̄(t, e) ≤ 1` for `|e| = 1`, `|p̄(t, 0) - p̄(t, e)| ≤ 1/(4πσ²t²)`, `p̄(t, z) ≤ 1/(2πσt)`;
* `r² e^{-r/C} ≤ 2C²`.
-/

open MeasureTheory Set Real Filter Topology

namespace Rigidity.Green

/-- A function bounded by `B` on `(0, S]` and by `A t^{-β}` on `(S, ∞)`, `β > 1`, is integrable
on `(0, ∞)` and `∫ |h| ≤ B S + A S^{1-β}/(β - 1)`. -/
theorem integrableOn_Ioi_of_le {h : ℝ → ℝ} (hm : AEStronglyMeasurable h volume)
    {S B A β : ℝ} (hS : 0 < S) (hβ : 1 < β)
    (h1 : ∀ t ∈ Ioc 0 S, |h t| ≤ B) (h2 : ∀ t ∈ Ioi S, |h t| ≤ A * t ^ (-β)) :
    IntegrableOn h (Ioi 0) ∧ ∫ t in Ioi (0 : ℝ), |h t| ≤ B * S + A * (S ^ (1 - β) / (β - 1)) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 S ∪ Ioi S := (Ioc_union_Ioi_eq_Ioi hS.le).symm
  have hI1 : IntegrableOn h (Ioc 0 S) := by
    refine Measure.integrableOn_of_bounded (M := B) measure_Ioc_lt_top.ne hm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs]
    exact h1 t ht
  have hpow : IntegrableOn (fun t : ℝ => A * t ^ (-β)) (Ioi S) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hS).const_mul A
  have hI2 : IntegrableOn h (Ioi S) := by
    refine hpow.mono' hm.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs]
    exact h2 t ht
  have hint : IntegrableOn h (Ioi 0) := by
    rw [hsplit]
    exact hI1.union hI2
  refine ⟨hint, ?_⟩
  rw [hsplit, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi (Integrable.abs hI1)
    (Integrable.abs hI2)]
  have hb1 : ∫ t in Ioc 0 S, |h t| ≤ B * S := by
    calc ∫ t in Ioc 0 S, |h t| ≤ ∫ _t in Ioc 0 S, B :=
          setIntegral_mono_on (Integrable.abs hI1) (integrableOn_const measure_Ioc_lt_top.ne)
            measurableSet_Ioc fun t ht => h1 t ht
      _ = B * S := by
          rw [← intervalIntegral.integral_of_le hS.le, intervalIntegral.integral_const,
            smul_eq_mul]
          ring
  have hb2 : ∫ t in Ioi S, |h t| ≤ A * (S ^ (1 - β) / (β - 1)) := by
    calc ∫ t in Ioi S, |h t| ≤ ∫ t in Ioi S, A * t ^ (-β) :=
          setIntegral_mono_on (Integrable.abs hI2) hpow measurableSet_Ioi fun t ht => h2 t ht
      _ = A * (S ^ (1 - β) / (β - 1)) := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (show -β < -1 by linarith) hS]
          congr 1
          have e1 : -β + 1 = -(β - 1) := by ring
          rw [e1, div_neg, neg_div, neg_neg, show -(β - 1) = 1 - β by ring]
  linarith

/-- `x e^{-x} ≤ 1`. -/
theorem mul_exp_neg_le_one (x : ℝ) : x * Real.exp (-x) ≤ 1 := by
  have h := Real.add_one_le_exp x
  have hpos := Real.exp_pos x
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hpos]
  linarith

/-- `r² e^{-r/C} ≤ 2C²` for `C > 0`, `r ≥ 0`. -/
theorem sq_mul_exp_neg_div_le {C r : ℝ} (hC : 0 < C) (hr : 0 ≤ r) :
    r ^ 2 * Real.exp (-(r / C)) ≤ 2 * C ^ 2 := by
  have hq := Real.quadratic_le_exp_of_nonneg (div_nonneg hr hC.le)
  have hpos := Real.exp_pos (r / C)
  have hC0 : C ≠ 0 := hC.ne'
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
  have h1 : r ^ 2 = 2 * C ^ 2 * ((r / C) ^ 2 / 2) := by field_simp
  rw [h1]
  have h2 : (r / C) ^ 2 / 2 ≤ Real.exp (r / C) := by nlinarith [div_nonneg hr hC.le]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `p̄(t, z) ≤ (2πσt)^{-1}`. -/
theorem gaussianHeat_le_inv {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (z : EuclideanSpace ℝ (Fin 2)) :
    gaussianHeat σ t z ≤ (2 * Real.pi * σ * t)⁻¹ := by
  unfold gaussianHeat
  have := Real.pi_pos
  have h1 : Real.exp (-(‖z‖ ^ 2 / (2 * σ * t))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    positivity
  calc (2 * Real.pi * σ * t)⁻¹ * Real.exp (-(‖z‖ ^ 2 / (2 * σ * t)))
      ≤ (2 * Real.pi * σ * t)⁻¹ * 1 := by gcongr
    _ = _ := mul_one _

/-- `p̄(t, z) → 0` as `t → ∞`. -/
theorem tendsto_gaussianHeat_atTop {σ : ℝ} (hσ : 0 < σ) (z : EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun t => gaussianHeat σ t z) atTop (𝓝 0) := by
  have hinv : Tendsto (fun t : ℝ => (2 * Real.pi * σ * t)⁻¹) atTop (𝓝 0) := by
    have := Real.pi_pos
    exact (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi * σ)).inv_tendsto_atTop
  refine squeeze_zero' ?_ ?_ hinv
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact gaussianHeat_nonneg hσ ht.le z
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact gaussianHeat_le_inv hσ ht z

/-- `p̄(t, e) ≤ 1` for `|e| = 1` and `t > 0`. -/
theorem gaussianHeat_unit_le_one {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t)
    {e : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1) : gaussianHeat σ t e ≤ 1 := by
  unfold gaussianHeat
  rw [he, one_pow]
  have hpi := Real.pi_pos
  set x := 1 / (2 * σ * t) with hx
  have hx0 : 0 < x := by positivity
  have hinv : (2 * Real.pi * σ * t)⁻¹ = x / Real.pi := by rw [hx]; field_simp
  rw [hinv]
  have h1 := mul_exp_neg_le_one x
  have hpi1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  calc x / Real.pi * Real.exp (-x) = x * Real.exp (-x) / Real.pi := by ring
    _ ≤ 1 / Real.pi := by gcongr
    _ ≤ 1 := by rw [div_le_one hpi]; exact hpi1

/-- `|p̄(t, 0) - p̄(t, e)| ≤ 1/(4πσ²t²)` for `|e| = 1` and `t > 0`. -/
theorem abs_gaussianHeat_zero_sub_unit_le {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t)
    {e : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1) :
    |gaussianHeat σ t 0 - gaussianHeat σ t e| ≤ (4 * Real.pi * σ ^ 2) ⁻¹ * t ^ (-(2 : ℝ)) := by
  unfold gaussianHeat
  rw [he, norm_zero, one_pow]
  have hpi := Real.pi_pos
  set y := 1 / (2 * σ * t) with hy
  have hy0 : 0 < y := by positivity
  have h0 : (0 : ℝ) ^ 2 / (2 * σ * t) = 0 := by simp
  rw [h0, neg_zero, Real.exp_zero, mul_one]
  have hey : Real.exp (-y) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have h1 : 1 - Real.exp (-y) ≤ y := by linarith [Real.add_one_le_exp (-y)]
  have hdiff : (2 * Real.pi * σ * t)⁻¹ - (2 * Real.pi * σ * t)⁻¹ * Real.exp (-y) =
      (2 * Real.pi * σ * t)⁻¹ * (1 - Real.exp (-y)) := by ring
  rw [hdiff, abs_of_nonneg (mul_nonneg (by positivity) (by linarith))]
  rw [Real.rpow_neg ht.le, Real.rpow_two]
  calc (2 * Real.pi * σ * t)⁻¹ * (1 - Real.exp (-y)) ≤ (2 * Real.pi * σ * t)⁻¹ * y := by gcongr
    _ = (4 * Real.pi * σ ^ 2)⁻¹ * (t ^ 2)⁻¹ := by rw [hy]; field_simp; ring

/-- **Small times for the Gaussian kernel**: `p̄(t, z) ≤ e^{-|z|/(4σ)} / |z|²` for
`0 < t ≤ |z|`. -/
theorem gaussianHeat_le_of_le_norm {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t)
    {z : EuclideanSpace ℝ (Fin 2)} (htz : t ≤ ‖z‖) :
    gaussianHeat σ t z ≤ Real.exp (-(‖z‖ / (4 * σ))) / ‖z‖ ^ 2 := by
  have hr : 0 < ‖z‖ := lt_of_lt_of_le ht htz
  have hpi := Real.pi_pos
  unfold gaussianHeat
  set x := ‖z‖ ^ 2 / (2 * σ * t) with hx
  have hx0 : 0 < x := by positivity
  have hxr : ‖z‖ / (2 * σ) ≤ x := by
    rw [hx, div_le_div_iff₀ (by positivity) (by positivity)]
    have : ‖z‖ * (2 * σ * t) ≤ ‖z‖ ^ 2 * (2 * σ) := by
      nlinarith [mul_le_mul_of_nonneg_left htz (by positivity : (0 : ℝ) ≤ ‖z‖ * (2 * σ))]
    linarith
  have hinv : (2 * Real.pi * σ * t)⁻¹ = x / (Real.pi * ‖z‖ ^ 2) := by rw [hx]; field_simp
  rw [hinv]
  have hhalf : x * Real.exp (-(x / 2)) ≤ 2 := by
    have h := mul_exp_neg_le_one (x / 2)
    calc x * Real.exp (-(x / 2)) = 2 * (x / 2 * Real.exp (-(x / 2))) := by ring
      _ ≤ 2 * 1 := by gcongr
      _ = 2 := by norm_num
  have hsplit : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have he2 : Real.exp (-(x / 2)) ≤ Real.exp (-(‖z‖ / (4 * σ))) := by
    apply Real.exp_le_exp.mpr
    have : ‖z‖ / (4 * σ) = ‖z‖ / (2 * σ) / 2 := by ring
    rw [this]
    linarith
  have hpi2 : 2 ≤ Real.pi := by linarith [Real.pi_gt_three]
  calc x / (Real.pi * ‖z‖ ^ 2) * Real.exp (-x)
      = (x * Real.exp (-(x / 2))) * Real.exp (-(x / 2)) / (Real.pi * ‖z‖ ^ 2) := by
        rw [hsplit]; ring
    _ ≤ 2 * Real.exp (-(‖z‖ / (4 * σ))) / (Real.pi * ‖z‖ ^ 2) := by
        gcongr
    _ ≤ Real.exp (-(‖z‖ / (4 * σ))) / ‖z‖ ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := Real.exp_pos (-(‖z‖ / (4 * σ)))
        nlinarith [sq_nonneg ‖z‖, mul_pos this (pow_pos hr 2)]

end Rigidity.Green
