import Rigidity.Proofs.Green.GaussianShiftD

/-!
# The oscillation of the Gaussian kernel on `ℝ^d` near a point

If `|u - z|, |v - z| ≤ L ≤ 2√t`, then

  `|p̄(t, u) - p̄(t, v)| ≤ K_σ (L / √t) (2πσt)^{-d/2} e^{-|z|²/(16σt)}`,
  `K_σ = (2√(8σ) + 4) e^{8/σ + 1/(2σ)} / σ`

(`abs_gaussianHeatD_sub_le_of_near`), the `d`-dimensional form of
`abs_gaussianHeat_sub_le_of_near`, from `abs_gaussianHeatD_sub_le` with `ρ = 2L`.
-/

namespace Rigidity.Green

variable {d : ℕ}

/-- The constant `K_σ` of the oscillation bound. -/
noncomputable def gaussOscConstD (σ : ℝ) : ℝ :=
  (2 * Real.sqrt (8 * σ) + 4) * Real.exp (8 / σ + 1 / (2 * σ)) / σ

/-- **The oscillation of the Gaussian kernel near a point.** -/
theorem abs_gaussianHeatD_sub_le_of_near {σ t L : ℝ} (hσ : 0 < σ) (ht : 0 < t) (hL : 0 ≤ L)
    (hLt : L ≤ 2 * Real.sqrt t) {z u v : EuclideanSpace ℝ (Fin d)} (hu : ‖u - z‖ ≤ L)
    (hv : ‖v - z‖ ≤ L) :
    |gaussianHeatD d σ t u - gaussianHeatD d σ t v| ≤
      gaussOscConstD σ * (L / Real.sqrt t) *
        ((2 * Real.pi * σ * t) ^ (-((d : ℝ) / 2)) * Real.exp (-(‖z‖ ^ 2 / (16 * σ * t)))) := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have htt : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have huv : ‖u - v‖ ≤ 2 * L := by
    calc ‖u - v‖ = ‖(u - z) - (v - z)‖ := by congr 1; abel
      _ ≤ ‖u - z‖ + ‖v - z‖ := norm_sub_le _ _
      _ ≤ 2 * L := by linarith
  have h := abs_gaussianHeatD_sub_le (d := d) hσ ht (by linarith : 0 ≤ 2 * L) huv
  refine h.trans ?_
  set P := (2 * Real.pi * σ * t) ^ (-((d : ℝ) / 2)) with hP
  have hP0 : 0 ≤ P := by positivity
  set nu := ‖u‖ with hnu
  have hnu0 : 0 ≤ nu := norm_nonneg _
  have hz : ‖z‖ ≤ nu + L := by
    have := norm_sub_norm_le z u
    rw [norm_sub_rev] at this
    linarith
  have hL2 : L ^ 2 ≤ 4 * t := by
    have := mul_le_mul hLt hLt hL (by positivity)
    nlinarith [htt]
  -- the factors
  have hE1 : Real.exp ((2 * L) ^ 2 / (2 * σ * t)) ≤ Real.exp (8 / σ) := by
    apply Real.exp_le_exp.2
    rw [div_le_div_iff₀ (by positivity) hσ]
    have : (2 * L) ^ 2 ≤ 16 * t := by nlinarith
    nlinarith [this]
  have hsplit : Real.exp (-(nu ^ 2 / (4 * σ * t))) =
      Real.exp (-(nu ^ 2 / (8 * σ * t))) * Real.exp (-(nu ^ 2 / (8 * σ * t))) := by
    rw [← Real.exp_add]; congr 1; ring
  have hx := mul_exp_neg_sq_div_le hnu0 (by positivity : 0 < 8 * σ * t)
  have hE8 : Real.exp (-(nu ^ 2 / (8 * σ * t))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]; positivity
  have hsq8 : Real.sqrt (8 * σ * t) = Real.sqrt (8 * σ) * Real.sqrt t :=
    Real.sqrt_mul (by positivity) t
  have hlin : (2 * nu + 2 * L) * Real.exp (-(nu ^ 2 / (4 * σ * t))) ≤
      (2 * Real.sqrt (8 * σ) + 4) * Real.sqrt t * Real.exp (-(nu ^ 2 / (8 * σ * t))) := by
    rw [hsplit]
    have h1 : 2 * nu * (Real.exp (-(nu ^ 2 / (8 * σ * t))) * Real.exp (-(nu ^ 2 / (8 * σ * t)))) ≤
        2 * Real.sqrt (8 * σ) * Real.sqrt t * Real.exp (-(nu ^ 2 / (8 * σ * t))) := by
      have : nu * Real.exp (-(nu ^ 2 / (8 * σ * t))) ≤ Real.sqrt (8 * σ) * Real.sqrt t := by
        rw [← hsq8]; exact hx
      calc 2 * nu * (Real.exp (-(nu ^ 2 / (8 * σ * t))) * Real.exp (-(nu ^ 2 / (8 * σ * t))))
          = 2 * (nu * Real.exp (-(nu ^ 2 / (8 * σ * t)))) *
            Real.exp (-(nu ^ 2 / (8 * σ * t))) := by ring
        _ ≤ 2 * (Real.sqrt (8 * σ) * Real.sqrt t) * Real.exp (-(nu ^ 2 / (8 * σ * t))) := by
            gcongr
        _ = _ := by ring
    have h2 : 2 * L * (Real.exp (-(nu ^ 2 / (8 * σ * t))) * Real.exp (-(nu ^ 2 / (8 * σ * t)))) ≤
        4 * Real.sqrt t * Real.exp (-(nu ^ 2 / (8 * σ * t))) := by
      have hE0 : 0 ≤ Real.exp (-(nu ^ 2 / (8 * σ * t))) := (Real.exp_pos _).le
      calc 2 * L * (Real.exp (-(nu ^ 2 / (8 * σ * t))) * Real.exp (-(nu ^ 2 / (8 * σ * t))))
          ≤ 2 * L * (Real.exp (-(nu ^ 2 / (8 * σ * t))) * 1) := by gcongr
        _ ≤ 2 * (2 * Real.sqrt t) * Real.exp (-(nu ^ 2 / (8 * σ * t))) := by
            rw [mul_one]; gcongr
        _ = _ := by ring
    linarith [h1, h2]
  have hzexp : Real.exp (-(nu ^ 2 / (8 * σ * t))) ≤
      Real.exp (1 / (2 * σ)) * Real.exp (-(‖z‖ ^ 2 / (16 * σ * t))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hz2 : ‖z‖ ^ 2 ≤ 2 * nu ^ 2 + 8 * t := by
      have h1 : ‖z‖ ^ 2 ≤ (nu + L) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      nlinarith [sq_nonneg (nu - L), hL2]
    have e : 1 / (2 * σ) = 8 * t / (16 * σ * t) := by field_simp; try ring
    have e2 : nu ^ 2 / (8 * σ * t) = 2 * nu ^ 2 / (16 * σ * t) := by field_simp; try ring
    rw [e, e2, ← sub_eq_add_neg, ← sub_div, neg_le, ← neg_div, neg_sub]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  -- the assembly
  have hfac : 2 * L * (2 * nu + 2 * L) / (2 * σ * t) * Real.exp ((2 * L) ^ 2 / (2 * σ * t)) *
      (P * Real.exp (-(nu ^ 2 / (4 * σ * t)))) =
      L / (σ * t) * Real.exp ((2 * L) ^ 2 / (2 * σ * t)) * P *
        ((2 * nu + 2 * L) * Real.exp (-(nu ^ 2 / (4 * σ * t)))) := by
    ring
  rw [hfac]
  have hA : 0 ≤ L / (σ * t) * Real.exp ((2 * L) ^ 2 / (2 * σ * t)) * P := by positivity
  calc L / (σ * t) * Real.exp ((2 * L) ^ 2 / (2 * σ * t)) * P *
        ((2 * nu + 2 * L) * Real.exp (-(nu ^ 2 / (4 * σ * t))))
      ≤ L / (σ * t) * Real.exp ((2 * L) ^ 2 / (2 * σ * t)) * P *
        ((2 * Real.sqrt (8 * σ) + 4) * Real.sqrt t *
          (Real.exp (1 / (2 * σ)) * Real.exp (-(‖z‖ ^ 2 / (16 * σ * t))))) := by
        refine mul_le_mul_of_nonneg_left (hlin.trans ?_) hA
        exact mul_le_mul_of_nonneg_left hzexp (by positivity)
    _ ≤ L / (σ * t) * Real.exp (8 / σ) * P *
        ((2 * Real.sqrt (8 * σ) + 4) * Real.sqrt t *
          (Real.exp (1 / (2 * σ)) * Real.exp (-(‖z‖ ^ 2 / (16 * σ * t))))) := by
        gcongr
    _ = _ := by
        unfold gaussOscConstD
        rw [Real.exp_add]
        have hq : L / (σ * t) * Real.sqrt t = L / Real.sqrt t / σ := by
          rw [div_mul_eq_mul_div, div_div, div_eq_div_iff (by positivity) (by positivity)]
          have : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
          calc L * Real.sqrt t * (Real.sqrt t * σ) = L * σ * (Real.sqrt t * Real.sqrt t) := by ring
            _ = L * (σ * t) := by rw [this]; ring
        calc L / (σ * t) * Real.exp (8 / σ) * P * ((2 * Real.sqrt (8 * σ) + 4) * Real.sqrt t *
              (Real.exp (1 / (2 * σ)) * Real.exp (-(‖z‖ ^ 2 / (16 * σ * t)))))
            = (L / (σ * t) * Real.sqrt t) * ((2 * Real.sqrt (8 * σ) + 4) *
              (Real.exp (8 / σ) * Real.exp (1 / (2 * σ)))) *
              (P * Real.exp (-(‖z‖ ^ 2 / (16 * σ * t)))) := by ring
          _ = _ := by rw [hq]; ring

end Rigidity.Green
