import Rigidity.Proofs.Green.GaussianTimeIntegral

/-!
# The product of two Gaussian kernels

`p̄(a, u) p̄(a, v) = p̄(2a, u - v) p̄(a/2, (u + v)/2)` (`gaussianHeatD_mul_gaussianHeatD`), from the
parallelogram law `|u|² + |v|² = |u - v|²/2 + 2|(u + v)/2|²`. With `u = z - x` and `v = z - y`
this writes `p̄(t/2, z - x) p̄(t/2, z - y)` as `p̄(t, x - y)` times the Gaussian kernel at time
`t/4` centred at the midpoint of `x` and `y`.
-/

namespace Rigidity.Green

variable {d : ℕ}

theorem norm_sq_add_norm_sq_eq (u v : EuclideanSpace ℝ (Fin d)) :
    ‖u‖ ^ 2 + ‖v‖ ^ 2 = ‖u - v‖ ^ 2 / 2 + 2 * ‖(1 / 2 : ℝ) • (u + v)‖ ^ 2 := by
  rw [norm_smul, mul_pow, norm_sub_sq_real, norm_add_sq_real]
  norm_num
  ring

/-- **The product of two Gaussian kernels.** -/
theorem gaussianHeatD_mul_gaussianHeatD {σ a : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (u v : EuclideanSpace ℝ (Fin d)) :
    gaussianHeatD d σ a u * gaussianHeatD d σ a v =
      gaussianHeatD d σ (2 * a) (u - v) * gaussianHeatD d σ (a / 2) ((1 / 2 : ℝ) • (u + v)) := by
  unfold gaussianHeatD
  have hc : (2 * Real.pi * σ * a) ^ (-((d : ℝ) / 2)) * (2 * Real.pi * σ * a) ^ (-((d : ℝ) / 2)) =
      (2 * Real.pi * σ * (2 * a)) ^ (-((d : ℝ) / 2)) *
        (2 * Real.pi * σ * (a / 2)) ^ (-((d : ℝ) / 2)) := by
    rw [← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    ring
  have he : Real.exp (-(‖u‖ ^ 2 / (2 * σ * a))) * Real.exp (-(‖v‖ ^ 2 / (2 * σ * a))) =
      Real.exp (-(‖u - v‖ ^ 2 / (2 * σ * (2 * a)))) *
        Real.exp (-(‖(1 / 2 : ℝ) • (u + v)‖ ^ 2 / (2 * σ * (a / 2)))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have h := norm_sq_add_norm_sq_eq u v
    field_simp
    linear_combination (-(2 : ℝ)) * h
  calc _ = ((2 * Real.pi * σ * a) ^ (-((d : ℝ) / 2)) * (2 * Real.pi * σ * a) ^ (-((d : ℝ) / 2))) *
        (Real.exp (-(‖u‖ ^ 2 / (2 * σ * a))) * Real.exp (-(‖v‖ ^ 2 / (2 * σ * a)))) := by ring
    _ = _ := by rw [hc, he]; ring

end Rigidity.Green
