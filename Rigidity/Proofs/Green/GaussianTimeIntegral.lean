import Rigidity.Proofs.Green.FrullaniGaussian
import LatticeProb.Prob.Percolation.ContinuumGreen

/-!
# The time integral of the Gaussian kernel in dimension `d ≥ 3`

For `d ≥ 3`, `σ > 0` and `z ≠ 0` in `ℝ^d`, the Gaussian kernel
`p̄(t, z) = (2πσt)^{-d/2} exp(-|z|²/(2σt))` (`gaussianHeatD`, Dario–Gu (1.5) with `σ = σ̄²`) has

  `∫_0^∞ p̄(t, z) dt = Γ(d/2 - 1) / (2 π^{d/2} σ) |z|^{2-d}`  (`integral_gaussianHeatD`),

so that `θ^{-1} ∫_0^∞ p̄(t, z) dt` is the homogenized Green function `continuumGreen d κ z` with
`κ = σ θ / 2` (`integral_gaussianHeatD_eq_continuumGreen`). The proof is the Gamma integral
`∫_0^∞ t^{-a} e^{-b/t} dt = b^{1-a} Γ(a - 1)` (`integral_rpow_neg_mul_exp_neg_div`).
-/

open MeasureTheory Set Real

namespace Rigidity.Green

/-- The Gaussian kernel `p̄(t, z) = (2πσt)^{-d/2} exp(-|z|²/(2σt))` of `ℝ^d`. -/
noncomputable def gaussianHeatD (d : ℕ) (σ t : ℝ) (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (2 * Real.pi * σ * t) ^ (-((d : ℝ) / 2)) * Real.exp (-(‖z‖ ^ 2 / (2 * σ * t)))

theorem gaussianHeatD_eq {d : ℕ} {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin d)) :
    gaussianHeatD d σ t z = (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) *
      (t ^ (-((d : ℝ) / 2)) * Real.exp (-((‖z‖ ^ 2 / (2 * σ)) / t))) := by
  unfold gaussianHeatD
  rw [Real.mul_rpow (by positivity) ht.le, mul_assoc, div_div]

/-- **The time integral of the Gaussian kernel**:
`∫_0^∞ p̄(t, z) dt = Γ(d/2 - 1) / (2 π^{d/2} σ) |z|^{2-d}` for `d ≥ 3`, `z ≠ 0`. -/
theorem integral_gaussianHeatD {d : ℕ} (hd : 3 ≤ d) {σ : ℝ} (hσ : 0 < σ)
    {z : EuclideanSpace ℝ (Fin d)} (hz : z ≠ 0) :
    ∫ t in Ioi (0 : ℝ), gaussianHeatD d σ t z =
      Real.Gamma ((d : ℝ) / 2 - 1) / (2 * Real.pi ^ ((d : ℝ) / 2) * σ) *
        ‖z‖ ^ (2 - (d : ℝ)) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hb : 0 < ‖z‖ ^ 2 / (2 * σ) := by positivity
  rw [setIntegral_congr_fun measurableSet_Ioi fun t ht => gaussianHeatD_eq hσ ht z,
    integral_const_mul, (integral_rpow_neg_mul_exp_neg_div (by linarith) hb).2]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hz2 : (‖z‖ ^ 2) ^ (1 - (d : ℝ) / 2) = ‖z‖ ^ (2 - (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz0.le]
    congr 1
    push_cast
    ring
  have h2σ : 0 < 2 * σ := by positivity
  rw [show (2 * Real.pi * σ) = (2 * σ) * Real.pi by ring, Real.mul_rpow h2σ.le hpi.le,
    Real.div_rpow (sq_nonneg _) h2σ.le, hz2, Real.rpow_sub h2σ, Real.rpow_one,
    Real.rpow_neg h2σ.le, Real.rpow_neg hpi.le]
  have h1 : 0 < (2 * σ) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos h2σ _
  have h3 : 0 < Real.pi ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hpi _
  field_simp

/-- `θ^{-1} ∫_0^∞ p̄(t, z) dt = continuumGreen d κ z` with `κ = σ θ / 2`, for `d ≥ 3`. -/
theorem inv_mul_integral_gaussianHeatD_eq {d : ℕ} (hd : 3 ≤ d) (hd2 : 2 ≤ d) {σ θ : ℝ}
    (hσ : 0 < σ) (hθ : 0 < θ) (z : {x : EuclideanSpace ℝ (Fin d) // x ≠ 0}) :
    θ⁻¹ * ∫ t in Ioi (0 : ℝ), gaussianHeatD d σ t z.val =
      LatticeProb.Percolation.continuumGreen d hd2 ⟨σ * θ / 2, by positivity⟩ z := by
  rw [integral_gaussianHeatD hd hσ z.2]
  unfold LatticeProb.Percolation.continuumGreen
  rw [if_neg (by omega), Real.rpow_eq_pow, Real.rpow_eq_pow]
  have h3 : 0 < Real.pi ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  field_simp
  ring

end Rigidity.Green
