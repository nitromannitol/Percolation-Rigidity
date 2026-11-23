import Rigidity.Proofs.Green.DarioGuHeatKernelInputs

/-!
# The time derivative of the two-scale expansion

The time part of Step 1 of the proof of Proposition 4.3 of Dario–Gu: the derivative in time of the
Gaussian kernel, `∂_t p̄(t, z) = p̄(t, z) (|z|²/(2σt²) - 1/t)` (`hasDerivAt_gaussianHeat_time`), and of
the two-scale expansion `h(t, x, y) = θ^{-1}(p̄(t, x - y) + Σ_k D_k p̄(t, · - y)(x) χ_k(x))`
(`hasDerivAt_dgTwoScale_time`).
-/

open LatticeProb.Percolation

namespace Rigidity.Green

/-- `∂_t p̄(t, z)` for the planar Gaussian kernel `p̄(t, z) = (2πσt)^{-1} exp(-|z|²/(2σt))`. -/
noncomputable def gaussianHeatTimeDeriv (σ t : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  gaussianHeat σ t z * (‖z‖ ^ 2 / (2 * σ * t ^ 2) - 1 / t)

theorem hasDerivAt_gaussianHeat_time {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin 2)) :
    HasDerivAt (fun s => gaussianHeat σ s z) (gaussianHeatTimeDeriv σ t z) t := by
  have hc : (2 * Real.pi * σ * t) ≠ 0 := by positivity
  have hd : (2 * σ * t) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s => (2 * Real.pi * σ * s)⁻¹)
      (-(2 * Real.pi * σ * 1) / (2 * Real.pi * σ * t) ^ 2) t :=
    ((hasDerivAt_id t).const_mul (2 * Real.pi * σ)).inv hc
  have h2 : HasDerivAt (fun s => -(‖z‖ ^ 2 / (2 * σ * s)))
      (-((0 * (2 * σ * t) - ‖z‖ ^ 2 * (2 * σ * 1)) / (2 * σ * t) ^ 2)) t :=
    ((hasDerivAt_const t (‖z‖ ^ 2)).div ((hasDerivAt_id t).const_mul (2 * σ)) hd).neg
  have h := h1.mul h2.exp
  unfold gaussianHeatTimeDeriv gaussianHeat
  refine h.congr_deriv ?_
  field_simp
  ring

/-- `∂_t p̄(t, x - y)` at lattice points. -/
noncomputable def latticeGaussianTimeDeriv (σ t : ℝ) (x y : Vertex 2) : ℝ :=
  gaussianHeatTimeDeriv σ t (latticeEuclideanEmbedding x - latticeEuclideanEmbedding y)

theorem hasDerivAt_latticeGaussian_time {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (x y : Vertex 2) :
    HasDerivAt (fun s => latticeGaussian σ s x y) (latticeGaussianTimeDeriv σ t x y) t :=
  hasDerivAt_gaussianHeat_time hσ ht _

/-- **The time derivative of the two-scale expansion** (4.1):
`∂_t h(t, x, y) = θ^{-1}(∂_t p̄(t, x - y) + Σ_k (∂_t p̄(t, x + e_k - y) - ∂_t p̄(t, x - y)) χ_k(x))`. -/
theorem hasDerivAt_dgTwoScale_time {σ θ t : ℝ} (hσ : 0 < σ) (ht : 0 < t)
    (χ : Fin 2 → Vertex 2 → ℝ) (x y : Vertex 2) :
    HasDerivAt (fun s => dgTwoScale σ θ χ s x y)
      (θ⁻¹ * (latticeGaussianTimeDeriv σ t x y + ∑ k : Fin 2,
        (latticeGaussianTimeDeriv σ t (x + Pi.single k 1) y - latticeGaussianTimeDeriv σ t x y) *
          χ k x)) t := by
  unfold dgTwoScale
  refine ((hasDerivAt_latticeGaussian_time hσ ht x y).add
    (HasDerivAt.fun_sum fun k _ => ((hasDerivAt_latticeGaussian_time hσ ht _ y).sub
      (hasDerivAt_latticeGaussian_time hσ ht x y)).mul_const (χ k x))).const_mul θ⁻¹

end Rigidity.Green
