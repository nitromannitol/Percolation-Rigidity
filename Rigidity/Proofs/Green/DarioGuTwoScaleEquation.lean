import Rigidity.Proofs.Green.DarioGuHeatKernelInputs
import Rigidity.Proofs.Green.OpenHeatSemigroup

/-!
# The function `w` of Proposition 4.3 of Dario–Gu

Step 1 of the proof of Proposition 4.3 of Dario–Gu (lines 2245-2274 of the source) uses that
`v + q` solves the heat equation on the cluster from time `τ` with initial value `h(τ, ·, y)`, so
that `w = h - v - q` vanishes at time `τ` and `w(t) = h(t) - P_{t-τ} h(τ)`:

* `dgW_self`: `w(τ, ·, τ, y) = 0` (the initial condition of (4.25));
* `dgV_add_dgQ`: `v(t, x, τ, y) + q(t, x, τ, y) = Σ_z p(t - τ, x, z) h(τ, z, y)` when the series
  of `v` converges (the series of `q` always converges since `p̄(τ, ·)` is bounded);
* `dgW_eq_sub_tsum`: `w(t, x, τ, y) = h(t, x, y) - Σ_z p(t - τ, x, z) h(τ, z, y)`.
-/

open LatticeProb.Percolation

namespace Rigidity.Green

/-- The initial condition of (4.25): `w(τ, ·, τ, y) = 0`. -/
theorem dgW_self (ω : Configuration 2) (σ θ : ℝ) (χ : Fin 2 → Vertex 2 → ℝ) (τ : ℝ)
    (x y : Vertex 2) : dgW ω σ θ χ τ τ x y = 0 := by
  have hδ : ∀ f : Vertex 2 → ℝ, ∑' z, openHeat ω (τ - τ) x z * f z = f x := by
    intro f
    rw [sub_self]
    have e : (fun z => openHeat ω 0 x z * f z) = fun z => if z = x then f z else 0 := by
      funext z
      rw [openHeat_zero]
      by_cases hz : z = x
      · subst hz; simp
      · simp [Ne.symm hz, hz]
    rw [e]
    convert tsum_ite_eq x f
  unfold dgW dgV dgQ
  rw [hδ, hδ]
  ring

/-- The series of `q` converges for `t ≥ τ > 0` and `σ > 0`. -/
theorem summable_dgQ_term (ω : Configuration 2) {σ θ t τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ)
    (hτt : τ ≤ t) (x y : Vertex 2) :
    Summable fun z => openHeat ω (t - τ) x z * (θ⁻¹ * latticeGaussian σ τ z y) := by
  have hs : 0 ≤ t - τ := by linarith
  have hb : ∀ z, |θ⁻¹ * latticeGaussian σ τ z y| ≤ |θ⁻¹| * (2 * Real.pi * σ * τ)⁻¹ := by
    intro z
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    unfold latticeGaussian gaussianHeat
    have h0 : 0 < 2 * Real.pi * σ * τ := by positivity
    rw [abs_of_nonneg (by positivity)]
    calc (2 * Real.pi * σ * τ)⁻¹ * Real.exp (-(‖latticeEuclideanEmbedding z -
          latticeEuclideanEmbedding y‖ ^ 2 / (2 * σ * τ)))
        ≤ (2 * Real.pi * σ * τ)⁻¹ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [Real.exp_le_one_iff, neg_nonpos]
          positivity
      _ = (2 * Real.pi * σ * τ)⁻¹ := mul_one _
  refine Summable.of_norm_bounded ((hasSum_openHeat ω hs x).summable.mul_right
    (|θ⁻¹| * (2 * Real.pi * σ * τ)⁻¹)) fun z => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (openHeat_nonneg ω hs x z)]
  exact mul_le_mul_of_nonneg_left (hb z) (openHeat_nonneg ω hs x z)

/-- `v + q = P_{t-τ} h(τ)` when the series of `v` converges. -/
theorem dgV_add_dgQ (ω : Configuration 2) {σ θ t τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ)
    (hτt : τ ≤ t) (χ : Fin 2 → Vertex 2 → ℝ) (x y : Vertex 2)
    (hv : Summable fun z => openHeat ω (t - τ) x z *
      (dgTwoScale σ θ χ τ z y - θ⁻¹ * latticeGaussian σ τ z y)) :
    dgV ω σ θ χ t τ x y + dgQ ω σ θ t τ x y =
      ∑' z, openHeat ω (t - τ) x z * dgTwoScale σ θ χ τ z y := by
  unfold dgV dgQ
  rw [← hv.tsum_add (summable_dgQ_term ω hσ hτ hτt x y)]
  congr 1
  funext z
  ring

/-- `w(t) = h(t) - P_{t-τ} h(τ)` when the series of `v` converges. -/
theorem dgW_eq_sub_tsum (ω : Configuration 2) {σ θ t τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ)
    (hτt : τ ≤ t) (χ : Fin 2 → Vertex 2 → ℝ) (x y : Vertex 2)
    (hv : Summable fun z => openHeat ω (t - τ) x z *
      (dgTwoScale σ θ χ τ z y - θ⁻¹ * latticeGaussian σ τ z y)) :
    dgW ω σ θ χ t τ x y =
      dgTwoScale σ θ χ t x y - ∑' z, openHeat ω (t - τ) x z * dgTwoScale σ θ χ τ z y := by
  rw [← dgV_add_dgQ ω hσ hτ hτt χ x y hv]
  unfold dgW
  ring

end Rigidity.Green
