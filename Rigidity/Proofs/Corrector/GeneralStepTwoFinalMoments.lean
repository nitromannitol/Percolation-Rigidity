import Rigidity.Proofs.Corrector.GeneralStepTwoPathBound
import Rigidity.Proofs.Green.GeneralFluxBox

/-!
# The moments of the pieces of the weight of the Step 2 sum on `ℤᵈ`

* `growthMoments_size_pow`: `(1 + 3^d) σ(y)^d`, `σ` the stopping size of the good cubes of `ℤᵈ`,
  has moments of polynomial growth uniformly in `y`, from the exponential moment of `σ(y)`
  (`growthMomentsD_of_exp_moment`, `GrowthMomentsD.pow_nat`);
* `growthMoments_ballSum`: a sum over the ball of radius `Kσ(y)` of variables with moments of
  polynomial growth has such moments, uniformly in `y`
  (`lintegral_randomBallSum_rpow_le_of_growth`);
* `growthMoments_weightMajorant_zero`: the weighted number of anchor regions has them.

This is the planar file `DarioStepTwoFinalMoments` on `ℤᵈ`, with the moments `GrowthMomentsD`. The
bound `81σ(y)²` of the planar anchor regions becomes `(1 + 3^d) σ(y)^d`, and the radius `12σ(y)` of
the planar ball sums becomes a radius `Kσ(y)` for any `K > 0`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open Rigidity.Green.GeneralFlux (GrowthMomentsD growthMomentsD_of_exp_moment)
open scoped Classical ENNReal

variable {d : ℕ} {p : unitInterval}

/-- **The moments of `(1 + 3^d) σ(y)^d`**, uniformly in `y`. -/
theorem growthMoments_size_pow [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ)) :
    ∃ B k : ℝ, 0 < B ∧ 0 < k ∧ ∀ y : Vertex d, GrowthMomentsD p
      (fun ω => ENNReal.ofReal
        ((1 + 3 ^ d) * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y ^ d)) B k := by
  obtain ⟨θ', hθ', hexp⟩ := (partition_estimates hd hpc).2.1
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  refine ⟨(1 + 3 ^ d) * ((2 * θ') ^ d * (d : ℝ) ^ (d : ℝ)), d, by positivity, hd0,
    fun y => ?_⟩
  have h1 := growthMomentsD_of_exp_moment (p := p)
    (X := fun ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y)
    (fun ω => TriadicCube.stoppingSize_nonneg _ y) hθ' one_pos
    (by simpa only [Real.rpow_one] using (hexp y).1)
    (by simpa only [Real.rpow_one] using (hexp y).2)
  rw [div_one, Real.one_rpow, mul_one] at h1
  have h2 := (h1.pow_nat (by positivity) d hd1).const_mul (c := 1 + 3 ^ d) (by positivity)
    (by positivity)
  rw [mul_one] at h2
  refine h2.mono fun ω => le_of_eq ?_
  rw [ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (TriadicCube.stoppingSize_nonneg _ y), ENNReal.rpow_natCast]

/-- **The moments of a sum over the ball of radius `Kσ(y)`**, uniformly in `y`. -/
theorem growthMoments_ballSum [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ))
    {K : ℝ} (hK : 0 < K) {Y : Vertex d → Configuration d → ℝ≥0∞} (hY : ∀ z, Measurable (Y z))
    {B k : ℝ} (hB : 0 < B) (hk : 0 < k) (hYm : ∀ z, GrowthMomentsD p (Y z) B k) :
    ∃ B' k' : ℝ, 0 < B' ∧ 0 < k' ∧ ∀ y : Vertex d, GrowthMomentsD p
      (fun ω => ∑' z, if ‖latticeEuclideanEmbedding (z - y)‖ ≤
        K * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y then Y z ω else 0) B' k' := by
  obtain ⟨θ', hθ', hexp⟩ := (partition_estimates hd hpc).2.1
  refine ⟨(2 * (1 + 8 * d * (K * θ'))) ^ d * Real.sqrt 2 * (B * 2 ^ k), k + d, by positivity,
    by positivity, fun y q hq => ?_⟩
  exact lintegral_randomBallSum_rpow_le_of_growth y (θ := K * θ') (by positivity)
    (fun t _ => measure_le_mul_stoppingSize_le hθ' hK y (hexp y).1 (hexp y).2 t)
    ((measurable_stoppingSize_goodCubes y).const_mul K) hY hB hYm hq

/-- **The moments of the weighted number of anchor regions.** -/
theorem growthMoments_weightMajorant_zero [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ A k : ℝ, 0 < A ∧ 0 < k ∧ ∀ z : Vertex d,
      GrowthMomentsD p (weightMajorant (fun _ _ => 0) (3 * d) (4 * d) z) A k := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  refine growthMoments_weightMajorant hd hpc (fun _ => measurable_const) one_pos one_pos
    (fun z q hq => ?_) (by positivity) (by positivity)
  have hq0 : 0 ≤ q := by linarith
  simp only [add_zero, ENNReal.ofReal_one, ENNReal.one_rpow, lintegral_const, measure_univ,
    mul_one, one_mul, Real.rpow_one]
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  exact Real.one_le_rpow hq hq0

end Rigidity.Corrector.GeneralDim
