import Rigidity.Proofs.Corrector.DarioStepTwoPathBound

/-!
# The moments of the pieces of the weight of the Step 2 sum

* `growthMoments_sq_of_exp_moment`: a nonnegative variable with a stretched exponential moment has
  a square with moments of polynomial growth;
* `growthMoments_planarSize_sq`: so does `81σ(y)²`, `σ` the size of the planar partition,
  uniformly in `y`;
* `growthMoments_planarBallSum`: a sum over the ball of radius `12σ(y)` of variables with moments
  of polynomial growth has such moments, uniformly in `y`
  (`lintegral_randomBallSum_rpow_le_of_growth`);
* `growthMoments_weightMajorant_zero`: the weighted number of anchor regions has them.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

variable {p : unitInterval}

theorem growthMoments_sq_of_exp_moment {X : Configuration 2 → ℝ} (hXm : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s)
    (hint : Integrable (fun ω => Real.exp ((X ω / θ) ^ s)) (latticeBondLaw 2 p))
    (hb : ∫ ω, Real.exp ((X ω / θ) ^ s) ∂latticeBondLaw 2 p ≤ 2) :
    GrowthMoments p (fun ω => ENNReal.ofReal (X ω ^ 2))
      ((2 * θ * (1 / s) ^ (1 / s)) * (2 * θ * (1 / s) ^ (1 / s)) * 2 ^ (1 / s + 1 / s))
      (1 / s + 1 / s) := by
  have h1 := growthMoments_of_exp_moment hX0 hθ hs hint hb
  have hm : AEMeasurable (fun ω => ENNReal.ofReal (X ω)) (latticeBondLaw 2 p) :=
    hXm.ennreal_ofReal.aemeasurable
  have h2 := GrowthMoments.mul hm hm h1 h1 (by positivity) (by positivity)
  refine h2.mono fun ω => le_of_eq ?_
  rw [sq, ENNReal.ofReal_mul (hX0 ω)]

/-- **The moments of `81σ(y)²`.** -/
theorem growthMoments_planarSize_sq (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ B k : ℝ, 0 < B ∧ 0 < k ∧ ∀ y : Vertex 2, GrowthMoments p
      (fun ω => ENNReal.ofReal (81 * TriadicCube.stoppingSize (planarGoodCubes ω) y ^ 2)) B k := by
  obtain ⟨θ', hθ', hexp⟩ := (planar_meshed_partition_estimates hpc).2.1
  refine ⟨81 * ((2 * θ' * (1 / 1 : ℝ) ^ ((1 : ℝ) / 1)) * (2 * θ' * (1 / 1 : ℝ) ^ ((1 : ℝ) / 1)) *
      (2 : ℝ) ^ ((1 : ℝ) / 1 + (1 : ℝ) / 1)), (1 : ℝ) / 1 + (1 : ℝ) / 1, by positivity, by norm_num,
    fun y => ?_⟩
  have hint : Integrable (fun ω => Real.exp ((TriadicCube.stoppingSize (planarGoodCubes ω) y /
      θ') ^ (1 : ℝ))) (latticeBondLaw 2 p) := by
    simp only [Real.rpow_one]
    exact (hexp y).1
  have hb : ∫ ω, Real.exp ((TriadicCube.stoppingSize (planarGoodCubes ω) y / θ') ^ (1 : ℝ))
      ∂latticeBondLaw 2 p ≤ 2 := by
    simp only [Real.rpow_one]
    exact (hexp y).2
  have h := growthMoments_sq_of_exp_moment (measurable_stoppingSize_planar y)
    (fun ω => stoppingSize_nonneg' _ y) hθ' one_pos hint hb
  have h81 := h.const_mul (c := 81) (by norm_num) (by positivity)
  refine h81.mono fun ω => le_of_eq ?_
  rw [ENNReal.ofReal_mul (by norm_num)]

/-- **The moments of a sum over the ball of radius `12σ(y)`.** -/
theorem growthMoments_planarBallSum (hpc : criticalProbability 2 < (p : ℝ))
    {Y : Vertex 2 → Configuration 2 → ℝ≥0∞} (hY : ∀ z, Measurable (Y z)) {B k : ℝ} (hB : 0 < B)
    (hk : 0 < k) (hYm : ∀ z, GrowthMoments p (Y z) B k) :
    ∃ B' k' : ℝ, 0 < B' ∧ 0 < k' ∧ ∀ y : Vertex 2, GrowthMoments p
      (fun ω => ∑' z, if ‖latticeEuclideanEmbedding (z - y)‖ ≤
        12 * TriadicCube.stoppingSize (planarGoodCubes ω) y then Y z ω else 0) B' k' := by
  obtain ⟨θ', hθ', hexp⟩ := (planar_meshed_partition_estimates hpc).2.1
  refine ⟨4 * (1 + 8 * (12 * θ')) ^ 2 * Real.sqrt 2 * (B * 2 ^ k), k + 2, by positivity,
    by linarith, fun y q hq => ?_⟩
  exact lintegral_randomBallSum_rpow_le_of_growth y (θ := 12 * θ') (by positivity)
    (fun t _ => measure_le_mul_stoppingSize_le hθ' (by norm_num : (0 : ℝ) < 12) y (hexp y).1
      (hexp y).2 t)
    ((measurable_stoppingSize_planar y).const_mul 12) hY hB hYm hq

/-- **The moments of the weighted number of anchor regions.** -/
theorem growthMoments_weightMajorant_zero (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ A k : ℝ, 0 < A ∧ 0 < k ∧ ∀ z : Vertex 2,
      GrowthMoments p (weightMajorant (fun _ _ => 0) 12 10 z) A k := by
  refine growthMoments_weightMajorant hpc (fun _ => measurable_const) one_pos one_pos
    (fun z q hq => ?_) (by norm_num) (by norm_num)
  have hq0 : 0 ≤ q := by linarith
  simp only [add_zero, ENNReal.ofReal_one, ENNReal.one_rpow, lintegral_const, measure_univ,
    mul_one, one_mul, Real.rpow_one]
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  exact Real.one_le_rpow hq hq0

end Rigidity.Corrector
