import Rigidity.Proofs.Corrector.GeneralStepTwoPathBound

/-!
# The moments of the pieces of the weight of the Step 2 sum on `ℤᵈ`

* `growthMoments_sq_of_exp_moment`, `growthMoments_pow_of_exp_moment`: a nonnegative variable with
  a stretched exponential moment has a square, and powers, with moments of polynomial growth;
* `growthMoments_size_pow`: so does `(7σ(y))^d`, `σ` the stopping size of the good cubes of `ℤᵈ`,
  uniformly in `y`;
* `growthMoments_ballSum`: a sum over the ball of radius `Kσ(y)` of variables with moments of
  polynomial growth has such moments, uniformly in `y`
  (`lintegral_randomBallSum_rpow_le_of_growth`);
* `growthMoments_weightMajorant_zero`: the weighted number of anchor regions has them.

This is the planar file `DarioStepTwoFinalMoments` on `ℤᵈ`, with the moments `GrowthMomentsD`. The
bound `81σ(y)²` of the planar anchor regions becomes `(7σ(y))^d`, whose moments come from the
stretched exponential moment of exponent `1/d` of `(7σ(y))^d`
(`growthMoments_pow_of_exp_moment`), and the radius `12σ(y)` of the planar ball sums becomes a
radius `Kσ(y)` for any `K > 0`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open Rigidity.Green.GeneralFlux (GrowthMomentsD growthMomentsD_of_exp_moment)
open scoped Classical ENNReal

variable {d : ℕ} {p : unitInterval}

theorem growthMoments_sq_of_exp_moment {X : Configuration d → ℝ} (hXm : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s)
    (hint : Integrable (fun ω => Real.exp ((X ω / θ) ^ s)) (latticeBondLaw d p))
    (hb : ∫ ω, Real.exp ((X ω / θ) ^ s) ∂latticeBondLaw d p ≤ 2) :
    GrowthMomentsD p (fun ω => ENNReal.ofReal (X ω ^ 2))
      ((2 * θ * (1 / s) ^ (1 / s)) * (2 * θ * (1 / s) ^ (1 / s)) * 2 ^ (1 / s + 1 / s))
      (1 / s + 1 / s) := by
  have h1 := growthMomentsD_of_exp_moment hX0 hθ hs hint hb
  have hm : AEMeasurable (fun ω => ENNReal.ofReal (X ω)) (latticeBondLaw d p) :=
    hXm.ennreal_ofReal.aemeasurable
  have h2 := Rigidity.Green.GeneralFlux.GrowthMomentsD.mul hm hm h1 h1 (by positivity)
    (by positivity)
  refine h2.mono fun ω => le_of_eq ?_
  rw [sq, ENNReal.ofReal_mul (hX0 ω)]

/-- A nonnegative variable with a stretched exponential moment `E[exp((X/θ)^s)] ≤ 2` has powers
`X^n`, `n ≥ 1`, with moments of polynomial growth: `X^n` has the stretched exponential moment
`E[exp((X^n/θ^n)^{s/n})] ≤ 2`. -/
theorem growthMoments_pow_of_exp_moment {X : Configuration d → ℝ} (hX0 : ∀ ω, 0 ≤ X ω)
    {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s)
    (hint : Integrable (fun ω => Real.exp ((X ω / θ) ^ s)) (latticeBondLaw d p))
    (hb : ∫ ω, Real.exp ((X ω / θ) ^ s) ∂latticeBondLaw d p ≤ 2) {n : ℕ} (hn : 0 < n) :
    GrowthMomentsD p (fun ω => ENNReal.ofReal (X ω ^ n))
      (2 * θ ^ n * (n / s) ^ (n / s)) (n / s) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have e : ∀ ω, (X ω ^ n / θ ^ n) ^ (s / n) = (X ω / θ) ^ s := by
    intro ω
    rw [← div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg (hX0 ω) hθ.le)]
    congr 1
    field_simp
  have h := growthMomentsD_of_exp_moment (p := p) (X := fun ω => X ω ^ n)
    (fun ω => pow_nonneg (hX0 ω) n) (pow_pos hθ n) (div_pos hs (Nat.cast_pos.2 hn))
    (by simpa only [e] using hint) (by simpa only [e] using hb)
  rw [one_div_div] at h
  exact h

/-- **The moments of `(7σ(y))^d`**, uniformly in `y`. -/
theorem growthMoments_size_pow [NeZero d] (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ)) :
    ∃ B k : ℝ, 0 < B ∧ 0 < k ∧ ∀ y : Vertex d, GrowthMomentsD p
      (fun ω => ENNReal.ofReal ((7 * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y) ^ d))
      B k := by
  obtain ⟨θ', hθ', hexp⟩ := (partition_estimates hd hpc).2.1
  have hd0 : 0 < d := by omega
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  refine ⟨2 * (7 * θ') ^ d * ((d : ℝ) / 1) ^ ((d : ℝ) / 1), (d : ℝ) / 1,
    mul_pos (mul_pos two_pos (pow_pos (by positivity) d))
      (Real.rpow_pos_of_pos (div_pos hd0' one_pos) _), div_pos hd0' one_pos, fun y => ?_⟩
  have e : ∀ ω, (7 * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y / (7 * θ')) ^ (1 : ℝ) =
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y / θ' := by
    intro ω
    rw [Real.rpow_one, mul_div_mul_left _ _ (by norm_num : (7 : ℝ) ≠ 0)]
  exact growthMoments_pow_of_exp_moment
    (fun ω => mul_nonneg (by norm_num) (TriadicCube.stoppingSize_nonneg _ y))
    (by positivity : (0 : ℝ) < 7 * θ') one_pos (by simpa only [e] using (hexp y).1)
    (by simpa only [e] using (hexp y).2) hd0

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
