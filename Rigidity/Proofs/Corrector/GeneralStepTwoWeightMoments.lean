import Rigidity.Proofs.Corrector.GeneralStepTwoWeightMeas
import Rigidity.Proofs.Corrector.GeneralStepOneW
import Rigidity.Proofs.Corrector.DarioStepTwoWeightMoments
import Rigidity.Proofs.Green.GeneralFluxMoments

/-!
# The moments of the weights of the Step 2 sum on `ℤᵈ`

For nonnegative `Λ` with moments `E[(1 + Λ(z))^q] ≤ (B q^κ)^q` uniform in `z`, and constants
`K₁, K₂ > 0`, the majorant

`M(u) = Σ_a 1{|a - u| ≤ K₁ σ(a)} T(a)⁹`,   `T(v) = Σ_{|z - v| ≤ K₂ σ(v)} (1 + Λ(z))`

(`weightMajorant`), with `σ(v)` the stopping size of the good cubes of `ℤᵈ` at `v`, has moments
`E[M(u)^q] ≤ (A q^k)^q` uniform in `u` (`growthMoments_weightMajorant`), with `A, k` depending
only on `d, B, κ, K₁, K₂` (`growthMoments_weightMajorant_uniform`): as for Step 1
(`stepOneW_moments`), the ball sums `T` have such moments
(`lintegral_randomBallSum_rpow_le_of_growth`), each summand is a ball sum on the event
`|a - u| ≤ K₁ σ(a)` of probability `2 e^{-|a - u| / (K₁ θ)}` (Cauchy–Schwarz,
`lintegral_indicator_rpow_le`), and Jensen's inequality over the edges with these decaying weights
(`lintegral_tsum_rpow_le_of_decay`, with the weight bound `tsum_exp_neg_norm_edge_le` over the
edges of `ℤᵈ`) concludes.

This is the planar file `DarioStepTwoWeightMoments` on `ℤᵈ`: the stopping size of the planar
partition is replaced by that of the good cubes of `ℤᵈ`, whose exponential tail is
`partition_estimates`, the moments of polynomial growth are `GrowthMomentsD`, and the exponents
`2` of the planar ball sums and edge weights are `d`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open Rigidity.Green.GeneralFlux (GrowthMomentsD)
open scoped Classical ENNReal

variable {d : ℕ}

/-- The majorant `Σ_a 1{|a - u| ≤ K₁ σ(a)} T(a)⁹` of the weights of the Step 2 sum. -/
noncomputable def weightMajorant (Λ : Vertex d → Configuration d → ℝ) (K₁ K₂ : ℝ) (u : Vertex d)
    (ω : Configuration d) : ℝ≥0∞ :=
  ∑' a : LatticeEdge d, if ‖latticeEuclideanEmbedding (a.1 - u)‖ ≤
      K₁ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a.1 then
    stepOneBallSum Λ K₂ a.1 ω ^ (9 : ℝ) else 0

theorem measurable_weightMajorant {Λ : Vertex d → Configuration d → ℝ}
    (hΛm : ∀ z, Measurable (Λ z)) (K₁ K₂ : ℝ) (u : Vertex d) :
    Measurable (weightMajorant Λ K₁ K₂ u) :=
  Measurable.tsum fun a => Measurable.ite (measurableSet_le measurable_const
    ((measurable_stoppingSize_goodCubes a.1).const_mul K₁))
    ((measurable_stepOneBallSum hΛm K₂ a.1).pow_const _) measurable_const

/-- The edges weighted by `e^{-|a - u|/κ}`: `Σ_a e^{-|a - u|/κ} ≤ d (2d)^d (1 + κ)^d`. -/
theorem tsum_exp_neg_norm_edge_le (hd : 0 < d) (u : Vertex d) {κ : ℝ} (hκ : 0 < κ) :
    ∑' a : LatticeEdge d,
        ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (a.1 - u)‖ / κ)) ≤
      ENNReal.ofReal (d * (2 * d) ^ d * (1 + κ) ^ d) := by
  have hsum := tsum_exp_neg_norm_sub_le u hκ
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hbase : (2 * (1 + d * κ)) ^ d ≤ (2 * d) ^ d * (1 + κ) ^ d := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    nlinarith
  calc ∑' a : LatticeEdge d,
        ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (a.1 - u)‖ / κ))
      = ∑' x : Vertex d, ∑' _j : Fin d,
          ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (x - u)‖ / κ)) :=
        ENNReal.tsum_prod (f := fun x (_ : Fin d) =>
          ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (x - u)‖ / κ)))
    _ = d * ∑' x : Vertex d,
          ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (x - u)‖ / κ)) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun x => ?_
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ d * ENNReal.ofReal ((2 * (1 + d * κ)) ^ d) := by gcongr
    _ = ENNReal.ofReal (d * (2 * (1 + d * κ)) ^ d) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (d * (2 * d) ^ d * (1 + κ) ^ d) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hbase (by positivity)

/-- **The moments of the majorant of the weights**, with constants depending only on `d`, on the
growth constants `B, κ` of `1 + Λ` and on `K₁, K₂`. -/
theorem growthMoments_weightMajorant_uniform [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {B κ : ℝ} (hB : 0 < B) (hκ : 0 < κ) {K₁ K₂ : ℝ}
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    ∃ A k : ℝ, 0 < A ∧ 0 < k ∧ ∀ Λ : Vertex d → Configuration d → ℝ, (∀ z, Measurable (Λ z)) →
      (∀ z, GrowthMomentsD p (fun ω => ENNReal.ofReal (1 + Λ z ω)) B κ) →
        ∀ u, GrowthMomentsD p (weightMajorant Λ K₁ K₂ u) A k := by
  obtain ⟨θ', hθ', hexp⟩ := (partition_estimates hd hpc).2.1
  have hd0 : 0 < d := by omega
  set A₁ : ℝ := (2 * (1 + 8 * d * (K₂ * θ'))) ^ d * Real.sqrt 2 * (B * 2 ^ κ) with hA₁
  have hA₁0 : 0 < A₁ := by positivity
  set N : ℝ := d * (2 * d) ^ d with hN
  have hN1 : 1 ≤ N := by
    have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    have h2 : (1 : ℝ) ≤ (2 * d) ^ d := one_le_pow₀ (by linarith)
    rw [hN]
    nlinarith
  set X : ℝ := N * (1 + 4 * (K₁ * θ')) ^ d with hX
  have hX1 : 1 ≤ X := by
    have h0 : 0 ≤ K₁ * θ' := by positivity
    have : 1 ≤ (1 + 4 * (K₁ * θ')) ^ d := one_le_pow₀ (by linarith)
    rw [hX]
    nlinarith
  have hc1 : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.one_le_sqrt]; norm_num
  refine ⟨X * Real.sqrt 2 * (A₁ * 18 ^ (κ + d)) ^ 9, 9 * (κ + d) + d,
    mul_pos (mul_pos (by linarith) (by positivity)) (by positivity), by positivity,
    fun Λ hΛm hmom u q hq => ?_⟩
  have hq0 : 0 < q := by linarith
  set Y₀ : ℝ := (A₁ * 18 ^ (κ + d)) ^ 9 * q ^ (9 * (κ + d)) with hY₀
  have hY₀0 : 0 ≤ Y₀ := by positivity
  -- the moments of the ball sums
  have hball : ∀ v, ∫⁻ ω, stepOneBallSum Λ K₂ v ω ^ (18 * q) ∂latticeBondLaw d p ≤
      ENNReal.ofReal ((A₁ * (18 * q) ^ (κ + d)) ^ (18 * q)) := by
    intro v
    unfold stepOneBallSum
    exact lintegral_randomBallSum_rpow_le_of_growth v (θ := K₂ * θ') (by positivity)
      (fun t _ => measure_le_mul_stoppingSize_le hθ' hK₂ v (hexp v).1 (hexp v).2 t)
      ((measurable_stoppingSize_goodCubes v).const_mul K₂)
      (fun x => (measurable_const.add (hΛm x)).ennreal_ofReal) hB hmom (by linarith)
  -- the moments of each summand
  have hedge : ∀ a : LatticeEdge d, ∫⁻ ω, (if ‖latticeEuclideanEmbedding (a.1 - u)‖ ≤
      K₁ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a.1 then
        stepOneBallSum Λ K₂ a.1 ω ^ (9 : ℝ) else 0) ^ q ∂latticeBondLaw d p ≤
      ENNReal.ofReal (Real.sqrt 2 * Y₀ ^ q *
        Real.exp (-(‖latticeEuclideanEmbedding (a.1 - u)‖ / (2 * (K₁ * θ'))))) := by
    intro a
    set t := ‖latticeEuclideanEmbedding (a.1 - u)‖ with ht
    set Z : Configuration d → ℝ≥0∞ := fun ω => stepOneBallSum Λ K₂ a.1 ω ^ (9 : ℝ) with hZ
    have hZm : Measurable Z := (measurable_stepOneBallSum hΛm K₂ a.1).pow_const _
    have hind : ∀ ω, (if t ≤ K₁ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a.1 then
        stepOneBallSum Λ K₂ a.1 ω ^ (9 : ℝ) else 0) =
        {ω' | t ≤ K₁ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω') a.1}.indicator Z ω := by
      intro ω
      simp only [Set.indicator_apply, Set.mem_setOf_eq, hZ]
    have hZ2 : ∫⁻ ω, Z ω ^ (2 * q) ∂latticeBondLaw d p ≤ ENNReal.ofReal ((Y₀ ^ q) ^ 2) := by
      calc ∫⁻ ω, Z ω ^ (2 * q) ∂latticeBondLaw d p
          = ∫⁻ ω, stepOneBallSum Λ K₂ a.1 ω ^ (18 * q) ∂latticeBondLaw d p := by
            refine lintegral_congr fun ω => ?_
            simp only [hZ]
            rw [← ENNReal.rpow_mul]
            congr 1
            ring
        _ ≤ ENNReal.ofReal ((A₁ * (18 * q) ^ (κ + d)) ^ (18 * q)) := hball _
        _ = ENNReal.ofReal ((Y₀ ^ q) ^ 2) := by
            have h9 := ninefold_moment_eq (κ := κ + d - 2) hA₁0.le hq0
            rw [show κ + (d : ℝ) - 2 + 2 = κ + d by ring] at h9
            rw [hY₀, h9]
    have h3 := lintegral_indicator_rpow_le (p := p) (A := {ω' | t ≤ K₁ *
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω') a.1})
      (measurableSet_le measurable_const ((measurable_stoppingSize_goodCubes _).const_mul K₁))
      hZm hq0 (c := 2 * Real.exp (-(t / (K₁ * θ')))) (m := Y₀ ^ q) (by positivity)
      (by positivity) (measure_le_mul_stoppingSize_le hθ' hK₁ _ (hexp _).1 (hexp _).2 t) hZ2
    rw [lintegral_congr fun ω => by rw [hind ω]]
    refine h3.trans (le_of_eq ?_)
    rw [sqrt_two_mul_exp_neg, show t / (K₁ * θ') / 2 = t / (2 * (K₁ * θ')) by
      rw [div_div, mul_comm 2]]
    congr 1
    ring
  -- Jensen's inequality over the edges
  have hJ := lintegral_tsum_rpow_le_of_decay (ι := LatticeEdge d) (p := p)
    (I := fun a ω => if ‖latticeEuclideanEmbedding (a.1 - u)‖ ≤
      K₁ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a.1 then
        stepOneBallSum Λ K₂ a.1 ω ^ (9 : ℝ) else 0)
    (fun a => Measurable.ite (measurableSet_le measurable_const
      ((measurable_stoppingSize_goodCubes a.1).const_mul K₁))
      ((measurable_stepOneBallSum hΛm K₂ a.1).pow_const _) measurable_const)
    (a := fun a => ‖latticeEuclideanEmbedding (a.1 - u)‖)
    (fun a => norm_nonneg _) hq (θ := K₁ * θ') (by positivity) (M := Real.sqrt 2 * Y₀ ^ q)
    (N := N) (m := d) (by positivity) (by linarith)
    (fun κ' hκ' => tsum_exp_neg_norm_edge_le hd0 u hκ') hedge
  have hbase : N * (1 + 4 * q * (K₁ * θ')) ^ d ≤ X * q ^ d := by
    have h0 : 0 ≤ K₁ * θ' := by positivity
    have h1 : 1 + 4 * q * (K₁ * θ') ≤ q * (1 + 4 * (K₁ * θ')) := by nlinarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 d
    rw [mul_pow] at h2
    rw [hX]
    calc N * (1 + 4 * q * (K₁ * θ')) ^ d ≤ N * (q ^ d * (1 + 4 * (K₁ * θ')) ^ d) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = N * (1 + 4 * (K₁ * θ')) ^ d * q ^ d := by ring
  have hXq : 0 < X * q ^ d := mul_pos (by linarith) (by positivity)
  have hXq1 : (X * q ^ d) ^ (q - 1) * X ≤ (X * q ^ d) ^ q := by
    rw [Real.rpow_sub hXq, Real.rpow_one, div_mul_eq_mul_div, div_le_iff₀ hXq]
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by linarith)
      (one_le_pow₀ hq)) (Real.rpow_nonneg hXq.le q)
  have hcq : Real.sqrt 2 ≤ Real.sqrt 2 ^ q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hc1 hq
  refine hJ.trans (ENNReal.ofReal_le_ofReal ?_)
  calc (N * (1 + 4 * q * (K₁ * θ')) ^ d) ^ (q - 1) *
        (Real.sqrt 2 * Y₀ ^ q * (N * (1 + 4 * (K₁ * θ')) ^ d))
      ≤ (X * q ^ d) ^ (q - 1) * (X * (Real.sqrt 2 * Y₀ ^ q)) := by
        rw [show Real.sqrt 2 * Y₀ ^ q * (N * (1 + 4 * (K₁ * θ')) ^ d) =
          X * (Real.sqrt 2 * Y₀ ^ q) by rw [hX]; ring]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (by positivity) hbase (by linarith))
          (mul_nonneg (by linarith) (by positivity))
    _ = ((X * q ^ d) ^ (q - 1) * X) * (Real.sqrt 2 * Y₀ ^ q) := by ring
    _ ≤ (X * q ^ d) ^ q * (Real.sqrt 2 ^ q * Y₀ ^ q) :=
        mul_le_mul hXq1 (mul_le_mul_of_nonneg_right hcq (by positivity)) (by positivity)
          (Real.rpow_nonneg hXq.le q)
    _ = (X * Real.sqrt 2 * (A₁ * 18 ^ (κ + d)) ^ 9 * q ^ (9 * (κ + d) + d)) ^ q := by
        rw [← Real.mul_rpow (by positivity) hY₀0,
          ← Real.mul_rpow hXq.le (by positivity), hY₀, Real.rpow_add hq0, Real.rpow_natCast]
        congr 1
        ring

/-- **The moments of the majorant of the weights.** -/
theorem growthMoments_weightMajorant [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {Λ : Vertex d → Configuration d → ℝ}
    (hΛm : ∀ z, Measurable (Λ z)) {B κ : ℝ} (hB : 0 < B) (hκ : 0 < κ)
    (hmom : ∀ z, GrowthMomentsD p (fun ω => ENNReal.ofReal (1 + Λ z ω)) B κ) {K₁ K₂ : ℝ}
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    ∃ A k : ℝ, 0 < A ∧ 0 < k ∧ ∀ u, GrowthMomentsD p (weightMajorant Λ K₁ K₂ u) A k := by
  obtain ⟨A, k, hA, hk, h⟩ := growthMoments_weightMajorant_uniform hd hpc hB hκ hK₁ hK₂
  exact ⟨A, k, hA, hk, h Λ hΛm hmom⟩

end Rigidity.Corrector.GeneralDim
