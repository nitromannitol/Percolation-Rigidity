import Rigidity.Proofs.Corrector.DarioLocalGradientMoments
import Rigidity.Proofs.Corrector.DarioStepOneHolds

/-!
# The moments of the weights of the Step 2 sum

For nonnegative `Λ` with moments `E[(1 + Λ(z))^q] ≤ (B q^κ)^q` uniform in `z`, and constants
`K₁, K₂ > 0`, the majorant

`M(u) = Σ_a 1{|a - u| ≤ K₁ σ(a)} T(a)⁹`,   `T(v) = Σ_{|z - v| ≤ K₂ σ(v)} (1 + Λ(z))`

(`weightMajorant`), with `σ(v)` the stopping size of the planar partition at `v`, has moments
`E[M(u)^q] ≤ (A q^k)^q` uniform in `u` (`growthMoments_weightMajorant`), with `A, k` depending
only on `B, κ, K₁, K₂` (`growthMoments_weightMajorant_uniform`): as for Step 1
(`stepOneW_moments`), the ball sums `T` have such moments
(`lintegral_randomBallSum_rpow_le_of_growth`),
each summand is a ball sum on the event `|a - u| ≤ K₁ σ(a)` of probability
`2 e^{-|a - u| / (K₁ θ)}` (Cauchy–Schwarz, `lintegral_indicator_rpow_le`), and Jensen's inequality
over the edges with these decaying weights (`lintegral_tsum_rpow_le_of_decay`) concludes. The
weight `W` of the Step 2 sum and its finite-range approximations are bounded by such majorants.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

/-- The majorant `Σ_a 1{|a - u| ≤ K₁ σ(a)} T(a)⁹` of the weights of the Step 2 sum. -/
noncomputable def weightMajorant (Λ : Vertex 2 → Configuration 2 → ℝ) (K₁ K₂ : ℝ) (u : Vertex 2)
    (ω : Configuration 2) : ℝ≥0∞ :=
  ∑' a : LatticeEdge, if ‖latticeEuclideanEmbedding (a.1 - u)‖ ≤
      K₁ * TriadicCube.stoppingSize (planarGoodCubes ω) a.1 then
    stepOneBallSum Λ K₂ a.1 ω ^ (9 : ℝ) else 0

theorem measurable_weightMajorant {Λ : Vertex 2 → Configuration 2 → ℝ}
    (hΛm : ∀ z, Measurable (Λ z)) (K₁ K₂ : ℝ) (u : Vertex 2) :
    Measurable (weightMajorant Λ K₁ K₂ u) :=
  Measurable.tsum fun a => Measurable.ite (measurableSet_le measurable_const
    ((measurable_stoppingSize_planar a.1).const_mul K₁))
    ((measurable_stepOneBallSum hΛm K₂ a.1).pow_const _) measurable_const

/-- The edges weighted by `e^{-|a - u|/κ}`. -/
theorem tsum_exp_neg_norm_edge_le (u : Vertex 2) {κ : ℝ} (hκ : 0 < κ) :
    ∑' a : LatticeEdge, ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (a.1 - u)‖ / κ)) ≤
      ENNReal.ofReal (32 * (1 + κ) ^ 2) := by
  have hsum := tsum_exp_neg_norm_sub_le u hκ
  calc ∑' a : LatticeEdge, ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (a.1 - u)‖ / κ))
      = ∑' x : Vertex 2, ∑' _j : Fin 2,
          ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (x - u)‖ / κ)) :=
        ENNReal.tsum_prod (f := fun x (_ : Fin 2) =>
          ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (x - u)‖ / κ)))
    _ = 2 * ∑' x : Vertex 2,
          ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (x - u)‖ / κ)) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun x => ?_
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
    _ ≤ 2 * ENNReal.ofReal (4 * (1 + 2 * κ) ^ 2) := by gcongr
    _ = ENNReal.ofReal (8 * (1 + 2 * κ) ^ 2) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring
    _ ≤ ENNReal.ofReal (32 * (1 + κ) ^ 2) := ENNReal.ofReal_le_ofReal (by nlinarith)

/-- The arithmetic of the ninefold moments of the ball sums. -/
theorem ninefold_moment_eq {A₁ κ q : ℝ} (hA : 0 ≤ A₁) (hq : 0 < q) :
    (A₁ * (18 * q) ^ (κ + 2)) ^ (18 * q) =
      (((A₁ * 18 ^ (κ + 2)) ^ 9 * q ^ (9 * (κ + 2))) ^ q) ^ 2 := by
  have h6 : (18 * q) ^ (κ + 2) = 18 ^ (κ + 2) * q ^ (κ + 2) := Real.mul_rpow (by norm_num) hq.le
  have h9 : q ^ (9 * (κ + 2)) = (q ^ (κ + 2)) ^ 9 := by
    rw [mul_comm, Real.rpow_mul hq.le, show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h6, h9, ← mul_pow, ← mul_assoc]
  obtain ⟨w, hw0, hw⟩ : ∃ w, 0 ≤ w ∧ A₁ * 18 ^ (κ + 2) * q ^ (κ + 2) = w :=
    ⟨_, by positivity, rfl⟩
  rw [hw, ← Real.rpow_natCast ((w ^ 9) ^ q) 2, ← Real.rpow_mul (by positivity),
    ← rpow_natCast_mul_eq hw0 9]
  congr 1
  push_cast
  ring

/-- **The moments of the majorant of the weights**, with constants depending only on the growth
constants `B, κ` of `1 + Λ` and on `K₁, K₂`. -/
theorem growthMoments_weightMajorant_uniform {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) {B κ : ℝ} (hB : 0 < B) (hκ : 0 < κ) {K₁ K₂ : ℝ}
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    ∃ A k : ℝ, 0 < A ∧ 0 < k ∧ ∀ Λ : Vertex 2 → Configuration 2 → ℝ, (∀ z, Measurable (Λ z)) →
      (∀ z, GrowthMoments p (fun ω => ENNReal.ofReal (1 + Λ z ω)) B κ) →
        ∀ u, GrowthMoments p (weightMajorant Λ K₁ K₂ u) A k := by
  obtain ⟨θ', hθ', hexp⟩ := (planar_meshed_partition_estimates hpc).2.1
  set A₁ : ℝ := 4 * (1 + 8 * (K₂ * θ')) ^ 2 * Real.sqrt 2 * (B * 2 ^ κ) with hA₁
  have hA₁0 : 0 < A₁ := by positivity
  set X : ℝ := 32 * (1 + 4 * (K₁ * θ')) ^ 2 with hX
  have hX1 : 1 ≤ X := by
    have h0 : 0 ≤ K₁ * θ' := by positivity
    have : 1 ≤ 1 + 4 * (K₁ * θ') := by linarith
    nlinarith
  have hc1 : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.one_le_sqrt]; norm_num
  refine ⟨X * Real.sqrt 2 * (A₁ * 18 ^ (κ + 2)) ^ 9, 9 * (κ + 2) + 2,
    mul_pos (mul_pos (by linarith) (by positivity)) (by positivity), by linarith,
    fun Λ hΛm hmom u q hq => ?_⟩
  have hq0 : 0 < q := by linarith
  set Y₀ : ℝ := (A₁ * 18 ^ (κ + 2)) ^ 9 * q ^ (9 * (κ + 2)) with hY₀
  have hY₀0 : 0 ≤ Y₀ := by positivity
  -- the moments of the ball sums
  have hball : ∀ v, ∫⁻ ω, stepOneBallSum Λ K₂ v ω ^ (18 * q) ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal ((A₁ * (18 * q) ^ (κ + 2)) ^ (18 * q)) := by
    intro v
    unfold stepOneBallSum
    exact lintegral_randomBallSum_rpow_le_of_growth v (θ := K₂ * θ') (by positivity)
      (fun t _ => measure_le_mul_stoppingSize_le hθ' hK₂ v (hexp v).1 (hexp v).2 t)
      ((measurable_stoppingSize_planar v).const_mul K₂)
      (fun x => (measurable_const.add (hΛm x)).ennreal_ofReal) hB hmom (by linarith)
  -- the moments of each summand
  have hedge : ∀ a : LatticeEdge, ∫⁻ ω, (if ‖latticeEuclideanEmbedding (a.1 - u)‖ ≤
      K₁ * TriadicCube.stoppingSize (planarGoodCubes ω) a.1 then
        stepOneBallSum Λ K₂ a.1 ω ^ (9 : ℝ) else 0) ^ q ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal (Real.sqrt 2 * Y₀ ^ q *
        Real.exp (-(‖latticeEuclideanEmbedding (a.1 - u)‖ / (2 * (K₁ * θ'))))) := by
    intro a
    set t := ‖latticeEuclideanEmbedding (a.1 - u)‖ with ht
    set Z : Configuration 2 → ℝ≥0∞ := fun ω => stepOneBallSum Λ K₂ a.1 ω ^ (9 : ℝ) with hZ
    have hZm : Measurable Z := (measurable_stepOneBallSum hΛm K₂ a.1).pow_const _
    have hind : ∀ ω, (if t ≤ K₁ * TriadicCube.stoppingSize (planarGoodCubes ω) a.1 then
        stepOneBallSum Λ K₂ a.1 ω ^ (9 : ℝ) else 0) =
        {ω' | t ≤ K₁ * TriadicCube.stoppingSize (planarGoodCubes ω') a.1}.indicator Z ω := by
      intro ω
      simp only [Set.indicator_apply, Set.mem_setOf_eq, hZ]
    have hZ2 : ∫⁻ ω, Z ω ^ (2 * q) ∂latticeBondLaw 2 p ≤ ENNReal.ofReal ((Y₀ ^ q) ^ 2) := by
      calc ∫⁻ ω, Z ω ^ (2 * q) ∂latticeBondLaw 2 p
          = ∫⁻ ω, stepOneBallSum Λ K₂ a.1 ω ^ (18 * q) ∂latticeBondLaw 2 p := by
            refine lintegral_congr fun ω => ?_
            simp only [hZ]
            rw [← ENNReal.rpow_mul]
            congr 1
            ring
        _ ≤ ENNReal.ofReal ((A₁ * (18 * q) ^ (κ + 2)) ^ (18 * q)) := hball _
        _ = ENNReal.ofReal ((Y₀ ^ q) ^ 2) := by rw [hY₀, ninefold_moment_eq hA₁0.le hq0]
    have h3 := lintegral_indicator_rpow_le (p := p) (A := {ω' | t ≤ K₁ *
        TriadicCube.stoppingSize (planarGoodCubes ω') a.1})
      (measurableSet_le measurable_const ((measurable_stoppingSize_planar _).const_mul K₁)) hZm
      hq0 (c := 2 * Real.exp (-(t / (K₁ * θ')))) (m := Y₀ ^ q) (by positivity) (by positivity)
      (measure_le_mul_stoppingSize_le hθ' hK₁ _ (hexp _).1 (hexp _).2 t) hZ2
    rw [lintegral_congr fun ω => by rw [hind ω]]
    refine h3.trans (le_of_eq ?_)
    rw [sqrt_two_mul_exp_neg, show t / (K₁ * θ') / 2 = t / (2 * (K₁ * θ')) by
      rw [div_div, mul_comm 2]]
    congr 1
    ring
  have hJ := lintegral_tsum_rpow_le_of_decay (ι := LatticeEdge) (p := p)
    (I := fun a ω => if ‖latticeEuclideanEmbedding (a.1 - u)‖ ≤
      K₁ * TriadicCube.stoppingSize (planarGoodCubes ω) a.1 then
        stepOneBallSum Λ K₂ a.1 ω ^ (9 : ℝ) else 0)
    (fun a => Measurable.ite (measurableSet_le measurable_const
      ((measurable_stoppingSize_planar a.1).const_mul K₁))
      ((measurable_stepOneBallSum hΛm K₂ a.1).pow_const _) measurable_const)
    (a := fun a => ‖latticeEuclideanEmbedding (a.1 - u)‖)
    (fun a => norm_nonneg _) hq (θ := K₁ * θ') (by positivity) (M := Real.sqrt 2 * Y₀ ^ q)
    (N := 32) (by positivity) (by norm_num) (fun κ' hκ' => tsum_exp_neg_norm_edge_le u hκ')
    hedge
  have hbase : 32 * (1 + 4 * q * (K₁ * θ')) ^ 2 ≤ X * q ^ 2 := by
    have h1 := one_add_mul_le_mul (b := 4) (θ := K₁ * θ') hq
    have h0 : 0 ≤ 1 + 4 * q * (K₁ * θ') := by positivity
    have := pow_le_pow_left₀ h0 h1 2
    rw [hX]
    nlinarith
  refine hJ.trans (ENNReal.ofReal_le_ofReal ?_)
  calc (32 * (1 + 4 * q * (K₁ * θ')) ^ 2) ^ (q - 1) *
        (Real.sqrt 2 * Y₀ ^ q * (32 * (1 + 4 * (K₁ * θ')) ^ 2))
      ≤ (X * q ^ 2) ^ (q - 1) * (X * (Real.sqrt 2 * Y₀ ^ q)) := by
        rw [show Real.sqrt 2 * Y₀ ^ q * (32 * (1 + 4 * (K₁ * θ')) ^ 2) =
          X * (Real.sqrt 2 * Y₀ ^ q) by rw [hX]; ring]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (by positivity) hbase (by linarith)) (by positivity)
    _ ≤ (X * Real.sqrt 2 * Y₀ * q ^ 2) ^ q := rpow_sub_one_mul_le hX1 hc1 hY₀0 hq
    _ = (X * Real.sqrt 2 * (A₁ * 18 ^ (κ + 2)) ^ 9 * q ^ (9 * (κ + 2) + 2)) ^ q := by
        rw [hY₀, Real.rpow_add hq0, Real.rpow_two]
        congr 1
        ring

/-- **The moments of the majorant of the weights.** -/
theorem growthMoments_weightMajorant {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    {Λ : Vertex 2 → Configuration 2 → ℝ} (hΛm : ∀ z, Measurable (Λ z)) {B κ : ℝ} (hB : 0 < B)
    (hκ : 0 < κ) (hmom : ∀ z, GrowthMoments p (fun ω => ENNReal.ofReal (1 + Λ z ω)) B κ) {K₁ K₂ : ℝ}
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    ∃ A k : ℝ, 0 < A ∧ 0 < k ∧ ∀ u, GrowthMoments p (weightMajorant Λ K₁ K₂ u) A k := by
  obtain ⟨A, k, hA, hk, h⟩ := growthMoments_weightMajorant_uniform hpc hB hκ hK₁ hK₂
  exact ⟨A, k, hA, hk, h Λ hΛm hmom⟩

end Rigidity.Corrector
