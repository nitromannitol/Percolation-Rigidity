import Rigidity.Proofs.Corrector.GeneralStepTwoWeightMeas
import Rigidity.Proofs.Corrector.GeneralStepOneW
import Rigidity.Proofs.Corrector.DarioStepTwoWeightMoments
import Rigidity.Proofs.Green.GeneralFluxMoments

/-!
# The moments of the weights of the Step 2 sum on `ℤᵈ`

For nonnegative `Λ` with moments `E[(1 + Λ(z))^q] ≤ (B q^κ)^q` uniform in `z`, constants
`K₁, K₂ > 0` and radii `ρ(a)` of the edges with the uniform tail `P[ρ(a) ≥ t] ≤ 2 e^{-t/θ}`, the
majorant

`M(u) = Σ_a 1{|a - u| ≤ K₁ ρ(a)} T(a)⁹`,   `T(a) = Σ_{|z - a| ≤ K₂ ρ(a)} (1 + Λ(z))`

(`weightMajorantOf`) has moments `E[M(u)^q] ≤ (A q^k)^q` uniform in `u`, with `A, k` depending only
on `d, θ, B, κ, K₁, K₂` (`growthMoments_weightMajorantOf_uniform`): as for Step 1
(`stepOneW_moments`), the ball sums `T` have such moments
(`lintegral_randomBallSum_rpow_le_of_growth`), each summand is a ball sum on the event
`|a - u| ≤ K₁ ρ(a)` of probability `2 e^{-|a - u| / (K₁ θ)}` (Cauchy–Schwarz,
`lintegral_indicator_rpow_le`), and Jensen's inequality over the edges with these decaying weights
(`lintegral_tsum_rpow_le_of_decay`, with the weight bound `tsum_exp_neg_norm_edge_le` over the
edges of `ℤᵈ`) concludes.

Two radii are used. With `ρ(a) = σ(a)`, the stopping size of the good cubes of `ℤᵈ` at the tail of
`a`, whose exponential tail is `partition_estimates`, the majorant is `weightMajorant`
(`growthMoments_weightMajorant`). With `ρ(a) = max(σ(a), σ♭(a))` (`edgeRadius`), where `σ♭(a)` is
the stopping size at the tail of `a` of the configuration with a bond `β(a)` closed (`flipSize`),
the tail of `σ♭` is at most `1/(1 - p)` times that of `σ`, since closing a bond changes the law by
the density at most `1/(1 - p)` (`ofReal_bondWeight_mul_lintegral_setBond_le`); the constant
`1 + 1/(1 - p)` of the tail of `ρ` is absorbed into a larger `θ` (`le_two_mul_exp_of_le`), and the
majorant on these radii has moments of polynomial growth for `p < 1`
(`growthMoments_weightMajorant_edgeRadius_uniform`).

This is the planar file `DarioStepTwoWeightMoments` on `ℤᵈ`: the stopping size of the planar
partition is replaced by that of the good cubes of `ℤᵈ`, the moments of polynomial growth are
`GrowthMomentsD`, and the exponents `2` of the planar ball sums and edge weights are `d`; the
majorant over a family of edge radii and the radii with one bond closed are added.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open Rigidity.Green.GeneralFlux (GrowthMomentsD)
open scoped Classical ENNReal

variable {d : ℕ}

/-! ### The majorant over a family of edge radii -/

/-- The ball sum `Σ_{|z - v| ≤ r} (1 + Λ(z))` of a random radius `r`. -/
noncomputable def radiusBallSum (Λ : Vertex d → Configuration d → ℝ) (r : Configuration d → ℝ)
    (v : Vertex d) (ω : Configuration d) : ℝ≥0∞ :=
  ∑' z, if ‖latticeEuclideanEmbedding (z - v)‖ ≤ r ω then ENNReal.ofReal (1 + Λ z ω) else 0

theorem measurable_radiusBallSum {Λ : Vertex d → Configuration d → ℝ}
    (hΛm : ∀ z, Measurable (Λ z)) {r : Configuration d → ℝ} (hr : Measurable r) (v : Vertex d) :
    Measurable (radiusBallSum Λ r v) :=
  Measurable.tsum fun z => Measurable.ite (measurableSet_le measurable_const hr)
    ((measurable_const.add (hΛm z)).ennreal_ofReal) measurable_const

/-- The majorant `Σ_a 1{|a - u| ≤ K₁ ρ(a)} T(a)⁹`, `T(a)` the ball sum of radius `K₂ ρ(a)` around
the tail of `a`, for a family `ρ` of edge radii. -/
noncomputable def weightMajorantOf (ρ : LatticeEdge d → Configuration d → ℝ)
    (Λ : Vertex d → Configuration d → ℝ) (K₁ K₂ : ℝ) (u : Vertex d) (ω : Configuration d) :
    ℝ≥0∞ :=
  ∑' a : LatticeEdge d, if ‖latticeEuclideanEmbedding (a.1 - u)‖ ≤ K₁ * ρ a ω then
    radiusBallSum Λ (fun ω => K₂ * ρ a ω) a.1 ω ^ (9 : ℝ) else 0

theorem measurable_weightMajorantOf {ρ : LatticeEdge d → Configuration d → ℝ}
    (hρm : ∀ a, Measurable (ρ a)) {Λ : Vertex d → Configuration d → ℝ}
    (hΛm : ∀ z, Measurable (Λ z)) (K₁ K₂ : ℝ) (u : Vertex d) :
    Measurable (weightMajorantOf ρ Λ K₁ K₂ u) :=
  Measurable.tsum fun a => Measurable.ite (measurableSet_le measurable_const
    ((hρm a).const_mul K₁))
    ((measurable_radiusBallSum hΛm ((hρm a).const_mul K₂) a.1).pow_const _) measurable_const

/-- The tail `2 e^{-t/θ}` of `X` gives the tail `2 e^{-t/(Kθ)}` of `K X`. -/
theorem measure_le_mul_le_of_tail {p : unitInterval} {X : Configuration d → ℝ} {θ K : ℝ}
    (hK : 0 < K)
    (htail : ∀ t : ℝ, 0 ≤ t →
      latticeBondLaw d p {ω | t ≤ X ω} ≤ ENNReal.ofReal (2 * Real.exp (-(t / θ))))
    (t : ℝ) (ht : 0 ≤ t) :
    latticeBondLaw d p {ω | t ≤ K * X ω} ≤ ENNReal.ofReal (2 * Real.exp (-(t / (K * θ)))) := by
  have hset : {ω | t ≤ K * X ω} = {ω | t / K ≤ X ω} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => by rw [div_le_iff₀ hK]; linarith,
      fun h => by rw [div_le_iff₀ hK] at h; linarith⟩
  rw [hset]
  refine (htail (t / K) (div_nonneg ht hK.le)).trans (le_of_eq ?_)
  rw [div_div]

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

/-- **The moments of the majorant over a family of edge radii**: for radii with the uniform tail
`2 e^{-t/θ}`, with constants depending only on `d, θ`, on the growth constants `B, κ` of `1 + Λ`
and on `K₁, K₂`. -/
theorem growthMoments_weightMajorantOf_uniform (hd : 0 < d) {p : unitInterval} {θ : ℝ}
    (hθ : 0 < θ) {B κ : ℝ} (hB : 0 < B) (hκ : 0 < κ) {K₁ K₂ : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    ∃ A k : ℝ, 0 < A ∧ 0 < k ∧ ∀ ρ : LatticeEdge d → Configuration d → ℝ,
      (∀ a, Measurable (ρ a)) →
      (∀ a (t : ℝ), 0 ≤ t →
        latticeBondLaw d p {ω | t ≤ ρ a ω} ≤ ENNReal.ofReal (2 * Real.exp (-(t / θ)))) →
      ∀ Λ : Vertex d → Configuration d → ℝ, (∀ z, Measurable (Λ z)) →
      (∀ z, GrowthMomentsD p (fun ω => ENNReal.ofReal (1 + Λ z ω)) B κ) →
        ∀ u, GrowthMomentsD p (weightMajorantOf ρ Λ K₁ K₂ u) A k := by
  set A₁ : ℝ := (2 * (1 + 8 * d * (K₂ * θ))) ^ d * Real.sqrt 2 * (B * 2 ^ κ) with hA₁
  have hA₁0 : 0 < A₁ := by positivity
  set N : ℝ := d * (2 * d) ^ d with hN
  have hN1 : 1 ≤ N := by
    have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have h2 : (1 : ℝ) ≤ (2 * d) ^ d := one_le_pow₀ (by linarith)
    rw [hN]
    nlinarith
  set X : ℝ := N * (1 + 4 * (K₁ * θ)) ^ d with hX
  have hX1 : 1 ≤ X := by
    have h0 : 0 ≤ K₁ * θ := by positivity
    have : 1 ≤ (1 + 4 * (K₁ * θ)) ^ d := one_le_pow₀ (by linarith)
    rw [hX]
    nlinarith
  have hc1 : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.one_le_sqrt]; norm_num
  refine ⟨X * Real.sqrt 2 * (A₁ * 18 ^ (κ + d)) ^ 9, 9 * (κ + d) + d,
    mul_pos (mul_pos (by linarith) (by positivity)) (by positivity), by positivity,
    fun ρ hρm htail Λ hΛm hmom u q hq => ?_⟩
  have hq0 : 0 < q := by linarith
  set Y₀ : ℝ := (A₁ * 18 ^ (κ + d)) ^ 9 * q ^ (9 * (κ + d)) with hY₀
  have hY₀0 : 0 ≤ Y₀ := by positivity
  -- the moments of the ball sums
  have hball : ∀ a : LatticeEdge d,
      ∫⁻ ω, radiusBallSum Λ (fun ω => K₂ * ρ a ω) a.1 ω ^ (18 * q) ∂latticeBondLaw d p ≤
        ENNReal.ofReal ((A₁ * (18 * q) ^ (κ + d)) ^ (18 * q)) := by
    intro a
    unfold radiusBallSum
    exact lintegral_randomBallSum_rpow_le_of_growth a.1 (θ := K₂ * θ) (by positivity)
      (fun t ht => measure_le_mul_le_of_tail hK₂ (htail a) t ht) ((hρm a).const_mul K₂)
      (fun x => (measurable_const.add (hΛm x)).ennreal_ofReal) hB hmom (by linarith)
  -- the moments of each summand
  have hedge : ∀ a : LatticeEdge d, ∫⁻ ω, (if ‖latticeEuclideanEmbedding (a.1 - u)‖ ≤
      K₁ * ρ a ω then radiusBallSum Λ (fun ω => K₂ * ρ a ω) a.1 ω ^ (9 : ℝ) else 0) ^ q
        ∂latticeBondLaw d p ≤
      ENNReal.ofReal (Real.sqrt 2 * Y₀ ^ q *
        Real.exp (-(‖latticeEuclideanEmbedding (a.1 - u)‖ / (2 * (K₁ * θ))))) := by
    intro a
    set t := ‖latticeEuclideanEmbedding (a.1 - u)‖ with ht
    set Z : Configuration d → ℝ≥0∞ := fun ω =>
      radiusBallSum Λ (fun ω => K₂ * ρ a ω) a.1 ω ^ (9 : ℝ) with hZ
    have hZm : Measurable Z :=
      (measurable_radiusBallSum hΛm ((hρm a).const_mul K₂) a.1).pow_const _
    have hind : ∀ ω, (if t ≤ K₁ * ρ a ω then
        radiusBallSum Λ (fun ω => K₂ * ρ a ω) a.1 ω ^ (9 : ℝ) else 0) =
        {ω' | t ≤ K₁ * ρ a ω'}.indicator Z ω := by
      intro ω
      simp only [Set.indicator_apply, Set.mem_setOf_eq, hZ]
    have hZ2 : ∫⁻ ω, Z ω ^ (2 * q) ∂latticeBondLaw d p ≤ ENNReal.ofReal ((Y₀ ^ q) ^ 2) := by
      calc ∫⁻ ω, Z ω ^ (2 * q) ∂latticeBondLaw d p
          = ∫⁻ ω, radiusBallSum Λ (fun ω => K₂ * ρ a ω) a.1 ω ^ (18 * q)
              ∂latticeBondLaw d p := by
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
    have h3 := lintegral_indicator_rpow_le (p := p) (A := {ω' | t ≤ K₁ * ρ a ω'})
      (measurableSet_le measurable_const ((hρm a).const_mul K₁))
      hZm hq0 (c := 2 * Real.exp (-(t / (K₁ * θ)))) (m := Y₀ ^ q) (by positivity)
      (by positivity) (measure_le_mul_le_of_tail hK₁ (htail a) t (norm_nonneg _)) hZ2
    rw [lintegral_congr fun ω => by rw [hind ω]]
    refine h3.trans (le_of_eq ?_)
    rw [sqrt_two_mul_exp_neg, show t / (K₁ * θ) / 2 = t / (2 * (K₁ * θ)) by
      rw [div_div, mul_comm 2]]
    congr 1
    ring
  -- Jensen's inequality over the edges
  have hJ := lintegral_tsum_rpow_le_of_decay (ι := LatticeEdge d) (p := p)
    (I := fun a ω => if ‖latticeEuclideanEmbedding (a.1 - u)‖ ≤ K₁ * ρ a ω then
      radiusBallSum Λ (fun ω => K₂ * ρ a ω) a.1 ω ^ (9 : ℝ) else 0)
    (fun a => Measurable.ite (measurableSet_le measurable_const ((hρm a).const_mul K₁))
      ((measurable_radiusBallSum hΛm ((hρm a).const_mul K₂) a.1).pow_const _) measurable_const)
    (a := fun a => ‖latticeEuclideanEmbedding (a.1 - u)‖)
    (fun a => norm_nonneg _) hq (θ := K₁ * θ) (by positivity) (M := Real.sqrt 2 * Y₀ ^ q)
    (N := N) (m := d) (by positivity) (by linarith)
    (fun κ' hκ' => tsum_exp_neg_norm_edge_le hd u hκ') hedge
  have hbase : N * (1 + 4 * q * (K₁ * θ)) ^ d ≤ X * q ^ d := by
    have h0 : 0 ≤ K₁ * θ := by positivity
    have h1 : 1 + 4 * q * (K₁ * θ) ≤ q * (1 + 4 * (K₁ * θ)) := by nlinarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 d
    rw [mul_pow] at h2
    rw [hX]
    calc N * (1 + 4 * q * (K₁ * θ)) ^ d ≤ N * (q ^ d * (1 + 4 * (K₁ * θ)) ^ d) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = N * (1 + 4 * (K₁ * θ)) ^ d * q ^ d := by ring
  have hXq : 0 < X * q ^ d := mul_pos (by linarith) (by positivity)
  have hXq1 : (X * q ^ d) ^ (q - 1) * X ≤ (X * q ^ d) ^ q := by
    rw [Real.rpow_sub hXq, Real.rpow_one, div_mul_eq_mul_div, div_le_iff₀ hXq]
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by linarith)
      (one_le_pow₀ hq)) (Real.rpow_nonneg hXq.le q)
  have hcq : Real.sqrt 2 ≤ Real.sqrt 2 ^ q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hc1 hq
  refine hJ.trans (ENNReal.ofReal_le_ofReal ?_)
  calc (N * (1 + 4 * q * (K₁ * θ)) ^ d) ^ (q - 1) *
        (Real.sqrt 2 * Y₀ ^ q * (N * (1 + 4 * (K₁ * θ)) ^ d))
      ≤ (X * q ^ d) ^ (q - 1) * (X * (Real.sqrt 2 * Y₀ ^ q)) := by
        rw [show Real.sqrt 2 * Y₀ ^ q * (N * (1 + 4 * (K₁ * θ)) ^ d) =
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

/-! ### The majorant on the stopping sizes of the good cubes -/

/-- The sum `Σ_{|z - v| ≤ K σ(v)} (1 + Λ(z))` of `1 + Λ` over the ball of radius `K σ(v)` around
`v`. -/
noncomputable def sizeBallSum (Λ : Vertex d → Configuration d → ℝ) (K : ℝ) (v : Vertex d)
    (ω : Configuration d) : ℝ≥0∞ :=
  ∑' z, if ‖latticeEuclideanEmbedding (z - v)‖ ≤
      K * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v
    then ENNReal.ofReal (1 + Λ z ω) else 0

theorem measurable_sizeBallSum {Λ : Vertex d → Configuration d → ℝ}
    (hΛm : ∀ z, Measurable (Λ z)) (K : ℝ) (v : Vertex d) : Measurable (sizeBallSum Λ K v) :=
  Measurable.tsum fun z => Measurable.ite (measurableSet_le measurable_const
    ((measurable_stoppingSize_goodCubes v).const_mul K))
    ((measurable_const.add (hΛm z)).ennreal_ofReal) measurable_const

/-- The majorant `Σ_a 1{|a - u| ≤ K₁ σ(a)} T(a)⁹` of the weights of the Step 2 sum. -/
noncomputable def weightMajorant (Λ : Vertex d → Configuration d → ℝ) (K₁ K₂ : ℝ) (u : Vertex d)
    (ω : Configuration d) : ℝ≥0∞ :=
  ∑' a : LatticeEdge d, if ‖latticeEuclideanEmbedding (a.1 - u)‖ ≤
      K₁ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a.1 then
    sizeBallSum Λ K₂ a.1 ω ^ (9 : ℝ) else 0

theorem measurable_weightMajorant {Λ : Vertex d → Configuration d → ℝ}
    (hΛm : ∀ z, Measurable (Λ z)) (K₁ K₂ : ℝ) (u : Vertex d) :
    Measurable (weightMajorant Λ K₁ K₂ u) :=
  Measurable.tsum fun a => Measurable.ite (measurableSet_le measurable_const
    ((measurable_stoppingSize_goodCubes a.1).const_mul K₁))
    ((measurable_sizeBallSum hΛm K₂ a.1).pow_const _) measurable_const

/-- **The moments of the majorant of the weights**, with constants depending only on `d`, on the
growth constants `B, κ` of `1 + Λ` and on `K₁, K₂`. -/
theorem growthMoments_weightMajorant_uniform [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {B κ : ℝ} (hB : 0 < B) (hκ : 0 < κ) {K₁ K₂ : ℝ}
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    ∃ A k : ℝ, 0 < A ∧ 0 < k ∧ ∀ Λ : Vertex d → Configuration d → ℝ, (∀ z, Measurable (Λ z)) →
      (∀ z, GrowthMomentsD p (fun ω => ENNReal.ofReal (1 + Λ z ω)) B κ) →
        ∀ u, GrowthMomentsD p (weightMajorant Λ K₁ K₂ u) A k := by
  obtain ⟨θ', hθ', hexp⟩ := (partition_estimates hd hpc).2.1
  obtain ⟨A, k, hA, hk, h⟩ :=
    growthMoments_weightMajorantOf_uniform (d := d) (p := p) (by omega) hθ' hB hκ hK₁ hK₂
  refine ⟨A, k, hA, hk, fun Λ hΛm hmom u => ?_⟩
  exact h (fun a ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a.1)
    (fun a => measurable_stoppingSize_goodCubes a.1)
    (fun a t _ => by
      simpa only [one_mul] using
        measure_le_mul_stoppingSize_le hθ' one_pos a.1 (hexp a.1).1 (hexp a.1).2 t)
    Λ hΛm hmom u

/-- **The moments of the majorant of the weights.** -/
theorem growthMoments_weightMajorant [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {Λ : Vertex d → Configuration d → ℝ}
    (hΛm : ∀ z, Measurable (Λ z)) {B κ : ℝ} (hB : 0 < B) (hκ : 0 < κ)
    (hmom : ∀ z, GrowthMomentsD p (fun ω => ENNReal.ofReal (1 + Λ z ω)) B κ) {K₁ K₂ : ℝ}
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    ∃ A k : ℝ, 0 < A ∧ 0 < k ∧ ∀ u, GrowthMomentsD p (weightMajorant Λ K₁ K₂ u) A k := by
  obtain ⟨A, k, hA, hk, h⟩ := growthMoments_weightMajorant_uniform hd hpc hB hκ hK₁ hK₂
  exact ⟨A, k, hA, hk, h Λ hΛm hmom⟩

/-! ### The radii of the edges with one bond closed -/

/-- The stopping size `σ♭(e, v)` of the good cubes at `v` of the configuration with the bond `e`
closed. -/
noncomputable def flipSize (e : Bond d) (v : Vertex d) (ω : Configuration d) : ℝ :=
  TriadicCube.stoppingSize (TriadicCube.goodCubes (setBond e false ω)) v

theorem measurable_flipSize (e : Bond d) (v : Vertex d) : Measurable (flipSize e v) :=
  (measurable_stoppingSize_goodCubes v).comp (measurable_setBond e false)

/-- The radius `ρ(a) = max(σ(a), σ♭(β(a), a))` of the edge `a`, for a choice `β` of a bond for
every edge, `σ` and `σ♭` at the tail of `a`. -/
noncomputable def edgeRadius (β : LatticeEdge d → Bond d) (a : LatticeEdge d)
    (ω : Configuration d) : ℝ :=
  max (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a.1) (flipSize (β a) a.1 ω)

theorem measurable_edgeRadius (β : LatticeEdge d → Bond d) (a : LatticeEdge d) :
    Measurable (edgeRadius β a) :=
  (measurable_stoppingSize_goodCubes a.1).max (measurable_flipSize (β a) a.1)

/-- **Absorbing a constant into the tail**: a probability at most `2c e^{-t/θ}`, `c ≥ 1`, is at
most `2 e^{-t/(4cθ)}`. -/
theorem le_two_mul_exp_of_le {P : ℝ≥0∞} {c θ t : ℝ} (hc : 1 ≤ c) (hθ : 0 < θ) (ht : 0 ≤ t)
    (hP1 : P ≤ 1) (hP : P ≤ ENNReal.ofReal (2 * c * Real.exp (-(t / θ)))) :
    P ≤ ENNReal.ofReal (2 * Real.exp (-(t / (4 * c * θ)))) := by
  have hc0 : 0 < c := by linarith
  set u := t / θ with hu
  have hu0 : 0 ≤ u := div_nonneg ht hθ.le
  have e : t / (4 * c * θ) = u / (4 * c) := by rw [hu, div_div]; ring
  rw [e]
  have h4 : u / (4 * c) ≤ u / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  by_cases h : 2 * Real.log c ≤ u
  · refine hP.trans (ENNReal.ofReal_le_ofReal ?_)
    have e1 : c * Real.exp (-u) = Real.exp (Real.log c - u) := by
      rw [Real.exp_neg, Real.exp_sub, Real.exp_log hc0, div_eq_mul_inv]
    have h1 : c * Real.exp (-u) ≤ Real.exp (-(u / (4 * c))) := by
      rw [e1]
      exact Real.exp_le_exp.2 (by linarith)
    linarith
  · have hlog := Real.log_le_sub_one_of_pos hc0
    have hx : u / (4 * c) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hexp := Real.add_one_le_exp (-(u / (4 * c)))
    refine hP1.trans ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **The tail of the size with one bond closed**: closing the bond `e` changes the law by a density
at most `1/(1 - p)`, so `P[σ♭(e, v) ≥ t] ≤ (1 - p)⁻¹ 2 e^{-t/θ}`. -/
theorem measure_le_flipSize_le [NeZero d] {p : unitInterval} (hp1 : (p : ℝ) < 1) {θ : ℝ}
    (hθ : 0 < θ) (e : Bond d) (v : Vertex d)
    (hint : Integrable
      (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ))
      (latticeBondLaw d p))
    (hb : ∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ)
      ∂latticeBondLaw d p ≤ 2) (t : ℝ) :
    latticeBondLaw d p {ω | t ≤ flipSize e v ω} ≤
      ENNReal.ofReal ((1 - (p : ℝ))⁻¹ * (2 * Real.exp (-(t / θ)))) := by
  have hq : 0 < 1 - (p : ℝ) := by linarith
  have hA : MeasurableSet {ω : Configuration d |
      t ≤ TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v} :=
    measurableSet_le measurable_const (measurable_stoppingSize_goodCubes v)
  have hσ : latticeBondLaw d p {ω | t ≤ TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v} ≤
      ENNReal.ofReal (2 * Real.exp (-(t / θ))) := by
    simpa only [one_mul] using measure_le_mul_stoppingSize_le hθ one_pos v hint hb t
  have hflip := ofReal_bondWeight_mul_lintegral_setBond_le p
    (f := {ω : Configuration d | t ≤ TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v}.indicator
      1) (measurable_one.indicator hA) e false
  have hbw : Rigidity.Corrector.bondWeight p false = 1 - p := by
    simp [Rigidity.Corrector.bondWeight]
  have e1 : ∀ ω, {ω' : Configuration d |
      t ≤ TriadicCube.stoppingSize (TriadicCube.goodCubes ω') v}.indicator
        (1 : Configuration d → ℝ≥0∞) (setBond e false ω) =
      {ω' | t ≤ flipSize e v ω'}.indicator 1 ω := fun _ => rfl
  rw [hbw, lintegral_congr e1,
    lintegral_indicator_one (measurableSet_le measurable_const (measurable_flipSize e v)),
    lintegral_indicator_one hA] at hflip
  calc latticeBondLaw d p {ω | t ≤ flipSize e v ω}
      = ENNReal.ofReal (1 - (p : ℝ))⁻¹ *
          (ENNReal.ofReal (1 - (p : ℝ)) * latticeBondLaw d p {ω | t ≤ flipSize e v ω}) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hq.le), inv_mul_cancel₀ hq.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (1 - (p : ℝ))⁻¹ * ENNReal.ofReal (2 * Real.exp (-(t / θ))) :=
        mul_le_mul' le_rfl (hflip.trans hσ)
    _ = ENNReal.ofReal ((1 - (p : ℝ))⁻¹ * (2 * Real.exp (-(t / θ)))) :=
        (ENNReal.ofReal_mul (inv_nonneg.2 hq.le)).symm

/-- **The tail of the radius of an edge**: `P[ρ(a) ≥ t] ≤ 2 e^{-t/θ'}` with
`θ' = 4 (1 + (1 - p)⁻¹) θ`, `θ` the exponential scale of the stopping sizes. -/
theorem measure_le_edgeRadius_le [NeZero d] {p : unitInterval} (hp1 : (p : ℝ) < 1) {θ : ℝ}
    (hθ : 0 < θ)
    (hexp : ∀ v : Vertex d,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ))
        (latticeBondLaw d p) ∧
      ∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v / θ)
        ∂latticeBondLaw d p ≤ 2)
    (β : LatticeEdge d → Bond d) (a : LatticeEdge d) (t : ℝ) (ht : 0 ≤ t) :
    latticeBondLaw d p {ω | t ≤ edgeRadius β a ω} ≤
      ENNReal.ofReal (2 * Real.exp (-(t / (4 * (1 + (1 - (p : ℝ))⁻¹) * θ)))) := by
  have hq : 0 < 1 - (p : ℝ) := by linarith
  have hc : 1 ≤ 1 + (1 - (p : ℝ))⁻¹ := by
    have : 0 ≤ (1 - (p : ℝ))⁻¹ := inv_nonneg.2 hq.le
    linarith
  have hσ : latticeBondLaw d p {ω | t ≤ TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a.1} ≤
      ENNReal.ofReal (2 * Real.exp (-(t / θ))) := by
    simpa only [one_mul] using
      measure_le_mul_stoppingSize_le hθ one_pos a.1 (hexp a.1).1 (hexp a.1).2 t
  have hset : {ω | t ≤ edgeRadius β a ω} =
      {ω | t ≤ TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a.1} ∪
        {ω | t ≤ flipSize (β a) a.1 ω} := by
    ext ω
    simp only [edgeRadius, Set.mem_setOf_eq, Set.mem_union, le_max_iff]
  refine le_two_mul_exp_of_le hc hθ ht prob_le_one ?_
  rw [hset]
  refine (measure_union_le _ _).trans ((add_le_add hσ
    (measure_le_flipSize_le hp1 hθ (β a) a.1 (hexp a.1).1 (hexp a.1).2 t)).trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- **The moments of the majorant on the radii with one bond closed**, for `p < 1`, uniformly in the
choice `β` of the bonds. -/
theorem growthMoments_weightMajorant_edgeRadius_uniform [NeZero d] (hd : 2 ≤ d)
    {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) {B κ : ℝ}
    (hB : 0 < B) (hκ : 0 < κ) {K₁ K₂ : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    ∃ A k : ℝ, 0 < A ∧ 0 < k ∧ ∀ (β : LatticeEdge d → Bond d)
      (Λ : Vertex d → Configuration d → ℝ), (∀ z, Measurable (Λ z)) →
      (∀ z, GrowthMomentsD p (fun ω => ENNReal.ofReal (1 + Λ z ω)) B κ) →
        ∀ u, GrowthMomentsD p (weightMajorantOf (edgeRadius β) Λ K₁ K₂ u) A k := by
  obtain ⟨θ', hθ', hexp⟩ := (partition_estimates hd hpc).2.1
  have hq : 0 < 1 - (p : ℝ) := by linarith
  obtain ⟨A, k, hA, hk, h⟩ := growthMoments_weightMajorantOf_uniform (d := d) (p := p)
    (by omega) (θ := 4 * (1 + (1 - (p : ℝ))⁻¹) * θ') (by positivity) hB hκ hK₁ hK₂
  exact ⟨A, k, hA, hk, fun β Λ hΛm hmom u => h (edgeRadius β) (measurable_edgeRadius β)
    (fun a t ht => measure_le_edgeRadius_le hp1 hθ' hexp β a t ht) Λ hΛm hmom u⟩

end Rigidity.Corrector.GeneralDim
