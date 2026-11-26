import Rigidity.Proofs.Corrector.GeneralStepOneW
import Rigidity.Proofs.Corrector.GeneralVarianceSums
import Rigidity.Proofs.Corrector.DarioStepOneHolds

/-!
# Step 1 of Lemma 3.3 of Dario on `ℤᵈ` from Lemma 3.5

`stepOneW_moments`: the sums (3.18) `W(y) = Σ_e 1{y ∈ B_e} F_e` satisfy `E[W(y)^q] ≤ (A q^k)^q`
for all `y` and `q ≥ 1`, for the Lipschitz bounds `Λ` of `stepOne_lipschitz_data`. For each bond,
the factor of `W` at `ω` is the factor computed in `ω^{e,1}` (`stepOneFactor_eq_self`), whose
moments are at most `p^{-1}` times those of the factor computed in `ω` ((3.12) in the form
`ofReal_bondWeight_mul_lintegral_setBond_le`); the latter is at most `1{|a_e - y| ≤ κ₁ s} 16 d² T³`
(`stepOneFactorSelf_le`), whose moments decay exponentially in `|a_e - y|` (Cauchy–Schwarz, the
tail of the partition size and the moments of the ball sum `T`). Jensen's inequality over the
bonds (`lintegral_tsum_rpow_le_of_decay`) then bounds the moments of `W(y)`.

`flipSumOne_isOsBond_of_resample`: given Lemma 3.5 for the partition into good cubes of `ℤᵈ`
(`ResamplePartitionBound C₀ C`), the Step 1 sum `Σ_e T₁(e)²` is almost surely finite and
`O_s(C' r^{-d})`. With Lemma 3.5 the change of partition of each bond is supported in a box, so
the heat series of `T₁(e)` converges (`flipTermOneSummable_of_resample`), and
`darioStepOneSumBoundThree_of_resample` gives the bound of the Step 1 sum
`DarioStepOneSumBoundThree` from Lemma 3.5 in dimension `d ≥ 3` (`DarioResamplePartitionThree`).
Consequently Lemma 3.3 in dimension `d ≥ 3` follows from Lemma 3.5 and the bound of the Step 2 sum
(`darioVarianceBoundThree_of_resample`). This is the planar argument of `DarioStepOneHolds` on `ℤᵈ`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare.GeneralDim
open scoped Classical ENNReal

variable {d : ℕ} [NeZero d]

/-- The arithmetic of the sixfold moments of the ball sums. -/
theorem sixfold_moment_eq_const {K A m q : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hq : 0 < q) :
    K ^ (2 * q) * (A * (6 * q) ^ m) ^ (6 * q) =
      ((K * (A * 6 ^ m) ^ 3 * q ^ (3 * m)) ^ q) ^ 2 := by
  have h6 : (6 * q) ^ m = 6 ^ m * q ^ m := Real.mul_rpow (by norm_num) hq.le
  have h3 : q ^ (3 * m) = (q ^ m) ^ 3 := by
    rw [mul_comm, Real.rpow_mul hq.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e1 : A * (6 ^ m * q ^ m) = A * 6 ^ m * q ^ m := by ring
  have e2 : K * (A * 6 ^ m) ^ 3 * (q ^ m) ^ 3 = K * (A * 6 ^ m * q ^ m) ^ 3 := by ring
  rw [h6, h3, e1, e2]
  obtain ⟨w, hw0, hw⟩ : ∃ w, 0 ≤ w ∧ A * 6 ^ m * q ^ m = w := ⟨_, by positivity, rfl⟩
  rw [hw, ← Real.rpow_natCast ((K * w ^ 3) ^ q) 2, ← Real.rpow_mul (by positivity),
    Real.mul_rpow hK (by positivity), ← Rigidity.Corrector.rpow_natCast_mul_eq hw0 3]
  congr 2
  all_goals (push_cast; ring)

section Holds

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **The moments of Dario's sums (3.18) on `ℤᵈ`**: for the Lipschitz bounds `Λ` of the
corrector, the sums `W(y) = stepOneW (Λ i) C₀ C y` satisfy `E[W(y)^q] ≤ (A q^k)^q` uniformly
in `y`. -/
theorem stepOneW_moments (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) (C₀ C : ℕ) :
    ∃ (Λ : Fin d → Vertex d → Configuration d → ℝ) (A k : ℝ), 0 < A ∧ 0 < k ∧
      (∀ i x, Measurable (Λ i x)) ∧ (∀ i x ω, 0 ≤ Λ i x ω) ∧
      (∀ i, ∀ᵐ ω ∂latticeBondLaw d p, ∀ x, ω ∈ infiniteComponentEvent x → ∀ y,
        (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω) ∧
      (∀ i y (q : ℝ), 1 ≤ q →
        ∫⁻ ω, stepOneW (Λ i) C₀ C y ω ^ q ∂latticeBondLaw d p ≤
          ENNReal.ofReal ((A * q ^ k) ^ q)) := by
  obtain ⟨Λ, B, κ, hB, hκ, hΛm, hΛ0, hlip, hmom⟩ :=
    stepOne_lipschitz_data hG hGv hd hpc hp1 hGae
  obtain ⟨θ', hθ', hexp⟩ := (partition_estimates hd hpc).2.1
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  have hd0 : 0 < d := by omega
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  set κ₁ : ℝ := d * ((C₀ : ℝ) * C + 1) with hκ₁
  set κ₃ : ℝ := d * ((C₀ : ℝ) * C + 1 + 3 * (C : ℝ) ^ 2) with hκ₃
  have hκ₁0 : 0 < κ₁ := by positivity
  have hκ₃0 : 0 < κ₃ := by positivity
  set A₁ : ℝ := (2 * (1 + 8 * d * (κ₃ * θ'))) ^ d * Real.sqrt 2 * (B * 2 ^ κ) with hA₁
  have hA₁0 : 0 < A₁ := by positivity
  set N : ℝ := 2 * d * (2 * d) ^ d with hN
  have hN1 : 1 ≤ N := by
    rw [hN]
    have h1 : (1 : ℝ) ≤ 2 * d := by linarith
    have h2 : (1 : ℝ) ≤ (2 * d) ^ d := one_le_pow₀ h1
    nlinarith
  set X : ℝ := N * (1 + 4 * (κ₁ * θ')) ^ d with hX
  set c : ℝ := (p : ℝ)⁻¹ * Real.sqrt 2 with hc
  set K₀ : ℝ := 16 * (d : ℝ) ^ 2 with hK₀
  have hX1 : 1 ≤ X := by
    have h0 : 0 ≤ κ₁ * θ' := by positivity
    have : 1 ≤ (1 + 4 * (κ₁ * θ')) ^ d := one_le_pow₀ (by linarith)
    nlinarith
  have hc1 : 1 ≤ c := by
    have h1 : 1 ≤ (p : ℝ)⁻¹ := one_le_inv₀ hp0 |>.2 hp1.le
    have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.one_le_sqrt]; norm_num
    nlinarith
  refine ⟨Λ, X * c * (K₀ * (A₁ * 6 ^ (κ + d)) ^ 3), 3 * (κ + d) + d, by positivity,
    by positivity, hΛm, hΛ0, hlip, fun i y q hq => ?_⟩
  have hq0 : 0 < q := by linarith
  set Y₀ : ℝ := K₀ * (A₁ * 6 ^ (κ + d)) ^ 3 * q ^ (3 * (κ + d)) with hY₀
  have hY₀0 : 0 ≤ Y₀ := by positivity
  -- the moments of the ball sums
  have hball : ∀ v, ∫⁻ ω, stepOneBallSum (Λ i) κ₃ v ω ^ (6 * q) ∂latticeBondLaw d p ≤
      ENNReal.ofReal ((A₁ * (6 * q) ^ (κ + d)) ^ (6 * q)) := by
    intro v
    unfold stepOneBallSum
    exact lintegral_randomBallSum_rpow_le_of_growth v (θ := κ₃ * θ') (by positivity)
      (fun t _ => measure_le_mul_stoppingSize_le hθ' hκ₃0 v (hexp v).1 (hexp v).2 t)
      ((measurable_stoppingSize_goodCubes v).const_mul κ₃)
      (fun x => (measurable_const.add (hΛm i x)).ennreal_ofReal) hB (hmom i) (by linarith)
  -- the arithmetic of the sixfold moments
  have hsix : K₀ ^ (2 * q) * (A₁ * (6 * q) ^ (κ + d)) ^ (6 * q) = (Y₀ ^ q) ^ 2 := by
    rw [hY₀]
    exact sixfold_moment_eq_const (by positivity) hA₁0.le hq0
  -- the moments of the factor of each bond
  have hedge : ∀ e : Bond d,
      ∫⁻ ω, stepOneFactor (Λ i) C₀ C e y ω ^ q ∂latticeBondLaw d p ≤
        ENNReal.ofReal (c * Y₀ ^ q * Real.exp
          (-(‖latticeEuclideanEmbedding (bondBase e - y)‖ / (2 * (κ₁ * θ'))))) := by
    intro e
    have hfm : Measurable fun ω => stepOneFactorSelf (Λ i) C₀ C e y ω ^ q :=
      (measurable_stepOneFactorSelf (hΛm i) C₀ C e y).pow_const q
    have hflip := ofReal_bondWeight_mul_lintegral_setBond_le p hfm e true
    have hbw : Rigidity.Corrector.bondWeight p true = p := by simp [Rigidity.Corrector.bondWeight]
    rw [hbw] at hflip
    have hne : ENNReal.ofReal (p : ℝ) ≠ 0 := by simp [hp0]
    have h1 : ∫⁻ ω, stepOneFactor (Λ i) C₀ C e y ω ^ q ∂latticeBondLaw d p ≤
        ENNReal.ofReal (p : ℝ)⁻¹ *
          ∫⁻ ω, stepOneFactorSelf (Λ i) C₀ C e y ω ^ q ∂latticeBondLaw d p := by
      calc ∫⁻ ω, stepOneFactor (Λ i) C₀ C e y ω ^ q ∂latticeBondLaw d p
          = ∫⁻ ω, stepOneFactorSelf (Λ i) C₀ C e y (setBond e true ω) ^ q
              ∂latticeBondLaw d p :=
            lintegral_congr fun ω => by rw [stepOneFactor_eq_self]
        _ = (ENNReal.ofReal (p : ℝ))⁻¹ * (ENNReal.ofReal (p : ℝ) *
              ∫⁻ ω, stepOneFactorSelf (Λ i) C₀ C e y (setBond e true ω) ^ q
                ∂latticeBondLaw d p) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]
        _ ≤ (ENNReal.ofReal (p : ℝ))⁻¹ *
              ∫⁻ ω, stepOneFactorSelf (Λ i) C₀ C e y ω ^ q ∂latticeBondLaw d p :=
            mul_le_mul_right hflip _
        _ = _ := by rw [ENNReal.ofReal_inv_of_pos hp0]
    set t := ‖latticeEuclideanEmbedding (bondBase e - y)‖ with ht
    set Z : Configuration d → ℝ≥0∞ := fun ω =>
      ENNReal.ofReal K₀ * stepOneBallSum (Λ i) κ₃ (bondBase e) ω ^ 3 with hZ
    have hZm : Measurable Z :=
      measurable_const.mul ((measurable_stepOneBallSum (hΛm i) κ₃ _).pow_const 3)
    have h2 : ∫⁻ ω, stepOneFactorSelf (Λ i) C₀ C e y ω ^ q ∂latticeBondLaw d p ≤
        ∫⁻ ω, {ω' | t ≤ κ₁ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω')
          (bondBase e)}.indicator Z ω ^ q ∂latticeBondLaw d p := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_partitionEvent hd hpc] with ω hP
      exact ENNReal.rpow_le_rpow (stepOneFactorSelf_le (hΛ0 i) C₀ C e y hP) hq0.le
    have hZ2 : ∫⁻ ω, Z ω ^ (2 * q) ∂latticeBondLaw d p ≤ ENNReal.ofReal ((Y₀ ^ q) ^ 2) := by
      calc ∫⁻ ω, Z ω ^ (2 * q) ∂latticeBondLaw d p
          = ∫⁻ ω, ENNReal.ofReal (K₀ ^ (2 * q)) *
              stepOneBallSum (Λ i) κ₃ (bondBase e) ω ^ (6 * q) ∂latticeBondLaw d p := by
            refine lintegral_congr fun ω => ?_
            simp only [hZ]
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
              ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
              ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
            congr 2
            push_cast
            ring
        _ = ENNReal.ofReal (K₀ ^ (2 * q)) *
              ∫⁻ ω, stepOneBallSum (Λ i) κ₃ (bondBase e) ω ^ (6 * q) ∂latticeBondLaw d p :=
            lintegral_const_mul _ ((measurable_stepOneBallSum (hΛm i) κ₃ _).pow_const _)
        _ ≤ ENNReal.ofReal (K₀ ^ (2 * q)) *
              ENNReal.ofReal ((A₁ * (6 * q) ^ (κ + d)) ^ (6 * q)) := by
            gcongr
            exact hball _
        _ = ENNReal.ofReal ((Y₀ ^ q) ^ 2) := by
            rw [← ENNReal.ofReal_mul (by positivity), hsix]
    have h3 := lintegral_indicator_rpow_le (p := p) (A := {ω' | t ≤ κ₁ *
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω') (bondBase e)})
      (measurableSet_le measurable_const ((measurable_stoppingSize_goodCubes _).const_mul κ₁))
      hZm hq0 (c := 2 * Real.exp (-(t / (κ₁ * θ')))) (m := Y₀ ^ q) (by positivity)
      (by positivity) (measure_le_mul_stoppingSize_le hθ' hκ₁0 _ (hexp _).1 (hexp _).2 t) hZ2
    calc ∫⁻ ω, stepOneFactor (Λ i) C₀ C e y ω ^ q ∂latticeBondLaw d p
        ≤ ENNReal.ofReal (p : ℝ)⁻¹ *
            ENNReal.ofReal (Real.sqrt (2 * Real.exp (-(t / (κ₁ * θ')))) * Y₀ ^ q) :=
          h1.trans (mul_le_mul_right (h2.trans h3) _)
      _ = ENNReal.ofReal (c * Y₀ ^ q * Real.exp (-(t / (2 * (κ₁ * θ'))))) := by
          rw [← ENNReal.ofReal_mul (by positivity), Rigidity.Corrector.sqrt_two_mul_exp_neg,
            show t / (κ₁ * θ') / 2 = t / (2 * (κ₁ * θ')) by rw [div_div, mul_comm 2]]
          congr 1
          rw [hc]
          ring
  -- Jensen's inequality over the bonds
  letI : MeasurableSpace (Bond d) := ⊤
  haveI : MeasurableSingletonClass (Bond d) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hJ := lintegral_tsum_rpow_le_of_decay (ι := Bond d) (p := p)
    (I := fun e => stepOneFactor (Λ i) C₀ C e y)
    (fun e => measurable_stepOneFactor (hΛm i) C₀ C _ y)
    (a := fun e => ‖latticeEuclideanEmbedding (bondBase e - y)‖)
    (fun e => norm_nonneg _) hq (θ := κ₁ * θ') (by positivity) (M := c * Y₀ ^ q) (N := N)
    (m := d) (by positivity) (by positivity)
    (fun κ' hκ' => tsum_exp_neg_norm_bondBase_le hd0 y hκ') hedge
  have hbase : N * (1 + 4 * q * (κ₁ * θ')) ^ d ≤ X * q ^ d := by
    have h1 : 1 + 4 * q * (κ₁ * θ') ≤ q * (1 + 4 * (κ₁ * θ')) := by
      have h0 : 0 ≤ κ₁ * θ' := by positivity
      nlinarith
    have h0 : 0 ≤ 1 + 4 * q * (κ₁ * θ') := by positivity
    have := pow_le_pow_left₀ h0 h1 d
    rw [hX, mul_pow] at *
    calc N * (1 + 4 * q * (κ₁ * θ')) ^ d ≤ N * (q ^ d * (1 + 4 * (κ₁ * θ')) ^ d) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = N * (1 + 4 * (κ₁ * θ')) ^ d * q ^ d := by ring
  have hXq1 : (X * q ^ d) ^ (q - 1) * X ≤ (X * q ^ d) ^ q := by
    have hXq : 0 < X * q ^ d := by positivity
    rw [Real.rpow_sub hXq, Real.rpow_one, div_mul_eq_mul_div, div_le_iff₀ hXq]
    have : 0 ≤ (X * q ^ d) ^ q := by positivity
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity)
      (one_le_pow₀ hq)) this
  have hcq : c ≤ c ^ q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hc1 hq
  calc ∫⁻ ω, stepOneW (Λ i) C₀ C y ω ^ q ∂latticeBondLaw d p
      = ∫⁻ ω, (∑' e, stepOneFactor (Λ i) C₀ C e y ω) ^ q ∂latticeBondLaw d p := rfl
    _ ≤ _ := hJ
    _ ≤ ENNReal.ofReal ((X * c * (K₀ * (A₁ * 6 ^ (κ + d)) ^ 3) * q ^ (3 * (κ + d) + d)) ^ q) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (N * (1 + 4 * q * (κ₁ * θ')) ^ d) ^ (q - 1) *
              (c * Y₀ ^ q * (N * (1 + 4 * (κ₁ * θ')) ^ d))
            ≤ (X * q ^ d) ^ (q - 1) * (X * (c * Y₀ ^ q)) := by
              rw [show c * Y₀ ^ q * (N * (1 + 4 * (κ₁ * θ')) ^ d) = X * (c * Y₀ ^ q) by
                rw [hX]; ring]
              exact mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow (by positivity) hbase (by linarith)) (by positivity)
          _ = ((X * q ^ d) ^ (q - 1) * X) * (c * Y₀ ^ q) := by ring
          _ ≤ (X * q ^ d) ^ q * (c ^ q * Y₀ ^ q) :=
              mul_le_mul hXq1 (mul_le_mul_of_nonneg_right hcq (by positivity)) (by positivity)
                (by positivity)
          _ = (X * c * (K₀ * (A₁ * 6 ^ (κ + d)) ^ 3) * q ^ (3 * (κ + d) + d)) ^ q := by
              rw [← Real.mul_rpow (by positivity) hY₀0,
                ← Real.mul_rpow (by positivity) (by positivity), hY₀,
                Real.rpow_add hq0, Real.rpow_natCast]
              congr 1
              ring

/-- **Step 1 of Lemma 3.3 of Dario on `ℤᵈ`, given Lemma 3.5**: the sum over the bonds of the
squares of the change-of-partition terms is almost surely finite and `O_s(C' r^{-d})`. -/
theorem flipSumOne_isOsBond_of_resample (hd : 2 ≤ d) {C₀ C : ℕ} (hC₀ : 0 < C₀)
    (hres : ResamplePartitionBound (d := d) C₀ C) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) :
    ∃ s C' : ℝ, 0 < s ∧ 0 < C' ∧ ∀ (i j : Fin d) (r : ℝ), 1 ≤ r → ∀ x : Vertex d,
      (∀ᵐ ω ∂latticeBondLaw d p, flipSumOne hG hGv i j r x ω < ∞) ∧
      IsOsBond d p (fun ω => (flipSumOne hG hGv i j r x ω).toReal) s (C' / r ^ (d : ℝ)) := by
  obtain ⟨Λ, A, k, hA, hk, hΛm, hΛ0, hlip, hmom⟩ :=
    stepOneW_moments hG hGv hd hpc hp1 hGae C₀ C
  obtain ⟨s, C', hs, hC', h⟩ := isOsBond_heatSqSum_of_moments (d := d) (p := p) hA hk
  refine ⟨s, C', hs, hC', fun i j r hr x => ?_⟩
  have hle := ae_flipSumOne_le hG hGv hd hpc hp1 hGae hC₀ hres (Λ := Λ i)
    (fun z ω => hΛ0 i z ω) (hlip i)
  refine h r hr x (stepOneW (Λ i) C₀ C) (fun y => measurable_stepOneW (hΛm i) C₀ C y) (hmom i) _
    (measurable_flipSumOne hG hGv i j r x) ?_
  filter_upwards [hle] with ω hω
  exact hω j r x

/-- **The heat series of the change of partition converges**: with Lemma 3.5 the change of
partition of each bond is supported in a box (`partitionChange_eq_zero`), so the series of
`T₁(e)` is a finite sum. -/
theorem flipTermOneSummable_of_resample (hd : 2 ≤ d) {C₀ C : ℕ}
    (hres : ResamplePartitionBound (d := d) C₀ C) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (i j : Fin d) (r : ℝ)
    (x : Vertex d) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ e, FlipTermOneSummable hG hGv i j r x e ω := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 (ae_partitionEvent hd hpc)] with ω hP' e
  have hloc := resampleLocal_of_bound hres (setBond_agree_off e false true ω) (hP' e false)
    (hP' e true) (bondBase_mem e)
  set ρ := C₀ * 3 ^ (partitionCube (setBond e false ω) (bondBase e)).scale
  set B : Finset (Vertex d) := supBox (bondBase e) ρ
  refine summable_of_ne_finset_zero (s := B) fun y hy => ?_
  have h0 : partitionChange (setBond e false ω) (setBond e true ω)
      (flipCorrector hG hGv i true e ω) j y = 0 := by
    refine partitionChange_eq_zero hloc _ j (fun hb => hy ?_) (fun hb => hy ?_)
    · rw [mem_supBox]
      exact fun i => (hb i).le
    · rw [mem_supBox]
      intro i
      have t := abs_sub_le (y i) ((y + LatticeProb.unit j) i) (bondBase e i)
      have h1 := (abs_sub_add_unit_le y j i).1
      have h2 := Int.add_one_le_iff.mpr (hb i)
      linarith
  show zdHeat d (r ^ 2) x y * partitionChange (setBond e false ω) (setBond e true ω)
    (flipCorrector hG hGv i true e ω) j y = 0
  rw [h0, mul_zero]

end Holds

/-- **The bound of the Step 1 sum of the proof of Lemma 3.3 of Dario in dimension `d ≥ 3`, from
Lemma 3.5 for the partition into good cubes of `ℤᵈ`.** -/
theorem darioStepOneSumBoundThree_of_resample (h35 : DarioResamplePartitionThree) :
    DarioStepOneSumBoundThree := by
  intro d _ hd3 p hpc hp1 G hG hGv hGae
  have hd : 2 ≤ d := by omega
  obtain ⟨C₀, C, hC₀, hres⟩ := h35 d hd3
  obtain ⟨s, C', hs, hC', h⟩ := flipSumOne_isOsBond_of_resample hG hGv hd hC₀ hres hpc hp1 hGae
  refine ⟨s, C', hs, hC', fun i j r hr x => ?_⟩
  obtain ⟨hf, hO⟩ := h i j r hr x
  exact ⟨flipTermOneSummable_of_resample hG hGv hd hres hpc hp1 i j r x, hf, hO⟩

/-- **Dario, Lemma 3.3 in dimension `d ≥ 3`, from Lemma 3.5 and the bound of the Step 2 sum.** -/
theorem darioVarianceBoundThree_of_resample (h35 : DarioResamplePartitionThree)
    (h2 : DarioStepTwoSumBoundThree) : DarioVarianceBoundThree :=
  darioVarianceBoundThree_of_sums (darioStepOneSumBoundThree_of_resample h35) h2

end Rigidity.Corrector.GeneralDim
