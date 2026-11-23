import Rigidity.Proofs.Corrector.DarioStepOneW

/-!
# Step 1 of Lemma 3.3 of Dario from Lemma 3.5

`stepOneW_moments`: the sums (3.18) `W(y) = Σ_e 1{y ∈ B_e} F_e` satisfy
`E[W(y)^q] ≤ (A q^k)^q` for all `y` and `q ≥ 1`, for the Lipschitz bounds `Λ` of
`stepOne_lipschitz_data`. For each bond, the factor of `W` at `ω` is the factor computed in
`ω^{e,1}` (`stepOneFactor_eq_self`), whose moments are at most `p^{-1}` times those of the factor
computed in `ω` ((3.12) in the form `ofReal_bondWeight_mul_lintegral_setBond_le`); the latter is at
most `1{|a_e - y| ≤ κ₁ s} 64 T³` (`stepOneFactorSelf_le`), whose moments decay exponentially in
`|a_e - y|` (Cauchy–Schwarz, the tail of the partition size and the moments of the ball sum `T`).
Jensen's inequality over the bonds (`lintegral_tsum_rpow_le_of_decay`) then bounds the moments
of `W(y)`.

`flipSumOne_isOsBond_of_resample`: given Lemma 3.5 (`ResamplePartitionBound C₀ C`), the Step 1
sum `Σ_e T₁(e)²` is almost surely finite and `O_s(C'/r²)`; the order-zero regularity input is
`armstrongDarioOrderZeroTwo_holds`. `darioFlipSumBound_of_resample` reduces the flip form
(3.13) of Lemma 3.3 to Lemma 3.5 and the Step 2 sum.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare
open scoped Classical ENNReal

/-- `√(2 e^{-x}) = √2 e^{-x/2}`. -/
theorem sqrt_two_mul_exp_neg (x : ℝ) :
    Real.sqrt (2 * Real.exp (-x)) = Real.sqrt 2 * Real.exp (-(x / 2)) := by
  rw [Real.sqrt_mul (by norm_num)]
  congr 1
  have : Real.exp (-x) = Real.exp (-(x / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [this, Real.sqrt_sq (Real.exp_pos _).le]

/-- The arithmetic of the sixfold moments of the ball sums. -/
theorem sixfold_moment_eq {A₁ κ q : ℝ} (hA : 0 ≤ A₁) (hq : 0 < q) :
    64 ^ (2 * q) * (A₁ * (6 * q) ^ (κ + 2)) ^ (6 * q) =
      ((64 * (A₁ * 6 ^ (κ + 2)) ^ 3 * q ^ (3 * (κ + 2))) ^ q) ^ 2 := by
  have h6 : (6 * q) ^ (κ + 2) = 6 ^ (κ + 2) * q ^ (κ + 2) := Real.mul_rpow (by norm_num) hq.le
  have h3 : q ^ (3 * (κ + 2)) = (q ^ (κ + 2)) ^ 3 := by
    rw [mul_comm, Real.rpow_mul hq.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e1 : A₁ * (6 ^ (κ + 2) * q ^ (κ + 2)) = A₁ * 6 ^ (κ + 2) * q ^ (κ + 2) := by ring
  have e2 : 64 * (A₁ * 6 ^ (κ + 2)) ^ 3 * (q ^ (κ + 2)) ^ 3 =
      64 * (A₁ * 6 ^ (κ + 2) * q ^ (κ + 2)) ^ 3 := by ring
  rw [h6, h3, e1, e2]
  obtain ⟨w, hw0, hw⟩ : ∃ w, 0 ≤ w ∧ A₁ * 6 ^ (κ + 2) * q ^ (κ + 2) = w :=
    ⟨_, by positivity, rfl⟩
  rw [hw, ← Real.rpow_natCast ((64 * w ^ 3) ^ q) 2, ← Real.rpow_mul (by positivity),
    Real.mul_rpow (by norm_num) (by positivity), ← rpow_natCast_mul_eq hw0 3]
  congr 2
  all_goals (push_cast; ring)

section Holds

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **The moments of Dario's sums (3.18)**: for the Lipschitz bounds `Λ` of the corrector, the
sums `W(y) = stepOneW (Λ i) C₀ C y` satisfy `E[W(y)^q] ≤ (A q^k)^q` uniformly in `y`. -/
theorem stepOneW_moments (hR3 : ArmstrongDarioOrderZeroTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) (C₀ C : ℕ) :
    ∃ (Λ : Fin 2 → Vertex 2 → Configuration 2 → ℝ) (A k : ℝ), 0 < A ∧ 0 < k ∧
      (∀ i x, Measurable (Λ i x)) ∧ (∀ i x ω, 0 ≤ Λ i x ω) ∧
      (∀ i, ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ x, ω ∈ infiniteComponentEvent x → ∀ y,
        (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω) ∧
      (∀ i y (q : ℝ), 1 ≤ q →
        ∫⁻ ω, stepOneW (Λ i) C₀ C y ω ^ q ∂latticeBondLaw 2 p ≤
          ENNReal.ofReal ((A * q ^ k) ^ q)) := by
  obtain ⟨Λ, B, κ, hB, hκ, hΛm, hΛ0, hlip, hmom⟩ :=
    stepOne_lipschitz_data hG hGv hR3 hpc hp1 hGae
  obtain ⟨θ', hθ', hexp⟩ := (planar_meshed_partition_estimates hpc).2.1
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  set κ₁ : ℝ := 2 * ((C₀ : ℝ) * C + 1) with hκ₁
  set κ₃ : ℝ := 2 * ((C₀ : ℝ) * C + 1 + 5 * (C : ℝ) ^ 2) with hκ₃
  have hκ₁0 : 0 < κ₁ := by positivity
  have hκ₃0 : 0 < κ₃ := by positivity
  set A₁ : ℝ := 4 * (1 + 8 * (κ₃ * θ')) ^ 2 * Real.sqrt 2 * (B * 2 ^ κ) with hA₁
  have hA₁0 : 0 < A₁ := by positivity
  set X : ℝ := 64 * (1 + 4 * (κ₁ * θ')) ^ 2 with hX
  set c : ℝ := (p : ℝ)⁻¹ * Real.sqrt 2 with hc
  have hX1 : 1 ≤ X := by
    have h0 : 0 ≤ κ₁ * θ' := by positivity
    have : 1 ≤ 1 + 4 * (κ₁ * θ') := by linarith
    nlinarith
  have hc1 : 1 ≤ c := by
    have h1 : 1 ≤ (p : ℝ)⁻¹ := one_le_inv₀ hp0 |>.2 hp1.le
    have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.one_le_sqrt]; norm_num
    nlinarith
  refine ⟨Λ, X * c * (64 * (A₁ * 6 ^ (κ + 2)) ^ 3), 3 * (κ + 2) + 2, by positivity,
    by positivity, hΛm, hΛ0, hlip, fun i y q hq => ?_⟩
  have hq0 : 0 < q := by linarith
  set Y₀ : ℝ := 64 * (A₁ * 6 ^ (κ + 2)) ^ 3 * q ^ (3 * (κ + 2)) with hY₀
  have hY₀0 : 0 ≤ Y₀ := by positivity
  -- the moments of the ball sums
  have hball : ∀ v, ∫⁻ ω, stepOneBallSum (Λ i) κ₃ v ω ^ (6 * q) ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal ((A₁ * (6 * q) ^ (κ + 2)) ^ (6 * q)) := by
    intro v
    unfold stepOneBallSum
    exact lintegral_randomBallSum_rpow_le_of_growth v (θ := κ₃ * θ') (by positivity)
      (fun t _ => measure_le_mul_stoppingSize_le hθ' hκ₃0 v (hexp v).1 (hexp v).2 t)
      ((measurable_stoppingSize_planar v).const_mul κ₃)
      (fun x => (measurable_const.add (hΛm i x)).ennreal_ofReal) hB (hmom i) (by linarith)
  -- the moments of the factor of each bond
  have hedge : ∀ a : LatticeEdge,
      ∫⁻ ω, stepOneFactor (Λ i) C₀ C (edgeBond a) y ω ^ q ∂latticeBondLaw 2 p ≤
        ENNReal.ofReal (c * Y₀ ^ q * Real.exp
          (-(‖latticeEuclideanEmbedding (bondBase (edgeBond a) - y)‖ / (2 * (κ₁ * θ'))))) := by
    intro a
    have hfm : Measurable fun ω => stepOneFactorSelf (Λ i) C₀ C (edgeBond a) y ω ^ q :=
      (measurable_stepOneFactorSelf (hΛm i) C₀ C (edgeBond a) y).pow_const q
    have hflip := ofReal_bondWeight_mul_lintegral_setBond_le p hfm (edgeBond a) true
    have hbw : bondWeight p true = p := by simp [bondWeight]
    rw [hbw] at hflip
    have hne : ENNReal.ofReal (p : ℝ) ≠ 0 := by simp [hp0]
    have h1 : ∫⁻ ω, stepOneFactor (Λ i) C₀ C (edgeBond a) y ω ^ q ∂latticeBondLaw 2 p ≤
        ENNReal.ofReal (p : ℝ)⁻¹ *
          ∫⁻ ω, stepOneFactorSelf (Λ i) C₀ C (edgeBond a) y ω ^ q ∂latticeBondLaw 2 p := by
      calc ∫⁻ ω, stepOneFactor (Λ i) C₀ C (edgeBond a) y ω ^ q ∂latticeBondLaw 2 p
          = ∫⁻ ω, stepOneFactorSelf (Λ i) C₀ C (edgeBond a) y (setBond (edgeBond a) true ω) ^ q
              ∂latticeBondLaw 2 p :=
            lintegral_congr fun ω => by rw [stepOneFactor_eq_self]
        _ = (ENNReal.ofReal (p : ℝ))⁻¹ * (ENNReal.ofReal (p : ℝ) *
              ∫⁻ ω, stepOneFactorSelf (Λ i) C₀ C (edgeBond a) y (setBond (edgeBond a) true ω) ^ q
                ∂latticeBondLaw 2 p) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]
        _ ≤ (ENNReal.ofReal (p : ℝ))⁻¹ *
              ∫⁻ ω, stepOneFactorSelf (Λ i) C₀ C (edgeBond a) y ω ^ q ∂latticeBondLaw 2 p :=
            mul_le_mul_right hflip _
        _ = _ := by rw [ENNReal.ofReal_inv_of_pos hp0]
    set t := ‖latticeEuclideanEmbedding (bondBase (edgeBond a) - y)‖ with ht
    set Z : Configuration 2 → ℝ≥0∞ := fun ω =>
      ENNReal.ofReal 64 * stepOneBallSum (Λ i) κ₃ (bondBase (edgeBond a)) ω ^ 3 with hZ
    have hZm : Measurable Z :=
      measurable_const.mul ((measurable_stepOneBallSum (hΛm i) κ₃ _).pow_const 3)
    have h2 : ∫⁻ ω, stepOneFactorSelf (Λ i) C₀ C (edgeBond a) y ω ^ q ∂latticeBondLaw 2 p ≤
        ∫⁻ ω, {ω' | t ≤ κ₁ * TriadicCube.stoppingSize (planarGoodCubes ω')
          (bondBase (edgeBond a))}.indicator Z ω ^ q ∂latticeBondLaw 2 p := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_planarPartitionEvent hpc] with ω hP
      exact ENNReal.rpow_le_rpow (stepOneFactorSelf_le (hΛ0 i) C₀ C (edgeBond a) y hP) hq0.le
    have hZ2 : ∫⁻ ω, Z ω ^ (2 * q) ∂latticeBondLaw 2 p ≤ ENNReal.ofReal ((Y₀ ^ q) ^ 2) := by
      calc ∫⁻ ω, Z ω ^ (2 * q) ∂latticeBondLaw 2 p
          = ∫⁻ ω, ENNReal.ofReal (64 ^ (2 * q)) *
              stepOneBallSum (Λ i) κ₃ (bondBase (edgeBond a)) ω ^ (6 * q) ∂latticeBondLaw 2 p := by
            refine lintegral_congr fun ω => ?_
            simp only [hZ]
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
              ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by positivity),
              ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
            congr 2
            push_cast
            ring
        _ = ENNReal.ofReal (64 ^ (2 * q)) *
              ∫⁻ ω, stepOneBallSum (Λ i) κ₃ (bondBase (edgeBond a)) ω ^ (6 * q)
                ∂latticeBondLaw 2 p :=
            lintegral_const_mul _ ((measurable_stepOneBallSum (hΛm i) κ₃ _).pow_const _)
        _ ≤ ENNReal.ofReal (64 ^ (2 * q)) *
              ENNReal.ofReal ((A₁ * (6 * q) ^ (κ + 2)) ^ (6 * q)) := by
            gcongr
            exact hball _
        _ = ENNReal.ofReal ((Y₀ ^ q) ^ 2) := by
            rw [← ENNReal.ofReal_mul (by positivity), hY₀, sixfold_moment_eq hA₁0.le hq0]
    have h3 := lintegral_indicator_rpow_le (p := p) (A := {ω' | t ≤ κ₁ *
        TriadicCube.stoppingSize (planarGoodCubes ω') (bondBase (edgeBond a))})
      (measurableSet_le measurable_const ((measurable_stoppingSize_planar _).const_mul κ₁)) hZm
      hq0 (c := 2 * Real.exp (-(t / (κ₁ * θ')))) (m := Y₀ ^ q) (by positivity) (by positivity)
      (measure_le_mul_stoppingSize_le hθ' hκ₁0 _ (hexp _).1 (hexp _).2 t) hZ2
    calc ∫⁻ ω, stepOneFactor (Λ i) C₀ C (edgeBond a) y ω ^ q ∂latticeBondLaw 2 p
        ≤ ENNReal.ofReal (p : ℝ)⁻¹ *
            ENNReal.ofReal (Real.sqrt (2 * Real.exp (-(t / (κ₁ * θ')))) * Y₀ ^ q) :=
          h1.trans (mul_le_mul_right (h2.trans h3) _)
      _ = ENNReal.ofReal (c * Y₀ ^ q * Real.exp (-(t / (2 * (κ₁ * θ'))))) := by
          rw [← ENNReal.ofReal_mul (by positivity), sqrt_two_mul_exp_neg,
            show t / (κ₁ * θ') / 2 = t / (2 * (κ₁ * θ')) by rw [div_div, mul_comm 2]]
          congr 1
          rw [hc]
          ring
  -- the sum over the bonds as a sum over the oriented edges
  have hWsum : ∀ ω, stepOneW (Λ i) C₀ C y ω =
      ∑' a : LatticeEdge, stepOneFactor (Λ i) C₀ C (edgeBond a) y ω := fun ω =>
    ((Equiv.ofBijective edgeBond ⟨edgeBond_injective, fun e => exists_edgeBond_eq e⟩).tsum_eq
      (fun e => stepOneFactor (Λ i) C₀ C e y ω)).symm
  have hJ := lintegral_tsum_rpow_le_of_decay (ι := LatticeEdge) (p := p)
    (I := fun a => stepOneFactor (Λ i) C₀ C (edgeBond a) y)
    (fun a => measurable_stepOneFactor (hΛm i) C₀ C _ y)
    (a := fun a => ‖latticeEuclideanEmbedding (bondBase (edgeBond a) - y)‖)
    (fun a => norm_nonneg _) hq (θ := κ₁ * θ') (by positivity) (M := c * Y₀ ^ q) (N := 64)
    (by positivity) (by norm_num) (fun κ' hκ' => tsum_exp_neg_norm_bondBase_le y hκ') hedge
  have hbase : 64 * (1 + 4 * q * (κ₁ * θ')) ^ 2 ≤ X * q ^ 2 := by
    have h1 := one_add_mul_le_mul (b := 4) (θ := κ₁ * θ') hq
    have h0 : 0 ≤ 1 + 4 * q * (κ₁ * θ') := by positivity
    have := pow_le_pow_left₀ h0 h1 2
    rw [hX]
    nlinarith
  calc ∫⁻ ω, stepOneW (Λ i) C₀ C y ω ^ q ∂latticeBondLaw 2 p
      = ∫⁻ ω, (∑' a : LatticeEdge, stepOneFactor (Λ i) C₀ C (edgeBond a) y ω) ^ q
          ∂latticeBondLaw 2 p := lintegral_congr fun ω => by rw [hWsum]
    _ ≤ _ := hJ
    _ ≤ ENNReal.ofReal ((X * c * (64 * (A₁ * 6 ^ (κ + 2)) ^ 3) * q ^ (3 * (κ + 2) + 2)) ^ q) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (64 * (1 + 4 * q * (κ₁ * θ')) ^ 2) ^ (q - 1) *
              (c * Y₀ ^ q * (64 * (1 + 4 * (κ₁ * θ')) ^ 2))
            ≤ (X * q ^ 2) ^ (q - 1) * (X * (c * Y₀ ^ q)) := by
              rw [show c * Y₀ ^ q * (64 * (1 + 4 * (κ₁ * θ')) ^ 2) = X * (c * Y₀ ^ q) by
                rw [hX]; ring]
              exact mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow (by positivity) hbase (by linarith)) (by positivity)
          _ ≤ (X * c * Y₀ * q ^ 2) ^ q := rpow_sub_one_mul_le hX1 hc1 hY₀0 hq
          _ = (X * c * (64 * (A₁ * 6 ^ (κ + 2)) ^ 3) * q ^ (3 * (κ + 2) + 2)) ^ q := by
              rw [hY₀, Real.rpow_add hq0, Real.rpow_two]
              congr 1
              ring

/-- **Step 1 of Lemma 3.3 of Dario, given Lemma 3.5**: the sum over the bonds of the squares of
the change-of-partition terms is almost surely finite and `O_s(C'/r²)`. -/
theorem flipSumOne_isOsBond_of_resample {C₀ C : ℕ} (hC₀ : 0 < C₀)
    (hres : ResamplePartitionBound C₀ C) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∃ s C' : ℝ, 0 < s ∧ 0 < C' ∧ ∀ (i j : Fin 2) (r : ℝ), 1 ≤ r → ∀ x : Vertex 2,
      (∀ᵐ ω ∂latticeBondLaw 2 p, flipSumOne hG hGv i j r x ω < ∞) ∧
      IsOsBond 2 p (fun ω => (flipSumOne hG hGv i j r x ω).toReal) s (C' / r ^ 2) := by
  obtain ⟨Λ, A, k, hA, hk, hΛm, hΛ0, hlip, hmom⟩ :=
    stepOneW_moments hG hGv Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_holds hpc hp1
      hGae C₀ C
  obtain ⟨s, C', hs, hC', h⟩ := isOsBond_heatSqSum_of_moments (p := p) hA hk
  refine ⟨s, C', hs, hC', fun i j r hr x => ?_⟩
  have hle := ae_flipSumOne_le hG hGv hpc hp1 hGae hC₀ hres (Λ := Λ i) (fun z ω => hΛ0 i z ω)
    (hlip i)
  refine h r hr x (stepOneW (Λ i) C₀ C) (fun y => measurable_stepOneW (hΛm i) C₀ C y) (hmom i) _
    (measurable_flipSumOne hG hGv i j r x) ?_
  filter_upwards [hle] with ω hω
  exact hω j r x

end Holds

/-- **The flip form (3.13) of Lemma 3.3 of Dario from Lemma 3.5 and Step 2**: Lemma 3.5 for the
planar partition (`DarioResamplePartitionTwo`) and the bound of the Step 2 sum `Σ_e T₂(e)²`
give `DarioFlipSumBound`. -/
theorem darioFlipSumBound_of_resample (h35 : DarioResamplePartitionTwo)
    (hTwo : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∀ (G : Set (Configuration 2)) (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2),
        (∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
          ∀ (i j : Fin 2) (r : ℝ), 1 ≤ r → ∀ x : Vertex 2,
            (∀ᵐ ω ∂latticeBondLaw 2 p, flipSumTwo hG hGv i j r x ω < ∞) ∧
            IsOsBond 2 p (fun ω => (flipSumTwo hG hGv i j r x ω).toReal) s (C / r ^ 2)) :
    DarioFlipSumBound := by
  obtain ⟨C₀, C, hC₀, hres⟩ := h35
  refine darioFlipSumBound_of_stepSums fun p hpc hp1 G hG hGv hGae => ?_
  obtain ⟨s₁, C₁, hs₁, hC₁, h1⟩ := flipSumOne_isOsBond_of_resample hG hGv hC₀ hres hpc hp1 hGae
  obtain ⟨s₂, C₂, hs₂, hC₂, h2⟩ := hTwo p hpc hp1 G hG hGv hGae
  set s := min s₁ s₂
  have hs : 0 < s := lt_min hs₁ hs₂
  refine ⟨s, max C₁ C₂ * 6 ^ (1 / s), hs, by positivity, fun i j r hr x => ?_⟩
  have hr0 : 0 < r ^ 2 := by positivity
  obtain ⟨hf1, hO1⟩ := h1 i j r hr x
  obtain ⟨hf2, hO2⟩ := h2 i j r hr x
  have hm1 : Measurable fun ω => (flipSumOne hG hGv i j r x ω).toReal :=
    (measurable_flipSumOne hG hGv i j r x).ennreal_toReal
  have hm2 : Measurable fun ω => (flipSumTwo hG hGv i j r x ω).toReal :=
    (measurable_flipSumTwo hG hGv i j r x).ennreal_toReal
  have hfin : ∀ {C'' : ℝ}, C'' ≤ max C₁ C₂ →
      C'' / r ^ 2 * 6 ^ (1 / s) ≤ max C₁ C₂ * 6 ^ (1 / s) / r ^ 2 := fun h => by
    rw [div_mul_eq_mul_div]
    gcongr
  refine ⟨hf1, hf2, ?_, ?_⟩
  · exact Rigidity.Proofs.S2.IsOsBond.mono_scale hs (by positivity) (hfin (le_max_left _ _)) hm1
      (Rigidity.Proofs.S2.IsOsBond.mono_exponent hs (min_le_left _ _) hm1 hO1)
  · exact Rigidity.Proofs.S2.IsOsBond.mono_scale hs (by positivity) (hfin (le_max_right _ _)) hm2
      (Rigidity.Proofs.S2.IsOsBond.mono_exponent hs (min_le_right _ _) hm2 hO2)

end Rigidity.Corrector
