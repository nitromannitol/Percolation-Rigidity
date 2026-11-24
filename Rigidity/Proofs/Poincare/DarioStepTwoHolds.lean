import Rigidity.Proofs.Poincare.DarioStepTwoBridges
import Rigidity.Proofs.Corrector.DarioStepTwoFinalMoments

/-!
# The Step 2 sum of Lemma 3.3 of Dario, in dimension two

The bound of the Step 2 sum `Σ_e T₂(e)²` of the proof of Lemma 3.3 of Dario (`DarioStepTwoSumBound`)
holds (`darioStepTwoSumBound_holds`). Almost surely the good cubes of the summation of estimate (2)
partition `ℤ²` (`exists_stepTwoGood_partition`), and through this partition
`Σ_e T₂(e)² ≤ Σ_y Φ_{r²}(x, y)² W(y)` (`flipSumTwo_le_of_partition`) with
`W(y) = K₀ (W₂(y) + 12 K pathWeight(y))`. The Step 2 weight `W₂(y)` is at most the majorant
built from the bound `Λ` of the corrector increments of Step 1 (`stepOne_lipschitz_data`,
`planeGrad_le_of_lipschitz`), and the path weight is at most `81σ(y)²` times a sum over the ball of
radius `12σ(y)` of the squared sizes of the good cubes times the weighted numbers of anchor
regions (`pathWeight_le_ballSum`). All these have moments of polynomial growth uniformly in `y`,
so `isOsBond_heatSqSum_of_moments` gives `Σ_e T₂(e)² = O_s(C/r²)`.

Consequently Theorem 1 of Dario in dimension two (`darioOptimalCorrectorTwo_holds`),
Proposition 2.12 of Dario and Gu in dimension two (`correctorQuantitativeInputTwo_holds`) and
Theorem 2 (iii) of Armstrong and Dario at `k = 1` at the origin in dimension two
(`armstrongDarioOrderOneOriginTwo_holds`) hold, in the forms of their statements in this
repository.
-/

namespace Rigidity.Poincare

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Corrector Rigidity.External Rigidity.Green
open scoped Classical ENNReal

section Grad

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

theorem rpow_nine_pow_le_sq {n : ℕ} {α : ℝ} (hα : α ≤ 1) :
    ((9 : ℝ) ^ n) ^ α ≤ ((3 : ℝ) ^ n) ^ 2 := by
  have h1 : (1 : ℝ) ≤ 9 ^ n := one_le_pow₀ (by norm_num)
  calc ((9 : ℝ) ^ n) ^ α ≤ ((9 : ℝ) ^ n) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hα
    _ = ((3 : ℝ) ^ n) ^ 2 := by
        rw [Real.rpow_one, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]

/-- **The weight of the Step 2 sum, with moments of polynomial growth**, for one direction `i`. -/
theorem exists_stepTwo_weight_data {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) (i : Fin 2) :
    ∃ (W : Vertex 2 → Configuration 2 → ℝ≥0∞) (A k : ℝ), 0 < A ∧ 0 < k ∧
      (∀ y, Measurable (W y)) ∧ (∀ y, GrowthMoments p (W y) A k) ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (j : Fin 2) (r : ℝ), 0 < r → ∀ x : Vertex 2,
        flipSumTwo hG hGv i j r x ω ≤
          ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) * W y ω := by
  have hκ : 1 ≤ 4747 + 5 * 14244 + 6 := by norm_num
  obtain ⟨ε, CM, M, hε, hCM, hM, s0, hs0, hpart⟩ :=
    exists_stepTwoGood_partition hG hGv hpc hp1 hGae hκ
  obtain ⟨hae, θ, hθ, hexpτ⟩ := hpart i
  obtain ⟨Λ, BΛ, κΛ, hBΛ, hκΛ, hΛm, hΛ0, hlip, hΛmom⟩ := stepOne_lipschitz_data hG hGv
    Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_holds hpc hp1 hGae
  -- the sizes of the good cubes
  have hτm : ∀ z, Measurable fun ω =>
      TriadicCube.stoppingSize (stepTwoGood hG hGv (4747 + 5 * 14244 + 6) i ε CM M ω) z :=
    TriadicCube.measurable_stoppingSize _ (measurableSet_mem_stepTwoGood hG hGv _ i ε CM M)
  have hτ2 := fun z => growthMoments_sq_of_exp_moment (hτm z) (fun ω => stoppingSize_nonneg' _ z)
    hθ hs0 (hexpτ z).1 (hexpτ z).2
  obtain ⟨A0, k0, hA0, hk0, hwm0⟩ := growthMoments_weightMajorant_zero (p := p) hpc
  have hwm0m : ∀ z, Measurable (weightMajorant (fun _ _ => 0) 12 10 z) := fun z =>
    measurable_weightMajorant (fun _ => measurable_const) 12 10 z
  set Y : Vertex 2 → Configuration 2 → ℝ≥0∞ := fun z ω => ENNReal.ofReal
    (TriadicCube.stoppingSize (stepTwoGood hG hGv (4747 + 5 * 14244 + 6) i ε CM M ω) z ^ 2) *
      weightMajorant (fun _ _ => 0) 12 10 z ω with hYdef
  have hYm : ∀ z, Measurable (Y z) := fun z => ((hτm z).pow_const 2).ennreal_ofReal.mul (hwm0m z)
  have hY := fun z => GrowthMoments.mul ((hτm z).pow_const 2).ennreal_ofReal.aemeasurable
    (hwm0m z).aemeasurable (hτ2 z) (hwm0 z) (by positivity) hA0.le
  obtain ⟨BS, kS, hBS, hkS, hS⟩ := growthMoments_planarBallSum hpc hYm (by positivity)
    (by positivity) hY
  obtain ⟨Bσ, kσ, hBσ, hkσ, hσ⟩ := growthMoments_planarSize_sq (p := p) hpc
  set S : Vertex 2 → Configuration 2 → ℝ≥0∞ := fun y ω => ∑' z,
    if ‖latticeEuclideanEmbedding (z - y)‖ ≤
      12 * TriadicCube.stoppingSize (planarGoodCubes ω) y then Y z ω else 0 with hSdef
  have hSm : ∀ y, Measurable (S y) := fun y => Measurable.tsum fun z =>
    Measurable.ite (measurableSet_le measurable_const
      ((measurable_stoppingSize_planar y).const_mul 12)) (hYm z) measurable_const
  have hσm : ∀ y, Measurable fun ω =>
      ENNReal.ofReal (81 * TriadicCube.stoppingSize (planarGoodCubes ω) y ^ 2) := fun y =>
    ((measurable_stoppingSize_planar y).pow_const 2).const_mul 81 |>.ennreal_ofReal
  have hP := fun y => GrowthMoments.mul (hσm y).aemeasurable (hSm y).aemeasurable (hσ y) (hS y)
    hBσ.le hBS.le
  -- the Step 2 weight
  have hΛ4 : ∀ z, GrowthMoments p (fun ω => ENNReal.ofReal (1 + 4 * Λ i z ω)) (4 * BΛ) κΛ := by
    intro z
    have h4 := (show GrowthMoments p (fun ω => ENNReal.ofReal (1 + Λ i z ω)) BΛ κΛ from
      fun q hq => hΛmom i z q hq).const_mul (c := 4) (by norm_num) hBΛ.le
    refine h4.mono fun ω => ?_
    rw [← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by linarith [hΛ0 i z ω])
  have hK : (0 : ℝ) < 6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ) := by positivity
  obtain ⟨AV, kV, hAV, hkV, hV⟩ := growthMoments_weightMajorant hpc
    (fun z => (hΛm i z).const_mul 4) (by positivity : (0 : ℝ) < 4 * BΛ) hκΛ hΛ4 hK hK
  have hVm : ∀ y, Measurable (weightMajorant (fun z ω => 4 * Λ i z ω)
      (6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ)) (6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ)) y) :=
    fun y => measurable_weightMajorant (fun z => (hΛm i z).const_mul 4) _ _ y
  -- the constants
  set Kc : ℝ := M ^ (1 / Real.conjExponent (1 + ε / 2)) + 48 * cellConst ε CM (9 * M) with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; unfold cellConst; positivity
  set K0 : ℝ := 2 * 1297 ^ 4 * 46656 with hK0
  set Bm : ℝ := max AV (12 * Kc * (Bσ * BS * 2 ^ (kσ + kS))) with hBm
  set km : ℝ := max kV (kσ + kS) with hkm
  have hBm0 : 0 < Bm := lt_max_of_lt_left hAV
  have hkm0 : 0 < km := lt_max_of_lt_left hkV
  have hW1 : ∀ y, GrowthMoments p (weightMajorant (fun z ω => 4 * Λ i z ω)
      (6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ)) (6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ)) y) Bm km :=
    fun y => (hV y).of_le hAV.le (le_max_left _ _) (le_max_left _ _)
  have hW2 : ∀ y, GrowthMoments p (fun ω => ENNReal.ofReal (12 * Kc) *
      (ENNReal.ofReal (81 * TriadicCube.stoppingSize (planarGoodCubes ω) y ^ 2) * S y ω)) Bm km :=
    fun y => ((hP y).const_mul (c := 12 * Kc) (by positivity) (by positivity)).of_le
      (by positivity) (le_max_right _ _) (le_max_right _ _)
  refine ⟨fun y ω => ENNReal.ofReal K0 * (weightMajorant (fun z ω => 4 * Λ i z ω)
      (6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ)) (6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ)) y ω +
      ENNReal.ofReal (12 * Kc) *
        (ENNReal.ofReal (81 * TriadicCube.stoppingSize (planarGoodCubes ω) y ^ 2) * S y ω)),
    K0 * (2 * Bm), km, by positivity, hkm0, fun y => ?_, fun y => ?_, ?_⟩
  · exact measurable_const.mul ((hVm y).add (measurable_const.mul ((hσm y).mul (hSm y))))
  · exact ((GrowthMoments.add (hVm y).aemeasurable (hW1 y) (hW2 y) hBm0.le).const_mul
      (c := K0) (by positivity) (by positivity))
  -- the almost sure bound
  filter_upwards [flipSumTwo_le_of_partition hG hGv (C₀ := 4747) (C := 14244) (by norm_num)
    resamplePartitionBound_holds hpc hp1 hGae hε hCM hM, hae, ae_planarPartitionEvent hpc,
    hlip i] with ω hfs hp hPω hl
  intro j r hr x
  refine (hfs i j r hr x hp).trans (ENNReal.tsum_le_tsum fun y => ?_)
  have h1 : stepTwoWeight hG hGv (4747 + 5 * 14244 + 6) i ω y ≤
      weightMajorant (fun z ω => 4 * Λ i z ω) (6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ))
        (6 * ((4747 + 5 * 14244 + 6 : ℕ) : ℝ)) y ω :=
    stepTwoWeight_le_weightMajorant hG hGv hPω (fun z => by positivity [hΛ0 i z ω])
      (fun z => planeGrad_le_of_lipschitz hG hGv (fun z => hΛ0 i z ω) hl z) y
  have hc : ∀ z, ENNReal.ofReal (((9 : ℝ) ^ partScale hp z) ^ (1 - 1 / (1 + ε / 2))) ≤
      ENNReal.ofReal
        (TriadicCube.stoppingSize (stepTwoGood hG hGv (4747 + 5 * 14244 + 6) i ε CM M ω) z ^
          2) := by
    intro z
    refine ENNReal.ofReal_le_ofReal ?_
    rw [TriadicCube.stoppingSize_eq_of_mem (partCell_spec hp z).1 (partCell_spec hp z).2]
    exact rpow_nine_pow_le_sq (by have : 0 ≤ 1 / (1 + ε / 2) := by positivity
                                  linarith)
  have h2 : 12 * ENNReal.ofReal Kc *
      pathWeight (fun z => ((9 : ℝ) ^ partScale hp z) ^ (1 - 1 / (1 + ε / 2))) ω j y ≤
      ENNReal.ofReal (12 * Kc) *
        (ENNReal.ofReal (81 * TriadicCube.stoppingSize (planarGoodCubes ω) y ^ 2) * S y ω) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    gcongr
    exact pathWeight_le_ballSum hPω hc j y
  gcongr

end Grad

/-- **The Step 2 sum of the proof of Lemma 3.3 of Dario, in dimension two**: for every
supercritical `p < 1` and every almost sure event `G` of valid correctors, `Σ_e T₂(e)²` is almost
surely finite and `O_s(C / r²)`. The source derives it from Proposition 3.6 (the Meyers estimate)
with the same exponent on the source and the gradient, which fails for Bernoulli clusters; the
proof here uses instead the Meyers estimate with a divergence source in the form of estimate (2),
summed over a partition into cubes carrying it and a bound of the weights on average. -/
theorem darioStepTwoSumBound_holds : DarioStepTwoSumBound := by
  intro p hpc hp1 G hG hGv hGae
  choose W A k hA hk hWm hWmom hWae using fun i => exists_stepTwo_weight_data hG hGv hpc hp1 hGae i
  obtain ⟨s, C, hs, hC, hOs⟩ := isOsBond_heatSqSum_of_moments (p := p) (A := ∑ i, A i)
    (k := ∑ i, k i) (Finset.sum_pos (fun i _ => hA i) Finset.univ_nonempty)
    (Finset.sum_pos (fun i _ => hk i) Finset.univ_nonempty)
  refine ⟨s, C, hs, hC, fun i j r hr x => ?_⟩
  have hAi : A i ≤ ∑ i, A i :=
    Finset.single_le_sum (fun i _ => (hA i).le) (Finset.mem_univ i)
  have hki : k i ≤ ∑ i, k i :=
    Finset.single_le_sum (fun i _ => (hk i).le) (Finset.mem_univ i)
  have hr0 : 0 < r := by linarith
  exact hOs r hr x (W i) (hWm i) (fun y => (hWmom i y).of_le (hA i).le hAi hki)
    (flipSumTwo hG hGv i j r x) (measurable_flipSumTwo hG hGv i j r x)
    (by filter_upwards [hWae i] with ω h using h j r hr0 x)

/-- **Dario, Theorem 1, in dimension two.** -/
theorem darioOptimalCorrectorTwo_holds : DarioOptimalCorrectorTwo :=
  darioOptimalCorrectorTwo_of_stepTwo darioStepTwoSumBound_holds

/-- **Dario and Gu, Proposition 2.12, in dimension two.** -/
theorem correctorQuantitativeInputTwo_holds : CorrectorQuantitativeInputTwo :=
  correctorQuantitativeInputTwo_of_stepTwo darioStepTwoSumBound_holds

/-- **Armstrong and Dario, Theorem 2 (iii) at `k = 1`, at the origin, in dimension two.** -/
theorem armstrongDarioOrderOneOriginTwo_holds : ArmstrongDarioOrderOneOriginTwo :=
  armstrongDarioOrderOneOriginTwo_of_stepTwo darioStepTwoSumBound_holds


/-- **Dario and Gu, Theorem 1, in dimension two**, from the inputs `hSec` of Sections 2 and 4 of
Dario and Gu and the Gaussian upper bound of Barlow; the Step 2 sum and the Carne–Varopoulos bound
are proved. -/
theorem darioGuHeatKernelTwo_of_sections_barlow
    (hSec : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuApproxLemmaTwo p σ ∧ DarioGuTwoScaleErrorTwo p σ ∧
        DarioGuDensityGaussianTwo p σ)
    (hBar : BarlowGaussianUpperBoundTwo) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_reduced_stepTwo hSec hBar Rigidity.Green.carneVaropoulosTwo_holds
    darioStepTwoSumBound_holds

/-- **Dario and Gu, Theorem 1, in dimension two**, from Proposition 2.13, Theorem 3 and the
Gaussian upper bound of Barlow; the Step 2 sum is proved. -/
theorem darioGuHeatKernelTwo_of_flux_gradient_barlow
    (hflux : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ)
    (hG3 : DarioGuGradientBoundTwo) (hBar : BarlowGaussianUpperBoundTwo) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_flux_gradient_barlow_stepTwo hflux hG3 hBar darioStepTwoSumBound_holds

end Rigidity.Poincare
