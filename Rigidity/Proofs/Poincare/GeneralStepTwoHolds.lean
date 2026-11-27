import Rigidity.Proofs.Corrector.GeneralStepTwoFinalMoments
import Rigidity.Proofs.Corrector.GeneralStepTwoPartition
import Rigidity.Proofs.Corrector.GeneralVarianceSums

/-!
# The Step 2 sum of Lemma 3.3 of Dario on `ℤᵈ`, from the reduction to a partition

The bound of the Step 2 sum `Σ_e T₂(e)²` of the proof of Lemma 3.3 of Dario in dimension `d ≥ 3`
(`DarioStepTwoSumBoundThree`) follows from two statements on `ℤᵈ` (`StepTwoReduceBound`,
`StepTwoWeightFailure`), by the argument of the planar file `DarioStepTwoHolds`
(`darioStepTwoSumBoundThree_of_reduce_of_weightFailure`):

* `StepTwoReduceBound`: through a partition of `ℤᵈ` into maximal good cubes of the summation of
  estimate (2), `Σ_e T₂(e)² ≤ Σ_y Φ_{r²}(x, y)² K₀ (W₂(y) + K₁ K pathWeight(y))`, with `W₂` the
  weight of the Step 2 sum and `K` the constant of `tsum_weight_openEnergy_le` (the form on `ℤᵈ`
  of the planar `flipSumTwo_le_of_partition`);
* `StepTwoWeightFailure`: the weight bound of a triadic cube fails with stretched exponential
  probability in its side (the form on `ℤᵈ` of the planar `exists_measure_not_weightGood_le`).

Given the failure bound, almost surely the good cubes partition `ℤᵈ`
(`exists_stepTwoGood_partition_of_weightFailure`), and the weight `K₀ (W₂(y) + K₁ K pathWeight(y))`
is at most a variable `W(y)` with moments of polynomial growth uniformly in `y`
(`exists_stepTwo_weight_data_of_weightFailure`): `W₂(y)` is at most the majorant built from the
bound `Λ` of the corrector increments of Step 1 (`stepOne_lipschitz_data`,
`planeGrad_le_of_lipschitz`, `stepTwoWeight_le_weightMajorant`), and the path weight is at most
`(7σ(y))^d` times a sum over the ball of radius `3dσ(y)` of the `d`-th powers of the sizes of the
good cubes times the weighted numbers of anchor regions (`pathWeight_le_ballSum`). Then
`isOsBond_heatSqSum_of_moments` gives `Σ_e T₂(e)² = O_s(C r^{-d})`.

Compared with the planar file, the weight `c(z) = ((3^d)^{n(z)})^{1 - 1/p}` of the cells is bounded
by the `d`-th power `(3^{n(z)})^d` of the size of the good cube (`rpow_three_pow_pow_le_pow`)
instead of its square, and the reduction and the failure bound are hypotheses.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.External
open Rigidity.Poincare.GeneralDim (zdHeat)
open Rigidity.Green.GeneralFlux (GrowthMomentsD)
open scoped Classical ENNReal

variable {d : ℕ}

/-- **The Step 2 sum through a partition into good cubes, on `ℤᵈ`** (the form on `ℤᵈ` of the planar
`flipSumTwo_le_of_partition`, with its constants left existential): almost surely, through every
partition of `ℤᵈ` into maximal good cubes of the summation of estimate (2),
`Σ_e T₂(e)² ≤ Σ_y Φ_{r²}(x, y)² K₀ (W₂(y) + K₁ K pathWeight(y))`. -/
def StepTwoReduceBound : Prop :=
  ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
    (p : ℝ) < 1 → ∀ (G : Set (Configuration d)) (hG : MeasurableSet G)
      (hGv : G ⊆ correctorValidEvent d), (∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) →
      ∃ κ : ℕ, 1 ≤ κ ∧ ∃ K₀ K₁ : ℝ, 0 ≤ K₀ ∧ 0 ≤ K₁ ∧ ∀ ε CM M : ℝ, 0 < ε → 0 ≤ CM → 0 ≤ M →
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ (i j : Fin d) (r : ℝ), 0 < r → ∀ (x : Vertex d)
          (hpart : ∀ z : Vertex d, ∃! Q : TriadicCube d,
            z ∈ Q.vertices ∧ Q.IsMaximalStopping (stepTwoGood hG hGv κ i ε CM M ω)),
          flipSumTwo hG hGv i j r x ω ≤ ∑' y, ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2) *
            (ENNReal.ofReal K₀ * (stepTwoWeight hG hGv κ i ω y + ENNReal.ofReal K₁ *
              ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) +
                3 * 4 ^ d * cellConst ε CM (3 ^ d * M)) *
              pathWeight (fun z => (((3 : ℝ) ^ d) ^ partScale hpart z) ^ (1 - 1 / (1 + ε / 2)))
                ω j y))

/-- **The failure bound of the weight bound on `ℤᵈ`** (the form on `ℤᵈ` of the planar
`exists_measure_not_weightGood_le`): for every `κ ≥ 1` and every exponent `q ≥ 1`, the weight bound
`Σ_T W^q ≤ M |T|` fails on a triadic cube with stretched exponential probability in its side. -/
def StepTwoWeightFailure : Prop :=
  ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
    (p : ℝ) < 1 → ∀ (G : Set (Configuration d)) (hG : MeasurableSet G)
      (hGv : G ⊆ correctorValidEvent d), (∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) →
      ∀ κ : ℕ, 1 ≤ κ → ∀ q : ℝ, 1 ≤ q → WeightFailureBound hG hGv p κ q

/-- The weight of a cell of scale `n` is at most the `d`-th power of its size:
`((3^d)^n)^α ≤ (3^n)^d` for `α ≤ 1`. -/
theorem rpow_three_pow_pow_le_pow {n : ℕ} {α : ℝ} (hα : α ≤ 1) :
    (((3 : ℝ) ^ d) ^ n) ^ α ≤ ((3 : ℝ) ^ n) ^ d := by
  have h1 : (1 : ℝ) ≤ ((3 : ℝ) ^ d) ^ n := one_le_pow₀ (one_le_pow₀ (by norm_num))
  calc (((3 : ℝ) ^ d) ^ n) ^ α ≤ (((3 : ℝ) ^ d) ^ n) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 hα
    _ = ((3 : ℝ) ^ n) ^ d := by rw [Real.rpow_one, ← pow_mul, ← pow_mul, mul_comm]

section Grad

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **The weight of the Step 2 sum on `ℤᵈ`, with moments of polynomial growth**, given the failure
bound of the weight bound: for constants `κ ≥ 1` and `K₀, K₁ ≥ 0` there are `ε, CM, M` such that,
for each direction `i`, almost surely the good cubes partition `ℤᵈ` and, through every such
partition, `K₀ (W₂(y) + K₁ K pathWeight(y)) ≤ W(y)` for a variable `W(y)` with moments
`E[W(y)^q] ≤ (A q^k)^q` uniform in `y`. -/
theorem exists_stepTwo_weight_data_of_weightFailure [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) {κ : ℕ} (hκ : 1 ≤ κ) {K₀ K₁ : ℝ} (hK₀ : 0 ≤ K₀)
    (hK₁ : 0 ≤ K₁) (hw : ∀ q : ℝ, 1 ≤ q → WeightFailureBound hG hGv p κ q) :
    ∃ ε CM M : ℝ, 0 < ε ∧ 0 ≤ CM ∧ 0 ≤ M ∧ ∀ i : Fin d,
      ∃ (W : Vertex d → Configuration d → ℝ≥0∞) (A k : ℝ), 0 < A ∧ 0 < k ∧
        (∀ y, Measurable (W y)) ∧ (∀ y, GrowthMomentsD p (W y) A k) ∧
        ∀ᵐ ω ∂latticeBondLaw d p, (∀ z : Vertex d, ∃! Q : TriadicCube d,
            z ∈ Q.vertices ∧ Q.IsMaximalStopping (stepTwoGood hG hGv κ i ε CM M ω)) ∧
          ∀ (hpart : ∀ z : Vertex d, ∃! Q : TriadicCube d,
              z ∈ Q.vertices ∧ Q.IsMaximalStopping (stepTwoGood hG hGv κ i ε CM M ω))
            (j : Fin d) (y : Vertex d),
            ENNReal.ofReal K₀ * (stepTwoWeight hG hGv κ i ω y + ENNReal.ofReal K₁ *
              ENNReal.ofReal (M ^ (1 / Real.conjExponent (1 + ε / 2)) +
                3 * 4 ^ d * cellConst ε CM (3 ^ d * M)) *
              pathWeight (fun z => (((3 : ℝ) ^ d) ^ partScale hpart z) ^ (1 - 1 / (1 + ε / 2)))
                ω j y) ≤ W y ω := by
  obtain ⟨ε, CM, M, hε, hCM, hM, s0, hs0, hpart⟩ :=
    exists_stepTwoGood_partition_of_weightFailure hG hGv hd hpc hw
  refine ⟨ε, CM, M, hε, hCM, hM, fun i => ?_⟩
  obtain ⟨hae, θ, hθ, hexpτ⟩ := hpart i
  obtain ⟨Λ, BΛ, κΛ, hBΛ, hκΛ, hΛm, hΛ0, hlip, hΛmom⟩ :=
    stepOne_lipschitz_data hG hGv hd hpc hp1 hGae
  have hd0 : 0 < d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  -- the sizes of the good cubes
  have hτm : ∀ z, Measurable fun ω =>
      TriadicCube.stoppingSize (stepTwoGood hG hGv κ i ε CM M ω) z :=
    TriadicCube.measurable_stoppingSize _ (measurableSet_mem_stepTwoGood hG hGv κ i ε CM M)
  have hτd := fun z => growthMoments_pow_of_exp_moment
    (X := fun ω => TriadicCube.stoppingSize (stepTwoGood hG hGv κ i ε CM M ω) z)
    (fun ω => TriadicCube.stoppingSize_nonneg _ z) hθ hs0 (hexpτ z).1 (hexpτ z).2 hd0
  obtain ⟨A0, k0, hA0, hk0, hwm0⟩ := growthMoments_weightMajorant_zero (p := p) hd hpc
  have hwm0m : ∀ z : Vertex d, Measurable (weightMajorant (fun _ _ => 0) (3 * d) (4 * d) z) :=
    fun z => measurable_weightMajorant (fun _ => measurable_const) _ _ z
  set Y : Vertex d → Configuration d → ℝ≥0∞ := fun z ω => ENNReal.ofReal
    (TriadicCube.stoppingSize (stepTwoGood hG hGv κ i ε CM M ω) z ^ d) *
      weightMajorant (fun _ _ => 0) (3 * d) (4 * d) z ω with hYdef
  have hYm : ∀ z, Measurable (Y z) := fun z => ((hτm z).pow_const d).ennreal_ofReal.mul (hwm0m z)
  have hY := fun z => Rigidity.Green.GeneralFlux.GrowthMomentsD.mul
    ((hτm z).pow_const d).ennreal_ofReal.aemeasurable (hwm0m z).aemeasurable (hτd z) (hwm0 z)
    (by positivity) hA0.le
  obtain ⟨BS, kS, hBS, hkS, hS⟩ := growthMoments_ballSum hd hpc (K := 3 * d) (by positivity) hYm
    (by positivity) (by positivity) hY
  obtain ⟨Bσ, kσ, hBσ, hkσ, hσ⟩ := growthMoments_size_pow (p := p) hd hpc
  set S : Vertex d → Configuration d → ℝ≥0∞ := fun y ω => ∑' z,
    if ‖latticeEuclideanEmbedding (z - y)‖ ≤
      3 * d * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y then Y z ω else 0 with hSdef
  have hSm : ∀ y, Measurable (S y) := fun y => Measurable.tsum fun z =>
    Measurable.ite (measurableSet_le measurable_const
      ((measurable_stoppingSize_goodCubes y).const_mul _)) (hYm z) measurable_const
  have hσm : ∀ y : Vertex d, Measurable fun ω =>
      ENNReal.ofReal ((7 * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y) ^ d) := fun y =>
    (((measurable_stoppingSize_goodCubes y).const_mul 7).pow_const d).ennreal_ofReal
  have hP := fun y => Rigidity.Green.GeneralFlux.GrowthMomentsD.mul (hσm y).aemeasurable
    (hSm y).aemeasurable (hσ y) (hS y) hBσ.le hBS.le
  -- the Step 2 weight
  have hΛ' : ∀ z, GrowthMomentsD p (fun ω => ENNReal.ofReal (1 + 2 * d * Λ i z ω))
      (2 * d * BΛ) κΛ := by
    intro z
    have h2 := (show GrowthMomentsD p (fun ω => ENNReal.ofReal (1 + Λ i z ω)) BΛ κΛ from
      fun q hq => hΛmom i z q hq).const_mul (c := 2 * d) (by positivity) hBΛ.le
    refine h2.mono fun ω => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [hΛ0 i z ω])
  have hK : (0 : ℝ) < 3 * d * κ := mul_pos (by positivity) (Nat.cast_pos.2 hκ)
  obtain ⟨AV, kV, hAV, hkV, hV⟩ := growthMoments_weightMajorant hd hpc
    (Λ := fun z ω => 2 * d * Λ i z ω) (fun z => (hΛm i z).const_mul _)
    (by positivity : (0 : ℝ) < 2 * d * BΛ) hκΛ hΛ' hK hK
  have hVm : ∀ y, Measurable (weightMajorant (fun z ω => 2 * d * Λ i z ω)
      (3 * d * κ) (3 * d * κ) y) :=
    fun y => measurable_weightMajorant (fun z => (hΛm i z).const_mul _) _ _ y
  -- the constants
  set Kc : ℝ := M ^ (1 / Real.conjExponent (1 + ε / 2)) +
    3 * 4 ^ d * cellConst ε CM (3 ^ d * M) with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; unfold cellConst; positivity
  set Bm : ℝ := max AV (K₁ * Kc * (Bσ * BS * 2 ^ (kσ + kS))) with hBm
  set km : ℝ := max kV (kσ + kS) with hkm
  have hBm0 : 0 < Bm := lt_max_of_lt_left hAV
  have hkm0 : 0 < km := lt_max_of_lt_left hkV
  have hW1 : ∀ y, GrowthMomentsD p (weightMajorant (fun z ω => 2 * d * Λ i z ω)
      (3 * d * κ) (3 * d * κ) y) Bm km :=
    fun y => (hV y).of_le hAV.le (le_max_left _ _) (le_max_left _ _)
  have hW2 : ∀ y, GrowthMomentsD p (fun ω => ENNReal.ofReal (K₁ * Kc) *
      (ENNReal.ofReal ((7 * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y) ^ d) *
        S y ω)) Bm km :=
    fun y => ((hP y).const_mul (c := K₁ * Kc) (by positivity) (by positivity)).of_le
      (by positivity) (le_max_right _ _) (le_max_right _ _)
  refine ⟨fun y ω => ENNReal.ofReal K₀ * (weightMajorant (fun z ω => 2 * d * Λ i z ω)
      (3 * d * κ) (3 * d * κ) y ω + ENNReal.ofReal (K₁ * Kc) *
        (ENNReal.ofReal ((7 * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y) ^ d) *
          S y ω)),
    (K₀ + 1) * (2 * Bm), km, by positivity, hkm0, fun y => ?_, fun y => ?_, ?_⟩
  · exact measurable_const.mul ((hVm y).add (measurable_const.mul ((hσm y).mul (hSm y))))
  · exact ((Rigidity.Green.GeneralFlux.GrowthMomentsD.add (hVm y).aemeasurable (hW1 y) (hW2 y)
      hBm0.le).const_mul (c := K₀) hK₀ (by positivity)).of_le (by positivity) (by nlinarith)
      le_rfl
  -- the almost sure bound
  filter_upwards [hae, ae_partitionEvent hd hpc, hlip i] with ω hp hPω hl
  refine ⟨hp, fun hpart j y => ?_⟩
  have h1 : stepTwoWeight hG hGv κ i ω y ≤ weightMajorant (fun z ω => 2 * d * Λ i z ω)
      (3 * d * κ) (3 * d * κ) y ω :=
    stepTwoWeight_le_weightMajorant hG hGv (Λ := fun z ω => 2 * d * Λ i z ω) hPω
      (fun z => mul_nonneg (by positivity) (hΛ0 i z ω))
      (fun z => planeGrad_le_of_lipschitz hG hGv (fun z => hΛ0 i z ω) hl z) y
  have hc : ∀ z, ENNReal.ofReal ((((3 : ℝ) ^ d) ^ partScale hpart z) ^ (1 - 1 / (1 + ε / 2))) ≤
      ENNReal.ofReal (TriadicCube.stoppingSize (stepTwoGood hG hGv κ i ε CM M ω) z ^ d) := by
    intro z
    refine ENNReal.ofReal_le_ofReal ?_
    rw [TriadicCube.stoppingSize_eq_of_mem (partCell_spec hpart z).1 (partCell_spec hpart z).2]
    have : 0 ≤ 1 / (1 + ε / 2) := by positivity
    exact rpow_three_pow_pow_le_pow (by linarith)
  have h2 : ENNReal.ofReal K₁ * ENNReal.ofReal Kc *
      pathWeight (fun z => (((3 : ℝ) ^ d) ^ partScale hpart z) ^ (1 - 1 / (1 + ε / 2))) ω j y ≤
      ENNReal.ofReal (K₁ * Kc) *
        (ENNReal.ofReal ((7 * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y) ^ d) *
          S y ω) := by
    rw [ENNReal.ofReal_mul hK₁]
    exact mul_le_mul' le_rfl (pathWeight_le_ballSum hPω hc j y)
  exact mul_le_mul' le_rfl (add_le_add h1 h2)

end Grad

/-- **The Step 2 sum of the proof of Lemma 3.3 of Dario in dimension `d ≥ 3`**, from the reduction
to a partition into good cubes (`StepTwoReduceBound`) and the failure bound of the weight bound
(`StepTwoWeightFailure`): `Σ_e T₂(e)²` is almost surely finite and `O_s(C r^{-d})`. -/
theorem darioStepTwoSumBoundThree_of_reduce_of_weightFailure (hred : StepTwoReduceBound)
    (hw : StepTwoWeightFailure) : DarioStepTwoSumBoundThree := by
  intro d _ hd3 p hpc hp1 G hG hGv hGae
  have hd : 2 ≤ d := by omega
  obtain ⟨κ, hκ, K₀, K₁, hK₀, hK₁, hfs⟩ := hred d hd3 p hpc hp1 G hG hGv hGae
  obtain ⟨ε, CM, M, hε, hCM, hM, hdata⟩ := exists_stepTwo_weight_data_of_weightFailure hG hGv hd
    hpc hp1 hGae hκ hK₀ hK₁ (hw d hd3 p hpc hp1 G hG hGv hGae κ hκ)
  choose W A k hA hk hWm hWmom hWae using hdata
  obtain ⟨s, C, hs, hC, hOs⟩ := isOsBond_heatSqSum_of_moments (d := d) (p := p) (A := ∑ i, A i)
    (k := ∑ i, k i) (Finset.sum_pos (fun i _ => hA i) (Finset.univ_nonempty_iff.2 ⟨0⟩))
    (Finset.sum_pos (fun i _ => hk i) (Finset.univ_nonempty_iff.2 ⟨0⟩))
  refine ⟨s, C, hs, hC, fun i j r hr x => ?_⟩
  have hAi : A i ≤ ∑ i, A i :=
    Finset.single_le_sum (fun i _ => (hA i).le) (Finset.mem_univ i)
  have hki : k i ≤ ∑ i, k i :=
    Finset.single_le_sum (fun i _ => (hk i).le) (Finset.mem_univ i)
  have hr0 : 0 < r := by linarith
  refine hOs r hr x (W i) (hWm i) (fun y => (hWmom i y).of_le (hA i).le hAi hki)
    (flipSumTwo hG hGv i j r x) (measurable_flipSumTwo hG hGv i j r x) ?_
  filter_upwards [hfs ε CM M hε hCM hM, hWae i] with ω hf hWy
  obtain ⟨hp, hle⟩ := hWy
  exact (hf i j r hr0 x hp).trans (ENNReal.tsum_le_tsum fun y => mul_le_mul' le_rfl (hle hp j y))

end Rigidity.Corrector.GeneralDim
