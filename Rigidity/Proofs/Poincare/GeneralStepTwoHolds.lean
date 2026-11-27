import Rigidity.Proofs.Corrector.GeneralStepTwoFinalMoments
import Rigidity.Proofs.Corrector.GeneralStepTwoPartition

/-!
# The weight of the Step 2 sum of Lemma 3.3 of Dario on `ℤᵈ`, with moments of polynomial growth

For `d ≥ 3` and every `κ ≥ 1` there are `ε, C_M, M` such that, for each direction `i`, almost
surely the good cubes of the summation of estimate (2) partition `ℤᵈ`
(`exists_stepTwoGood_partition`), and through every such partition the weight of the Step 2 sum
plus the path weight, `W₂(y) + pathWeight(y)`, is at most a variable `W(y)` with moments of
polynomial growth uniformly in `y` (`exists_stepTwo_weight_data`): `W₂(y)` is at most the majorant
built from the bound `Λ` of the corrector increments of Step 1 (`stepOne_lipschitz_data`,
`planeGrad_le_of_lipschitz`, `stepTwoWeight_le_weightMajorant`), and the path weight is at most
`(1 + 3^d) σ(y)^d` times a sum over the ball of radius `3dσ(y)` of the `d`-th powers of the sizes of
the good cubes times the weighted numbers of anchor regions (`pathWeight_le_ballSum`).

This is the planar file `DarioStepTwoHolds` on `ℤᵈ`. The weight `c(z) = ((3^d)^{n(z)})^{1 - 1/p}`
of the cells is bounded by the `d`-th power `(3^{n(z)})^d` of the size of the good cube
(`rpow_three_pow_pow_le_pow`) instead of its square.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.External
open Rigidity.Green.GeneralFlux (GrowthMomentsD growthMomentsD_of_exp_moment)
open scoped Classical ENNReal

variable {d : ℕ}

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

/-- **The weight of the Step 2 sum on `ℤᵈ`, with moments of polynomial growth** (`d ≥ 3`): for
`κ ≥ 1` there are `ε, CM, M` such that, for each direction `i`, almost surely the good cubes
partition `ℤᵈ` and, through every such partition, `W₂(y) + pathWeight(y) ≤ W(y)` for a variable
`W(y)` with moments `E[W(y)^q] ≤ (A q^k)^q` uniform in `y`. -/
theorem exists_stepTwo_weight_data [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) {κ : ℕ} (hκ : 1 ≤ κ) :
    ∃ ε CM M : ℝ, 0 < ε ∧ 0 ≤ CM ∧ 0 ≤ M ∧ ∀ i : Fin d,
      (∀ᵐ ω ∂latticeBondLaw d p, ∀ x : Vertex d, ∃! Q : TriadicCube d,
        x ∈ Q.vertices ∧ Q.IsMaximalStopping (stepTwoGood hG hGv κ i ε CM M ω)) ∧
      ∃ (W : Vertex d → Configuration d → ℝ≥0∞) (A k : ℝ), 0 < A ∧ 0 < k ∧
        (∀ y, Measurable (W y)) ∧ (∀ y, GrowthMomentsD p (W y) A k) ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ (hpart : ∀ z : Vertex d, ∃! Q : TriadicCube d,
            z ∈ Q.vertices ∧ Q.IsMaximalStopping (stepTwoGood hG hGv κ i ε CM M ω))
          (j : Fin d) (y : Vertex d),
          stepTwoWeight hG hGv κ i ω y +
            pathWeight (fun z => (((3 : ℝ) ^ d) ^ partScale hpart z) ^ (1 - 1 / (1 + ε / 2)))
              ω j y ≤ W y ω := by
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  obtain ⟨ε, CM, M, hε, hCM, hM, s0, hs0, hpart⟩ :=
    exists_stepTwoGood_partition hG hGv hd hpc hp1 hGae hκ
  refine ⟨ε, CM, M, hε, hCM, hM, fun i => ?_⟩
  obtain ⟨hae, θ, hθ, hexpτ⟩ := hpart i
  refine ⟨hae, ?_⟩
  obtain ⟨Λ, BΛ, κΛ, hBΛ, hκΛ, hΛm, hΛ0, hlip, hΛmom⟩ :=
    stepOne_lipschitz_data hG hGv hd2 hpc hp1 hGae
  -- the sizes of the good cubes
  have hτm : ∀ z, Measurable fun ω =>
      TriadicCube.stoppingSize (stepTwoGood hG hGv κ i ε CM M ω) z :=
    TriadicCube.measurable_stoppingSize _ (measurableSet_mem_stepTwoGood hG hGv κ i ε CM M)
  have hτd : ∀ z, GrowthMomentsD p (fun ω => ENNReal.ofReal
      (TriadicCube.stoppingSize (stepTwoGood hG hGv κ i ε CM M ω) z ^ d))
      ((2 * θ * (1 / s0) ^ (1 / s0)) ^ d * (d : ℝ) ^ ((d : ℝ) * (1 / s0))) ((d : ℝ) * (1 / s0)) :=
    fun z => by
      have h1 := growthMomentsD_of_exp_moment (p := p)
        (X := fun ω => TriadicCube.stoppingSize (stepTwoGood hG hGv κ i ε CM M ω) z)
        (fun ω => TriadicCube.stoppingSize_nonneg _ z) hθ hs0 (hexpτ z).1 (hexpτ z).2
      refine (h1.pow_nat (by positivity) d hd1).mono fun ω => le_of_eq ?_
      rw [ENNReal.ofReal_pow (TriadicCube.stoppingSize_nonneg _ z), ENNReal.rpow_natCast]
  obtain ⟨A0, k0, hA0, hk0, hwm0⟩ := growthMoments_weightMajorant_zero (p := p) hd2 hpc
  have hwm0m : ∀ z : Vertex d, Measurable (weightMajorant (fun _ _ => 0) (3 * d) (4 * d) z) :=
    fun z => measurable_weightMajorant (fun _ => measurable_const) _ _ z
  set Y : Vertex d → Configuration d → ℝ≥0∞ := fun z ω => ENNReal.ofReal
    (TriadicCube.stoppingSize (stepTwoGood hG hGv κ i ε CM M ω) z ^ d) *
      weightMajorant (fun _ _ => 0) (3 * d) (4 * d) z ω
  have hYm : ∀ z, Measurable (Y z) := fun z => ((hτm z).pow_const d).ennreal_ofReal.mul (hwm0m z)
  have hY := fun z => Rigidity.Green.GeneralFlux.GrowthMomentsD.mul
    ((hτm z).pow_const d).ennreal_ofReal.aemeasurable (hwm0m z).aemeasurable (hτd z) (hwm0 z)
    (by positivity) hA0.le
  obtain ⟨BS, kS, hBS, hkS, hS⟩ := growthMoments_ballSum hd2 hpc (K := 3 * d) (by positivity) hYm
    (by positivity) (by positivity) hY
  obtain ⟨Bσ, kσ, hBσ, hkσ, hσ⟩ := growthMoments_size_pow (p := p) hd2 hpc
  set S : Vertex d → Configuration d → ℝ≥0∞ := fun y ω => ∑' z,
    if ‖latticeEuclideanEmbedding (z - y)‖ ≤
      3 * d * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y then Y z ω else 0
  have hSm : ∀ y, Measurable (S y) := fun y => Measurable.tsum fun z =>
    Measurable.ite (measurableSet_le measurable_const
      ((measurable_stoppingSize_goodCubes y).const_mul _)) (hYm z) measurable_const
  have hσm : ∀ y : Vertex d, Measurable fun ω => ENNReal.ofReal
      ((1 + 3 ^ d) * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y ^ d) := fun y =>
    (((measurable_stoppingSize_goodCubes y).pow_const d).const_mul _).ennreal_ofReal
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
    have hd2' : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    exact ENNReal.ofReal_le_ofReal (by nlinarith [hΛ0 i z ω])
  have hK : (0 : ℝ) < 3 * d * κ := mul_pos (by positivity) (Nat.cast_pos.2 hκ)
  obtain ⟨AV, kV, hAV, hkV, hV⟩ := growthMoments_weightMajorant hd2 hpc
    (Λ := fun z ω => 2 * d * Λ i z ω) (fun z => (hΛm i z).const_mul _)
    (by positivity : (0 : ℝ) < 2 * d * BΛ) hκΛ hΛ' hK hK
  have hVm : ∀ y, Measurable (weightMajorant (fun z ω => 2 * d * Λ i z ω)
      (3 * d * κ) (3 * d * κ) y) :=
    fun y => measurable_weightMajorant (fun z => (hΛm i z).const_mul _) _ _ y
  -- the constants
  set Bm : ℝ := max AV (Bσ * BS * 2 ^ (kσ + kS))
  set km : ℝ := max kV (kσ + kS)
  have hBm0 : 0 < Bm := lt_max_of_lt_left hAV
  have hkm0 : 0 < km := lt_max_of_lt_left hkV
  have hW1 : ∀ y, GrowthMomentsD p (weightMajorant (fun z ω => 2 * d * Λ i z ω)
      (3 * d * κ) (3 * d * κ) y) Bm km :=
    fun y => (hV y).of_le hAV.le (le_max_left _ _) (le_max_left _ _)
  have hW2 : ∀ y, GrowthMomentsD p (fun ω => ENNReal.ofReal
      ((1 + 3 ^ d) * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y ^ d) * S y ω) Bm km :=
    fun y => (hP y).of_le (by positivity) (le_max_right _ _) (le_max_right _ _)
  refine ⟨fun y ω => weightMajorant (fun z ω => 2 * d * Λ i z ω) (3 * d * κ) (3 * d * κ) y ω +
      ENNReal.ofReal ((1 + 3 ^ d) * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y ^ d) *
        S y ω,
    2 * Bm, km, by positivity, hkm0, fun y => (hVm y).add ((hσm y).mul (hSm y)),
    fun y => Rigidity.Green.GeneralFlux.GrowthMomentsD.add (hVm y).aemeasurable (hW1 y) (hW2 y)
      hBm0.le, ?_⟩
  -- the almost sure bound
  filter_upwards [ae_partitionEvent hd2 hpc, hlip i] with ω hPω hl
  intro hpart j y
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
  exact add_le_add h1 (pathWeight_le_ballSum hPω hc j y)

end Grad

end Rigidity.Corrector.GeneralDim
