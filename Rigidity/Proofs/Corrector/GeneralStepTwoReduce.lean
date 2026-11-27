import Rigidity.Proofs.Corrector.GeneralStepTwoSum
import Rigidity.Proofs.Corrector.GeneralStepOneHolds

/-!
# The Step 2 sum of Lemma 3.3 of Dario on `ℤᵈ` through a partition of good cubes

For a partition of `ℤᵈ` into the maximal stopping cubes of the good cubes `stepTwoGood` of the
summation of estimate (2), whose children carry the Meyers estimate and on which the weight `W₂`
is bounded on average, the weighted energy of the bound (4) is summed through the cells
(`tsum_weight_openEnergy_le`), so that (`flipSumTwo_le_of_partition`, as in the planar file
`DarioStepTwoReduce`)

`Σ_e T₂(e)² ≤ Σ_y Φ_{r²}(x, y)² K₀ (W₂(y) + 6d K pathWeight(y))`.

The probabilistic part of Step 2 in dimension `d ≥ 3`, the existence of such a partition almost
surely and a majorant of `W₂ + pathWeight` with moments of polynomial growth uniformly in `y`, is
`DarioStepTwoWeightThree`, proved in `darioStepTwoWeightThree_holds` (in dimension two these are
`exists_stepTwoGood_partition`, `stepTwoWeight_le_weightMajorant`, `pathWeight_le_ballSum` and the
moments of the majorants). From it and Lemma 3.5 for the partition into good cubes,
`isOsBond_heatSqSum_of_moments` gives the bound of the Step 2 sum
(`darioStepTwoSumBoundThree_of_weight`), and with Step 1, Lemma 3.3 in dimension `d ≥ 3`
(`darioVarianceBoundThree_of_weight`).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare.GeneralDim Rigidity.Proofs.Cluster
open scoped Classical ENNReal InnerProductSpace

variable {d : ℕ}

section Good

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- The constant `M^{1/q'} + 3 · 4^d · cellConst(ε, C_M, 3^d M)` of the summation through the
cells. -/
noncomputable def cellSumConst (d : ℕ) (ε CM M : ℝ) : ℝ :=
  M ^ (1 / Real.conjExponent (1 + ε / 2)) + 3 * 4 ^ d * cellConst ε CM (3 ^ d * M)

theorem cellSumConst_nonneg (d : ℕ) {ε CM M : ℝ} (hCM : 0 ≤ CM) (hM : 0 ≤ M) :
    0 ≤ cellSumConst d ε CM M := by
  unfold cellSumConst cellConst
  positivity

/-- **The Step 2 sum through the partition of the good cubes.** -/
theorem flipSumTwo_le_of_partition [NeZero d] (hd : 2 ≤ d) {C₀ C : ℕ} (hC₀ : 0 < C₀)
    (hres : ResamplePartitionBound (d := d) C₀ C)
    {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) {ε CM M : ℝ} (hε : 0 < ε) (hCM : 0 ≤ CM)
    (hM : 0 ≤ M) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (i j : Fin d) (r : ℝ), 0 < r → ∀ (x : Vertex d)
      (hpart : ∀ z : Vertex d, ∃! Q : TriadicCube d, z ∈ Q.vertices ∧
        Q.IsMaximalStopping (stepTwoGood hG hGv (C₀ + 3 * C + 6) i ε CM M ω)),
      flipSumTwo hG hGv i j r x ω ≤ ∑' y, ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2) *
        (ENNReal.ofReal (stepTwoConst d) *
          (stepTwoWeight hG hGv (C₀ + 3 * C + 6) i ω y + 6 * d *
            ENNReal.ofReal (cellSumConst d ε CM M) *
            pathWeight (fun z => (((3 : ℝ) ^ d) ^ partScale hpart z) ^ (1 - 1 / (1 + ε / 2)))
              ω j y)) := by
  filter_upwards [ae_flipSumTwo_le hG hGv hd hC₀ hres hpc hp1 hGae, ae_partitionEvent hd hpc,
    ae_summable_heat_stepRegion hd hpc hp1] with ω hfs hP hS i j r hr x hpart
  have hS' : Summable fun z => zdHeat d (r ^ 2) x z * (stepRegion ω z j).card := by
    have := hS (edgeBond ((0 : Vertex d), (0 : Fin d)))
      (ω (edgeBond ((0 : Vertex d), (0 : Fin d)))) x j r hr
    rwa [setBond_self] at this
  have hfin : ∀ u, stepTwoWeight hG hGv (C₀ + 3 * C + 6) i ω u ≠ ∞ := fun u =>
    (partCell_mem hpart u).2.1 u
      ((TriadicCube.mem_toIntegerCube_vertices _ u).2 (partCell_spec hpart u).1)
  have hMey : ∀ x' z, 1 ≤ partScale hpart x' → z ∈ cube (partScale hpart x') x' →
      GeneralDim.MeyersCube ε CM ω (partScale hpart x' - 1) z := fun x' z h1 hz =>
    (partCell_mem hpart x').1 (partScale hpart x' - 1) (by unfold partScale at h1 ⊢; omega) z
      ((mem_cube_partScale_iff hpart).1 hz)
  have hWM : ∀ x', ∑ u ∈ cube (partScale hpart x') x',
      (stepTwoWeight hG hGv (C₀ + 3 * C + 6) i ω u).toReal ^ Real.conjExponent (1 + ε / 2) ≤
        M * (cube (partScale hpart x') x').card := fun x' => by
    rw [cube_partScale]
    exact (partCell_mem hpart x').2.2
  have hE := tsum_weight_openEnergy_le hP hS' (isCellScale_partScale hpart) hε hCM hM hMey hfin hWM
  refine (hfs i j r hr x hP).trans ?_
  calc ENNReal.ofReal (stepTwoConst d) *
        (∑' u, stepTwoWeight hG hGv (C₀ + 3 * C + 6) i ω u *
            ENNReal.ofReal (openEnergy ω (clusterPot ω (coarseHeatField hP r x j)) u) +
          ∑' y, stepTwoWeight hG hGv (C₀ + 3 * C + 6) i ω y *
            ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2))
      ≤ ENNReal.ofReal (stepTwoConst d) *
        (6 * d * ENNReal.ofReal (cellSumConst d ε CM M) *
          ∑' y, ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2) *
            pathWeight (fun z => (((3 : ℝ) ^ d) ^ partScale hpart z) ^ (1 - 1 / (1 + ε / 2)))
              ω j y +
          ∑' y, stepTwoWeight hG hGv (C₀ + 3 * C + 6) i ω y *
            ENNReal.ofReal (zdHeat d (r ^ 2) x y ^ 2)) := by
        unfold cellSumConst
        gcongr
    _ = _ := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun y => ?_
        ring

end Good

/-- **The probabilistic part of Step 2 of Lemma 3.3 of Dario in dimension `d ≥ 3`**, proved in
`darioStepTwoWeightThree_holds`: for every `κ ≥ 1` there are `ε > 0` and `C_M, M ≥ 0` such that, for each direction
`i`, almost surely the good cubes `stepTwoGood` of the summation of estimate (2) partition `ℤᵈ`
into maximal stopping cubes, and a majorant `W` of `W₂(y) + pathWeight(y)` (the weight of the
Step 2 sum and the path weight of the partition, for every such partition) has moments
`E[W(y)^q] ≤ (A q^k)^q` uniformly in `y`. In dimension two these facts are
`exists_stepTwoGood_partition`, `stepTwoWeight_le_weightMajorant`, `pathWeight_le_ballSum` and
the moments of the majorants. -/
def DarioStepTwoWeightThree : Prop :=
  ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
    (p : ℝ) < 1 → ∀ (G : Set (Configuration d)) (hG : MeasurableSet G)
      (hGv : G ⊆ correctorValidEvent d), (∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) →
      ∀ κ : ℕ, 1 ≤ κ → ∃ ε CM M : ℝ, 0 < ε ∧ 0 ≤ CM ∧ 0 ≤ M ∧ ∀ i : Fin d,
        (∀ᵐ ω ∂latticeBondLaw d p, ∀ x : Vertex d, ∃! Q : TriadicCube d,
          x ∈ Q.vertices ∧ Q.IsMaximalStopping (stepTwoGood hG hGv κ i ε CM M ω)) ∧
        ∃ (W : Vertex d → Configuration d → ℝ≥0∞) (A k : ℝ), 0 < A ∧ 0 < k ∧
          (∀ y, Measurable (W y)) ∧
          (∀ y (q : ℝ), 1 ≤ q →
            ∫⁻ ω, W y ω ^ q ∂latticeBondLaw d p ≤ ENNReal.ofReal ((A * q ^ k) ^ q)) ∧
          ∀ᵐ ω ∂latticeBondLaw d p, ∀ (hpart : ∀ z : Vertex d, ∃! Q : TriadicCube d,
              z ∈ Q.vertices ∧ Q.IsMaximalStopping (stepTwoGood hG hGv κ i ε CM M ω))
            (j : Fin d) (y : Vertex d),
            stepTwoWeight hG hGv κ i ω y +
              pathWeight (fun z => (((3 : ℝ) ^ d) ^ partScale hpart z) ^ (1 - 1 / (1 + ε / 2)))
                ω j y ≤ W y ω

/-- Moments of polynomial growth survive multiplication by a constant. -/
theorem lintegral_const_mul_rpow_le {p : unitInterval} {W : Configuration d → ℝ≥0∞}
    (hW : Measurable W) {c A k q : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A) (hq : 1 ≤ q)
    (h : ∫⁻ ω, W ω ^ q ∂latticeBondLaw d p ≤ ENNReal.ofReal ((A * q ^ k) ^ q)) :
    ∫⁻ ω, (ENNReal.ofReal c * W ω) ^ q ∂latticeBondLaw d p ≤
      ENNReal.ofReal ((c * A * q ^ k) ^ q) := by
  have hq0 : 0 ≤ q := by linarith
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq0]
  rw [lintegral_const_mul _ (hW.pow_const q)]
  calc ENNReal.ofReal c ^ q * ∫⁻ ω, W ω ^ q ∂latticeBondLaw d p
      ≤ ENNReal.ofReal c ^ q * ENNReal.ofReal ((A * q ^ k) ^ q) := mul_le_mul' le_rfl h
    _ = ENNReal.ofReal ((c * A * q ^ k) ^ q) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hc hq0, ← ENNReal.ofReal_mul (by positivity),
          ← Real.mul_rpow hc (by positivity), mul_assoc]

/-- Moments `(A q^k)^q` are monotone in `A` and `k`. -/
theorem rpow_moment_mono {A A' k k' q : ℝ} (hA : 0 ≤ A) (hAA : A ≤ A') (hkk : k ≤ k')
    (hq : 1 ≤ q) : (A * q ^ k) ^ q ≤ (A' * q ^ k') ^ q := by
  have hq0 : 0 ≤ q := by linarith
  have h1 : q ^ k ≤ q ^ k' := Real.rpow_le_rpow_of_exponent_le hq hkk
  exact Real.rpow_le_rpow (by positivity) (mul_le_mul hAA h1 (by positivity) (hA.trans hAA))
    hq0

/-- **The bound of the Step 2 sum of the proof of Lemma 3.3 of Dario in dimension `d ≥ 3`**, from
Lemma 3.5 for the partition into good cubes and the probabilistic part of Step 2. -/
theorem darioStepTwoSumBoundThree_of_weight (h35 : DarioResamplePartitionThree)
    (hW : DarioStepTwoWeightThree) : DarioStepTwoSumBoundThree := by
  intro d _ hd3 p hpc hp1 G hG hGv hGae
  have hd : 2 ≤ d := by omega
  obtain ⟨C₀, C, hC₀, hres⟩ := h35 d hd3
  obtain ⟨ε, CM, M, hε, hCM, hM, hdata⟩ :=
    hW d hd3 p hpc hp1 G hG hGv hGae (C₀ + 3 * C + 6) (by omega)
  have hdata2 := fun i => (hdata i).2
  choose W A k hA hk hWm hWmom hWae using hdata2
  set K : ℝ := stepTwoConst d with hK
  have hK0 : 0 ≤ K := stepTwoConst_nonneg d
  set K' : ℝ := 6 * d * cellSumConst d ε CM M with hK'
  have hK'0 : 0 ≤ K' := by have := cellSumConst_nonneg d (ε := ε) hCM hM; positivity
  set c : ℝ := K * max 1 K' with hc
  have hc0 : 0 ≤ c := mul_nonneg hK0 (le_max_of_le_left zero_le_one)
  set W' : Fin d → Vertex d → Configuration d → ℝ≥0∞ := fun i y ω =>
    ENNReal.ofReal c * W i y ω with hW'
  obtain ⟨s, C', hs, hC', hOs⟩ := isOsBond_heatSqSum_of_moments (d := d) (p := p)
    (A := ∑ i, c * A i + 1) (k := ∑ i, k i)
    (by have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => mul_nonneg hc0 (hA i).le)
        linarith)
    (Finset.sum_pos (fun i _ => hk i) Finset.univ_nonempty)
  refine ⟨s, C', hs, hC', fun i j r hr x => ?_⟩
  have hr0 : 0 < r := by linarith
  have hAi : c * A i ≤ ∑ i, c * A i + 1 := by
    have := Finset.single_le_sum (fun i _ => mul_nonneg hc0 (hA i).le) (Finset.mem_univ i)
    linarith
  have hki : k i ≤ ∑ i, k i := Finset.single_le_sum (fun i _ => (hk i).le) (Finset.mem_univ i)
  refine hOs r hr x (W' i) (fun y => measurable_const.mul (hWm i y)) (fun y q hq => ?_)
    (flipSumTwo hG hGv i j r x) (measurable_flipSumTwo hG hGv i j r x) ?_
  · refine (lintegral_const_mul_rpow_le (hWm i y) hc0 (hA i).le hq (hWmom i y q hq)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact rpow_moment_mono (mul_nonneg hc0 (hA i).le) hAi hki hq
  · filter_upwards [flipSumTwo_le_of_partition hG hGv hd hC₀ hres hpc hp1 hGae hε hCM hM,
      (hdata i).1, hWae i] with ω hfs hpart hWb
    refine (hfs i j r hr0 x hpart).trans (ENNReal.tsum_le_tsum fun y => ?_)
    refine mul_le_mul' le_rfl ?_
    have hm1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 K') := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    have hm2 : (6 * d : ℝ≥0∞) * ENNReal.ofReal (cellSumConst d ε CM M) ≤
        ENNReal.ofReal (max 1 K') := by
      rw [show (6 * d : ℝ≥0∞) = ENNReal.ofReal (6 * d) by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast],
        ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
    have hb := hWb hpart j y
    calc ENNReal.ofReal K * (stepTwoWeight hG hGv (C₀ + 3 * C + 6) i ω y + 6 * d *
          ENNReal.ofReal (cellSumConst d ε CM M) *
          pathWeight (fun z => (((3 : ℝ) ^ d) ^ partScale hpart z) ^ (1 - 1 / (1 + ε / 2)))
            ω j y)
        ≤ ENNReal.ofReal K * (ENNReal.ofReal (max 1 K') *
            (stepTwoWeight hG hGv (C₀ + 3 * C + 6) i ω y +
              pathWeight (fun z => (((3 : ℝ) ^ d) ^ partScale hpart z) ^ (1 - 1 / (1 + ε / 2)))
                ω j y)) := by
          refine mul_le_mul' le_rfl ?_
          rw [mul_add]
          exact add_le_add (le_mul_of_one_le_left bot_le hm1) (mul_le_mul' hm2 le_rfl)
      _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (max 1 K') * W i y ω) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hb)
      _ = ENNReal.ofReal c * W i y ω := by
          rw [hc, ← mul_assoc, ← ENNReal.ofReal_mul hK0]

/-- **Dario, Lemma 3.3 in dimension `d ≥ 3`**, from Lemma 3.5 for the partition into good cubes
and the probabilistic part of Step 2. -/
theorem darioVarianceBoundThree_of_weight (h35 : DarioResamplePartitionThree)
    (hW : DarioStepTwoWeightThree) : DarioVarianceBoundThree :=
  darioVarianceBoundThree_of_resample h35 (darioStepTwoSumBoundThree_of_weight h35 hW)

end Rigidity.Corrector.GeneralDim
