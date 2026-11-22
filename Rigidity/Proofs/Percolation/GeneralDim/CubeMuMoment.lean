import Rigidity.Proofs.Percolation.GeneralDim.CubeNuLowerBound

/-!
# The expectation of `-μ` on resolved triadic cubes of `ℤ^d`

By the upper bound `-μ(U, q) ≤ d C₃² |q|₁² |U|⁻¹ ∑_{z ∈ C_*(U)} s_z^{2d-2}` (Lemma 4.4) and the
moments of the partition sizes, for supercritical bond percolation on `ℤ^d`, `d ≥ 2`,

`E[-μ(U, q); partition event, U resolved] ≤ C |q|₁²`

uniformly in the triadic cube `U` (Armstrong and Dario, (4.16), in expectation).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ}

/-- **Expectation of `-μ`** (Armstrong and Dario, Lemma 4.4 and (4.16), in expectation, in every
dimension `d ≥ 2`). -/
theorem exists_lintegral_neg_cubeMu_le [NeZero d] (hd : 2 ≤ d) {prob : unitInterval}
    (hpc : criticalProbability d < (prob : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube d) (q : Fin d → ℝ),
      ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω U then
          ENNReal.ofReal (-cubeMu ω U q) else 0) ∂(latticeBondLaw d prob) ≤
        ENNReal.ofReal (C * (∑ i, |q i|) ^ 2) := by
  have hd0 : 0 < d := by omega
  obtain ⟨θ, hθ, hmom⟩ := exists_integral_sum_stoppingSize_pow_le hd hpc
  set M := 2 * ((2 * (d - 1)).factorial : ℝ) * θ ^ (2 * (d - 1))
  have hM : 0 ≤ M := by positivity
  refine ⟨d * coarseGradConstant d ^ 2 * M, by positivity, fun U q => ?_⟩
  set μ := latticeBondLaw d prob
  have hvol := U.latticeVolume_pos
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = d * coarseGradConstant d ^ 2 * (∑ i, |q i|) ^ 2 /
      U.latticeVolume := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨f, hf⟩ : ∃ f : Configuration d → ℝ, f = fun ω => ∑ z ∈ U.toIntegerCube.vertices,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) := ⟨_, rfl⟩
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => by
    rw [hf]; exact Finset.sum_nonneg fun z _ => pow_nonneg (stoppingSize_nonneg _ _) _
  have hfi : Integrable f μ := by rw [hf]; exact (hmom (2 * (d - 1)) _).1
  have hfb : ∫ ω, f ω ∂μ ≤ M * U.latticeVolume := by
    rw [hf]
    refine ((hmom (2 * (d - 1)) _).2).trans (le_of_eq ?_)
    rw [U.card_toIntegerCube_vertices]
  have hpoint : ∀ ω, (if PartitionEvent ω ∧ PartitionResolved ω U then
      ENNReal.ofReal (-cubeMu ω U q) else 0) ≤ ENNReal.ofReal (K * f ω) := by
    intro ω
    split_ifs with h
    · apply ENNReal.ofReal_le_ofReal
      have h1 := neg_cubeMu_le hd0 h.1 h.2 q
      have hC1 : ∑ z ∈ crossingClusterVertices ω U, ((3 : ℝ) ^ (partitionCube ω z).scale) ^
          (2 * (d - 1)) ≤ f ω := by
        rw [hf]
        refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun z _ _ => by positivity).trans (le_of_eq (Finset.sum_congr rfl fun z _ => ?_))
        rw [stoppingSize_goodCubes_eq h.1 z]
      have h2 : d * coarseGradConstant d ^ 2 * (∑ i, |q i|) ^ 2 *
          (∑ z ∈ crossingClusterVertices ω U, ((3 : ℝ) ^ (partitionCube ω z).scale) ^
            (2 * (d - 1))) / U.latticeVolume ≤ K * f ω := by
        rw [hK, div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hC1 (by positivity))
          hvol.le
      exact h1.trans h2
    · exact bot_le
  calc ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω U then
        ENNReal.ofReal (-cubeMu ω U q) else 0) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (K * f ω) ∂μ := lintegral_mono hpoint
    _ = ENNReal.ofReal (∫ ω, K * f ω ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal (hfi.const_mul K)
          (ae_of_all _ fun ω => mul_nonneg hK0 (hf0 ω))).symm
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_const_mul]
        have h := mul_le_mul_of_nonneg_left hfb hK0
        have e : K * (M * U.latticeVolume) =
            d * coarseGradConstant d ^ 2 * M * (∑ i, |q i|) ^ 2 := by
          rw [hK]
          field_simp
        linarith only [h, e]

end Rigidity.Percolation
