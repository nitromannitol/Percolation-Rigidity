import Rigidity.Proofs.Cluster.GeneralRestrictMajorant
import Rigidity.Proofs.Partition.PartitionSize
import Rigidity.Proofs.Percolation.GeneralDim.CubeSizeMoments

/-!
# Measurable majorants of the quantity of Lemma 5.5 with second moments, in every dimension

The majorants of `cubeMuRestrictError_le_sizeSum` and `cubeNuRestrictError_le_sizeSum` are
measurable functions of the configuration through the sizes of the partition cubes. With
`S(U) = ∑_{x ∈ U} size(x)^{2d-1}`, `(∑_x a_x)⁴ ≤ |U|³ ∑_x a_x⁴` and the moments of the partition
sizes (`exists_integral_sum_stoppingSize_pow_le`), their second moments are at most
`C |q|⁴ |U|²` (`exists_cubeMuRestrictError_majorant`, `exists_cubeNuRestrictError_majorant`), the
general-dimensional form of `Rigidity.Proofs.Cluster.exists_planarMuRestrictError_majorant`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ}

/-- `(∑ a)⁴ ≤ |s|³ ∑ a⁴`. -/
theorem sum_pow_four_le_card_pow_three_mul {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ s, a i) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, a i ^ 4 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := s) (f := a)
  have h2 := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => a i ^ 2)
  have h0 : 0 ≤ (∑ i ∈ s, a i) ^ 2 := sq_nonneg _
  have hN : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  calc (∑ i ∈ s, a i) ^ 4 = ((∑ i ∈ s, a i) ^ 2) ^ 2 := by ring
    _ ≤ ((s.card : ℝ) * ∑ i ∈ s, a i ^ 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (s.card : ℝ) ^ 2 * (∑ i ∈ s, a i ^ 2) ^ 2 := by ring
    _ ≤ (s.card : ℝ) ^ 2 * ((s.card : ℝ) * ∑ i ∈ s, (a i ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (s.card : ℝ) ^ 3 * ∑ i ∈ s, a i ^ 4 := by
        rw [Finset.sum_congr rfl fun i _ => (pow_mul (a i) 2 2).symm]
        ring

theorem measurable_partitionSizeSum (S : Finset (Vertex d)) (k : ℕ) :
    Measurable fun ω : Configuration d => partitionSizeSum ω S k :=
  Finset.measurable_sum _ fun x _ => (measurable_stoppingSize_goodCubes x).pow_const _

theorem partitionSizeSum_pow_two_le (ω : Configuration d) (S : Finset (Vertex d)) (k : ℕ) :
    partitionSizeSum ω S k ^ 2 ≤ (S.card : ℝ) * partitionSizeSum ω S (2 * k) := by
  have h := sq_sum_le_card_mul_sum_sq (s := S)
    (f := fun z => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ k)
  unfold partitionSizeSum
  refine h.trans (le_of_eq ?_)
  congr 1
  exact Finset.sum_congr rfl fun z _ => by rw [← pow_mul, mul_comm]

theorem partitionSizeSum_pow_four_le (ω : Configuration d) (S : Finset (Vertex d)) (k : ℕ) :
    partitionSizeSum ω S k ^ 4 ≤ (S.card : ℝ) ^ 3 * partitionSizeSum ω S (4 * k) := by
  have h := sum_pow_four_le_card_pow_three_mul S
    (fun z => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ k)
  unfold partitionSizeSum
  refine h.trans (le_of_eq ?_)
  congr 1
  exact Finset.sum_congr rfl fun z _ => by rw [← pow_mul, mul_comm]

/-- **A measurable majorant of the quantity of Lemma 5.5 for `μ` with a second moment**:
`E[M²] ≤ C |q|⁴ |U|²`. -/
theorem exists_cubeMuRestrictError_majorant [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube d) (n : ℕ), n ≤ U.scale → ∀ q : Fin d → ℝ,
      ∃ M : Configuration d → ℝ≥0∞, Measurable M ∧
        (∀ᵐ ω ∂(latticeBondLaw d p), ENNReal.ofReal (cubeMuRestrictError ω U n q) ≤ M ω) ∧
        ∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw d p) ≤
          C * ENNReal.ofReal (∑ i, q i ^ 2) ^ 2 * (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ 2 := by
  have hd0 : 0 < d := by omega
  obtain ⟨θ, hθ, hmom⟩ := exists_integral_sum_stoppingSize_pow_le hd hpc
  set c : ℝ := 16 * d ^ 2 * (d * d * coarseGradConstant d ^ 2) * coarseGradConstant d ^ 2
    with hc
  have hc0 : 0 ≤ c := by positivity
  set τ : ℕ := 4 * (2 * d - 1) with hτ
  set Cτ : ℝ := 2 * (τ.factorial : ℝ) * θ ^ τ with hCτ
  have hCτ0 : 0 ≤ Cτ := by positivity
  refine ⟨ENNReal.ofReal (c ^ 2 * Cτ), ENNReal.ofReal_ne_top, fun U n hn q => ?_⟩
  set P : ℝ := ∑ i, q i ^ 2 with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
  set N : ℝ := (U.toIntegerCube.vertices.card : ℝ) with hN
  have hNvol : N = U.latticeVolume := U.card_toIntegerCube_vertices
  have hN0 : 0 < N := by rw [hNvol]; exact U.latticeVolume_pos
  set M : Configuration d → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (c * P * partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) ^ 2 / U.latticeVolume)
    with hMdef
  refine ⟨M, ?_, ?_, ?_⟩
  · exact ENNReal.measurable_ofReal.comp ((measurable_const.mul
      ((measurable_partitionSizeSum _ _).pow_const 2)).div_const _)
  · filter_upwards [ae_partitionEvent hd hpc] with ω hPω
    exact ENNReal.ofReal_le_ofReal (cubeMuRestrictError_le_sizeSum hd0 hPω hn q)
  · have hint := (hmom τ U.toIntegerCube.vertices).1
    have hint2 := (hmom τ U.toIntegerCube.vertices).2
    have hpt : ∀ ω, M ω ^ 2 ≤ ENNReal.ofReal ((c * P / N) ^ 2 * N ^ 3 *
        ∑ x ∈ U.toIntegerCube.vertices,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ) := by
      intro ω
      rw [hMdef]
      dsimp only
      rw [← ENNReal.ofReal_pow (by
        have := partitionSizeSum_nonneg (ω := ω) U.toIntegerCube.vertices (2 * d - 1)
        have := U.latticeVolume_pos
        positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h4 := partitionSizeSum_pow_four_le ω U.toIntegerCube.vertices (2 * d - 1)
      rw [← hNvol]
      have e : (c * P * partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) ^ 2 / N) ^ 2 =
          (c * P / N) ^ 2 * partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) ^ 4 := by
        ring
      rw [e]
      have hcp : 0 ≤ (c * P / N) ^ 2 := sq_nonneg _
      calc (c * P / N) ^ 2 * partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) ^ 4
          ≤ (c * P / N) ^ 2 * (N ^ 3 * partitionSizeSum ω U.toIntegerCube.vertices
              (4 * (2 * d - 1))) := mul_le_mul_of_nonneg_left h4 hcp
        _ = (c * P / N) ^ 2 * N ^ 3 * ∑ x ∈ U.toIntegerCube.vertices,
              TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ := by
            rw [partitionSizeSum]
            ring
    calc ∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw d p)
        ≤ ∫⁻ ω, ENNReal.ofReal ((c * P / N) ^ 2 * N ^ 3 * ∑ x ∈ U.toIntegerCube.vertices,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ) ∂(latticeBondLaw d p) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (∫ ω, (c * P / N) ^ 2 * N ^ 3 * ∑ x ∈ U.toIntegerCube.vertices,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ ∂(latticeBondLaw d p)) :=
          (ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
            (ae_of_all _ fun ω => mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ =>
              pow_nonneg (TriadicCube.stoppingSize_nonneg _ _) _))).symm
      _ ≤ ENNReal.ofReal ((c * P / N) ^ 2 * N ^ 3 * (Cτ * N)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left hint2 (by positivity)
      _ = ENNReal.ofReal (c ^ 2 * Cτ) * ENNReal.ofReal P ^ 2 *
            (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ 2 := by
          have e : (c * P / N) ^ 2 * N ^ 3 * (Cτ * N) = c ^ 2 * Cτ * P ^ 2 * N ^ 2 := by
            field_simp
          rw [e, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_pow hP0, ENNReal.ofReal_pow hN0.le, hN, ENNReal.ofReal_natCast]

/-- **A measurable majorant of the quantity of Lemma 5.5 for `ν` with a second moment**:
`E[M²] ≤ C |ξ|₁⁴ |U|²`. -/
theorem exists_cubeNuRestrictError_majorant [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube d) (n : ℕ), n ≤ U.scale → ∀ ξ : Fin d → ℝ,
      ∃ M : Configuration d → ℝ≥0∞, Measurable M ∧
        (∀ᵐ ω ∂(latticeBondLaw d p), ENNReal.ofReal (cubeNuRestrictError ω U n ξ) ≤ M ω) ∧
        ∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw d p) ≤
          C * ENNReal.ofReal ((∑ i, |ξ i|) ^ 2) ^ 2 *
            (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ 2 := by
  have hd0 : 0 < d := by omega
  obtain ⟨θ, hθ, hmom⟩ := exists_integral_sum_stoppingSize_pow_le hd hpc
  set c : ℝ := 4 * d ^ 2 * 3 ^ d * coarseGradConstant d ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set τ : ℕ := 2 * (2 * d - 1) with hτ
  set Cτ : ℝ := 2 * (τ.factorial : ℝ) * θ ^ τ with hCτ
  have hCτ0 : 0 ≤ Cτ := by positivity
  refine ⟨ENNReal.ofReal (c ^ 2 * Cτ), ENNReal.ofReal_ne_top, fun U n hn ξ => ?_⟩
  set P : ℝ := (∑ i, |ξ i|) ^ 2 with hP
  have hP0 : 0 ≤ P := sq_nonneg _
  set N : ℝ := (U.toIntegerCube.vertices.card : ℝ) with hN
  have hN0 : 0 < N := by
    rw [hN, U.card_toIntegerCube_vertices]
    exact U.latticeVolume_pos
  set M : Configuration d → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (c * P * partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1)) with hMdef
  refine ⟨M, ?_, ?_, ?_⟩
  · exact ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_partitionSizeSum _ _))
  · filter_upwards [ae_partitionEvent hd hpc] with ω hPω
    exact ENNReal.ofReal_le_ofReal (cubeNuRestrictError_le_sizeSum hd0 hPω hn ξ)
  · have hint := (hmom τ U.toIntegerCube.vertices).1
    have hint2 := (hmom τ U.toIntegerCube.vertices).2
    have hpt : ∀ ω, M ω ^ 2 ≤ ENNReal.ofReal ((c * P) ^ 2 * N *
        ∑ x ∈ U.toIntegerCube.vertices,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ) := by
      intro ω
      rw [hMdef]
      dsimp only
      rw [← ENNReal.ofReal_pow (by
        have := partitionSizeSum_nonneg (ω := ω) U.toIntegerCube.vertices (2 * d - 1)
        positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 := partitionSizeSum_pow_two_le ω U.toIntegerCube.vertices (2 * d - 1)
      have hcp : 0 ≤ (c * P) ^ 2 := sq_nonneg _
      calc (c * P * partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1)) ^ 2
          = (c * P) ^ 2 * partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) ^ 2 := by ring
        _ ≤ (c * P) ^ 2 * (N * partitionSizeSum ω U.toIntegerCube.vertices (2 * (2 * d - 1))) :=
            mul_le_mul_of_nonneg_left h2 hcp
        _ = (c * P) ^ 2 * N * ∑ x ∈ U.toIntegerCube.vertices,
              TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ := by
            rw [partitionSizeSum]
            ring
    calc ∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw d p)
        ≤ ∫⁻ ω, ENNReal.ofReal ((c * P) ^ 2 * N * ∑ x ∈ U.toIntegerCube.vertices,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ) ∂(latticeBondLaw d p) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (∫ ω, (c * P) ^ 2 * N * ∑ x ∈ U.toIntegerCube.vertices,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ τ ∂(latticeBondLaw d p)) :=
          (ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
            (ae_of_all _ fun ω => mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ =>
              pow_nonneg (TriadicCube.stoppingSize_nonneg _ _) _))).symm
      _ ≤ ENNReal.ofReal ((c * P) ^ 2 * N * (Cτ * N)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left hint2 (by positivity)
      _ = ENNReal.ofReal (c ^ 2 * Cτ) * ENNReal.ofReal P ^ 2 *
            (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ 2 := by
          have e : (c * P) ^ 2 * N * (Cτ * N) = c ^ 2 * Cτ * P ^ 2 * N ^ 2 := by ring
          rw [e, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_pow hP0, ENNReal.ofReal_pow hN0.le, hN, ENNReal.ofReal_natCast]

end Rigidity.Percolation
