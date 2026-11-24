import Rigidity.Proofs.Cluster.GeneralNablaAffineMoments

/-!
# Display (4.26) of Armstrong and Dario in `L²(P)`: the expectation, in every dimension

With `L = 3^n` the side of a cube `U` of scale `n`, `F`, `M` the sizes at and near the faces of `U`
and `S = ∑_{x ∈ U} size(x)^{d+1}`, the pointwise bound of `GeneralNablaAffineMoments` gives, on the
partition event,

`∑ⱼ (|U|⁻¹ ⟨eⱼ, ∇[v]_𝒫⟩_U - ξⱼ)² ≤ |ξ|₁² (3d (L⁻² + 2d L^{d-1} ∑_{faces} size² / L^{2d}
  + 4 · 9^d d M / L^d) + S / (3L)^{d+1})`

(`sum_sq_cubeNuGradAvg_sub_le`; the last term covers the unresolved cubes). The moments of the
partition sizes bound the expectations of `∑_{faces} size²`, `M` and `S` by `C L^{d-1}`,
`C L^{d-1}` and `C L^d`, whence `E[∑ⱼ (|U|⁻¹ ⟨eⱼ, ∇[v(·, U, ξ)]_𝒫⟩_U - ξⱼ)²] ≤ C |ξ|₁² 3^{-n}`
(`exists_lintegral_cubeNuGradAvg_sub_le`): display (4.26) of Armstrong and Dario in `L²`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The square of the sum of the absolute values bounds the sum of the squares. -/
theorem sum_sq_le_sq_sum_abs_general (ξ : Fin d → ℝ) : ∑ j, ξ j ^ 2 ≤ (∑ i, |ξ i|) ^ 2 := by
  have hle : ∀ j, ξ j ^ 2 ≤ |ξ j| * ∑ i, |ξ i| := fun j => by
    rw [← sq_abs, sq]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun i => |ξ i|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ j)) (abs_nonneg _)
  calc ∑ j, ξ j ^ 2 ≤ ∑ j, |ξ j| * ∑ i, |ξ i| := Finset.sum_le_sum fun j _ => hle j
    _ = (∑ i, |ξ i|) ^ 2 := by rw [← Finset.sum_mul, sq]

/-- **The pointwise majorant of display (4.26)** on the partition event. -/
theorem sum_sq_cubeNuGradAvg_sub_le (hd : 0 < d) (hP : PartitionEvent ω) (U : TriadicCube d)
    (ξ : Fin d → ℝ) :
    ∑ j, (cubeCoarsePairing ω U (Pi.single j 1) (cubeNuSolution ω U ξ) /
        U.latticeVolume - ξ j) ^ 2 ≤
      (∑ i, |ξ i|) ^ 2 * (3 * d * (1 / ((3 : ℝ) ^ U.scale) ^ 2 +
        2 * d * (U.toIntegerCube.size : ℝ) ^ (d - 1) * faceSizeSqSum ω U / U.latticeVolume ^ 2 +
        4 * 9 ^ d * d * marginSizeSum ω U / U.latticeVolume) +
        (∑ x ∈ U.toIntegerCube.vertices,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (d + 1)) /
            (3 * 3 ^ U.scale) ^ (d + 1)) := by
  set Ξ := ∑ i, |ξ i| with hΞ
  have hΞ0 : 0 ≤ Ξ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hVpos := U.latticeVolume_pos
  have hFS0 := faceSizeSqSum_nonneg ω U
  have hM0 := marginSizeSum_nonneg ω U
  have hS0 : 0 ≤ (∑ x ∈ U.toIntegerCube.vertices,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (d + 1)) /
        (3 * 3 ^ U.scale) ^ (d + 1) :=
    div_nonneg (Finset.sum_nonneg fun x _ => pow_nonneg (TriadicCube.stoppingSize_nonneg _ _) _)
      (by positivity)
  set T := 3 * d * (1 / ((3 : ℝ) ^ U.scale) ^ 2 +
    2 * d * (U.toIntegerCube.size : ℝ) ^ (d - 1) * faceSizeSqSum ω U / U.latticeVolume ^ 2 +
    4 * 9 ^ d * d * marginSizeSum ω U / U.latticeVolume) with hT
  have hT0 : 0 ≤ T := by positivity
  by_cases hU : PartitionResolved ω U
  · rw [cubeNuSolution_eq hP hU]
    obtain ⟨hv, hvar⟩ := cubeNuMaximizer_spec (ω := ω) U ξ
    set Y := cubeComparisonError ω U with hY
    have hsum : ∑ j, (cubeCoarsePairing ω U (Pi.single j 1) (cubeNuMaximizer ω U ξ) /
        U.latticeVolume - ξ j) ^ 2 ≤ d * (Ξ * Y) ^ 2 := by
      calc _ ≤ ∑ _j : Fin d, (Ξ * Y) ^ 2 := Finset.sum_le_sum fun j _ => by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _)
              (abs_cubeCoarsePairing_single_div_sub_le hd hP hU ξ hv hvar j) 2
        _ = d * (Ξ * Y) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hF2 := faceSizeSum_sq_le ω U
    have hm : √(d * marginSizeSum ω U / U.latticeVolume) ^ 2 =
        d * marginSizeSum ω U / U.latticeVolume := Real.sq_sqrt (by positivity)
    have h9 : ((3 : ℝ) ^ d) ^ 2 = 9 ^ d := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hYsq : Y ^ 2 ≤ 3 * (1 / ((3 : ℝ) ^ U.scale) ^ 2 +
        2 * d * (U.toIntegerCube.size : ℝ) ^ (d - 1) * faceSizeSqSum ω U / U.latticeVolume ^ 2 +
        4 * 9 ^ d * d * marginSizeSum ω U / U.latticeVolume) := by
      have hYabc : Y = 1 / (3 : ℝ) ^ U.scale + faceSizeSum ω U / U.latticeVolume +
          2 * 3 ^ d * √(d * marginSizeSum ω U / U.latticeVolume) := rfl
      have hb2 : (faceSizeSum ω U / U.latticeVolume) ^ 2 ≤
          2 * d * (U.toIntegerCube.size : ℝ) ^ (d - 1) * faceSizeSqSum ω U /
            U.latticeVolume ^ 2 := by
        rw [div_pow]
        exact div_le_div_of_nonneg_right hF2 (sq_nonneg _)
      have hc2 : (2 * 3 ^ d * √(d * marginSizeSum ω U / U.latticeVolume)) ^ 2 =
          4 * 9 ^ d * d * marginSizeSum ω U / U.latticeVolume := by
        rw [mul_pow, mul_pow, h9, hm]
        ring
      have ha2 : (1 / (3 : ℝ) ^ U.scale) ^ 2 = 1 / ((3 : ℝ) ^ U.scale) ^ 2 := by rw [div_pow, one_pow]
      rw [hYabc]
      nlinarith [sq_nonneg (1 / (3 : ℝ) ^ U.scale - faceSizeSum ω U / U.latticeVolume),
        sq_nonneg (faceSizeSum ω U / U.latticeVolume -
          2 * 3 ^ d * √(d * marginSizeSum ω U / U.latticeVolume)),
        sq_nonneg (1 / (3 : ℝ) ^ U.scale - 2 * 3 ^ d * √(d * marginSizeSum ω U / U.latticeVolume))]
    calc ∑ j, (cubeCoarsePairing ω U (Pi.single j 1) (cubeNuMaximizer ω U ξ) /
          U.latticeVolume - ξ j) ^ 2
        ≤ d * (Ξ * Y) ^ 2 := hsum
      _ = Ξ ^ 2 * (d * Y ^ 2) := by ring
      _ ≤ Ξ ^ 2 * T := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          rw [hT]
          have := mul_le_mul_of_nonneg_left hYsq (Nat.cast_nonneg (α := ℝ) d)
          linarith
      _ ≤ Ξ ^ 2 * (T + (∑ x ∈ U.toIntegerCube.vertices,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (d + 1)) /
              (3 * 3 ^ U.scale) ^ (d + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          linarith
  · have h0 : cubeNuSolution ω U ξ = 0 := by rw [cubeNuSolution, if_neg fun h => hU h.2]
    rw [h0]
    simp only [map_zero, zero_div, zero_sub, neg_sq]
    have h1 := one_le_sum_size_div_of_not_resolved hP hU
    have hSeq : ∑ x ∈ U.toIntegerCube.vertices,
        (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / (3 * 3 ^ U.scale)) ^ (d + 1) =
        (∑ x ∈ U.toIntegerCube.vertices,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (d + 1)) /
            (3 * 3 ^ U.scale) ^ (d + 1) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun x _ => by rw [div_pow]
    rw [hSeq] at h1
    calc ∑ j, ξ j ^ 2 ≤ Ξ ^ 2 := sum_sq_le_sq_sum_abs_general ξ
      _ = Ξ ^ 2 * 1 := (mul_one _).symm
      _ ≤ Ξ ^ 2 * (T + (∑ x ∈ U.toIntegerCube.vertices,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (d + 1)) /
              (3 * 3 ^ U.scale) ^ (d + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          linarith

/-- The expected sum of the squares of the sizes on the faces is at most `C L^{d-1}`. -/
theorem exists_integral_faceSizeSqSum_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : TriadicCube d,
      Integrable (fun ω => faceSizeSqSum ω U) (latticeBondLaw d p) ∧
      ∫ ω, faceSizeSqSum ω U ∂(latticeBondLaw d p) ≤
        C * (U.toIntegerCube.size : ℝ) ^ (d - 1) := by
  obtain ⟨θ, hθ, hmom⟩ := exists_integral_sum_stoppingSize_pow_le hd hpc
  refine ⟨d * (2 * (4 * θ ^ 2)), by positivity, fun U => ?_⟩
  set N : ℝ := (U.toIntegerCube.size : ℝ) ^ (d - 1) with hN
  have hF : ∀ F : Finset (Vertex d), (F.card : ℝ) ≤ N →
      Integrable (fun ω => ∑ x ∈ F, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ 2)
        (latticeBondLaw d p) ∧
      ∫ ω, ∑ x ∈ F, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ 2
        ∂(latticeBondLaw d p) ≤ 4 * θ ^ 2 * N := by
    intro F hFc
    obtain ⟨hi, hb⟩ := hmom 2 F
    refine ⟨hi, hb.trans ?_⟩
    simp only [Nat.factorial_two, Nat.cast_ofNat]
    nlinarith [sq_nonneg θ]
  have hup := fun i => hF _ (by rw [hN]; exact_mod_cast U.toIntegerCube.card_upperFace_le i)
  have hlow := fun i => hF _ (by rw [hN]; exact_mod_cast U.toIntegerCube.card_lowerFace_le i)
  have hsi : ∀ i, Integrable (fun ω => ∑ x ∈ U.toIntegerCube.upperFace i,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ 2 + ∑ x ∈ U.toIntegerCube.lowerFace i,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ 2) (latticeBondLaw d p) := fun i =>
    (hup i).1.add (hlow i).1
  refine ⟨integrable_finsetSum _ fun i _ => hsi i, ?_⟩
  unfold faceSizeSqSum
  rw [integral_finsetSum _ fun i _ => hsi i]
  calc ∑ i : Fin d, ∫ ω, (∑ x ∈ U.toIntegerCube.upperFace i,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ 2 +
        ∑ x ∈ U.toIntegerCube.lowerFace i,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ 2) ∂(latticeBondLaw d p)
      ≤ ∑ _i : Fin d, (4 * θ ^ 2 * N + 4 * θ ^ 2 * N) :=
        Finset.sum_le_sum fun i _ => by
          rw [integral_add (hup i).1 (hlow i).1]
          exact add_le_add (hup i).2 (hlow i).2
    _ = d * (2 * (4 * θ ^ 2)) * N := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The arithmetic of the expectation of display (4.26). -/
theorem nablaAffine_arith {Ξ L C₁ C₂ C₃ : ℝ} {k : ℕ} (hL : 1 ≤ L) (hC₁ : 0 ≤ C₁)
    (hC₃ : 0 ≤ C₃) :
    Ξ ^ 2 * (3 * (k + 1 : ℕ) * (1 / L ^ 2 +
        2 * (k + 1 : ℕ) * L ^ k * (C₁ * L ^ k) / (L ^ (k + 1)) ^ 2 +
        4 * 9 ^ (k + 1) * (k + 1 : ℕ) * (C₂ * L ^ k) / L ^ (k + 1))) +
      Ξ ^ 2 * ((C₃ * L ^ (k + 1)) / (3 * L) ^ (k + 1 + 1)) ≤
      (3 * (k + 1 : ℕ) * (1 + 2 * (k + 1 : ℕ) * C₁ + 4 * 9 ^ (k + 1) * (k + 1 : ℕ) * C₂) + C₃) *
        Ξ ^ 2 / L := by
  have hL0 : 0 < L := by linarith
  set K : ℝ := ((k + 1 : ℕ) : ℝ) with hK
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have e1 : 1 / L ^ 2 ≤ 1 / L := one_div_le_one_div_of_le hL0 (by nlinarith)
  have e2 : 2 * K * L ^ k * (C₁ * L ^ k) / (L ^ (k + 1)) ^ 2 = 2 * K * C₁ / L ^ 2 := by
    field_simp
    ring
  have e2' : 2 * K * C₁ / L ^ 2 ≤ 2 * K * C₁ / L :=
    div_le_div_of_nonneg_left (by positivity) hL0 (by nlinarith)
  have e3 : 4 * 9 ^ (k + 1) * K * (C₂ * L ^ k) / L ^ (k + 1) = 4 * 9 ^ (k + 1) * K * C₂ / L := by
    field_simp
    ring
  have e4 : C₃ * L ^ (k + 1) / (3 * L) ^ (k + 1 + 1) ≤ C₃ / L := by
    rw [div_le_div_iff₀ (by positivity) hL0]
    have h3 : (1 : ℝ) ≤ 3 ^ (k + 1 + 1) := one_le_pow₀ (by norm_num)
    have hp : L ^ (k + 1) * L = L ^ (k + 1 + 1) := (pow_succ L (k + 1)).symm
    have hpos : 0 ≤ C₃ * L ^ (k + 1 + 1) := by positivity
    calc C₃ * L ^ (k + 1) * L = C₃ * L ^ (k + 1 + 1) := by rw [mul_assoc, hp]
      _ ≤ C₃ * L ^ (k + 1 + 1) * 3 ^ (k + 1 + 1) := le_mul_of_one_le_right hpos h3
      _ = C₃ * (3 * L) ^ (k + 1 + 1) := by rw [mul_pow]; ring
  have hsum : 1 / L ^ 2 + 2 * K * L ^ k * (C₁ * L ^ k) / (L ^ (k + 1)) ^ 2 +
      4 * 9 ^ (k + 1) * K * (C₂ * L ^ k) / L ^ (k + 1) ≤
      (1 + 2 * K * C₁ + 4 * 9 ^ (k + 1) * K * C₂) / L := by
    rw [e2, e3]
    have : (1 + 2 * K * C₁ + 4 * 9 ^ (k + 1) * K * C₂) / L =
        1 / L + 2 * K * C₁ / L + 4 * 9 ^ (k + 1) * K * C₂ / L := by ring
    linarith
  have hΞ2 : 0 ≤ Ξ ^ 2 := sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hsum (show 0 ≤ Ξ ^ 2 * (3 * K) by positivity)
  have h2 := mul_le_mul_of_nonneg_left e4 hΞ2
  have e : (3 * K * (1 + 2 * K * C₁ + 4 * 9 ^ (k + 1) * K * C₂) + C₃) * Ξ ^ 2 / L =
      Ξ ^ 2 * (3 * K) * ((1 + 2 * K * C₁ + 4 * 9 ^ (k + 1) * K * C₂) / L) + Ξ ^ 2 * (C₃ / L) := by
    ring
  rw [e]
  nlinarith

/-- **Display (4.26) of Armstrong and Dario in `L²(P)`** (every dimension `d ≥ 2`, `p > p_c(d)`):
`E[∑ⱼ (|U|⁻¹ ⟨eⱼ, ∇[v(·, U, ξ)]_𝒫⟩_U - ξⱼ)²] ≤ C |ξ|₁² 3^{-n}` for every cube `U` of scale `n`. -/
theorem exists_lintegral_cubeNuGradAvg_sub_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube d) (ξ : Fin d → ℝ),
      ∫⁻ ω, ENNReal.ofReal (∑ j, (cubeCoarsePairing ω U (Pi.single j 1) (cubeNuSolution ω U ξ) /
          U.latticeVolume - ξ j) ^ 2) ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal (C * (∑ i, |ξ i|) ^ 2 / 3 ^ U.scale) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C₁, hC₁, hFS⟩ := exists_integral_faceSizeSqSum_le hd hpc
  obtain ⟨C₂, hC₂, hmar⟩ := exists_integral_sum_margin_le hd hpc
  obtain ⟨θ, hθ, hmom⟩ := exists_integral_sum_stoppingSize_pow_le hd hpc
  obtain ⟨k, hk⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  set C₃ : ℝ := 2 * ((d + 1).factorial : ℝ) * θ ^ (d + 1) with hC₃
  have hC₃0 : 0 ≤ C₃ := by positivity
  refine ⟨3 * d * (1 + 2 * d * C₁ + 4 * 9 ^ d * d * C₂) + C₃, by positivity, fun U ξ => ?_⟩
  set μ := latticeBondLaw d p with hμ
  set Ξ := ∑ i, |ξ i| with hΞ
  set L : ℝ := (3 : ℝ) ^ U.scale with hL
  have hL1 : (1 : ℝ) ≤ L := one_le_pow₀ (by norm_num)
  have hsize : (U.toIntegerCube.size : ℝ) = L := U.cast_size_toIntegerCube
  have hvol : U.latticeVolume = L ^ d := by rw [U.latticeVolume_eq_size_pow, hsize]
  set A : ℝ := Ξ ^ 2 * (3 * d * (1 / L ^ 2)) with hA
  set B : ℝ := Ξ ^ 2 * (3 * d * (2 * d * L ^ (d - 1) / (L ^ d) ^ 2)) with hB
  set D : ℝ := Ξ ^ 2 * (3 * d * (4 * 9 ^ d * d / L ^ d)) with hD
  set E : ℝ := Ξ ^ 2 / (3 * L) ^ (d + 1) with hE
  have hB0 : 0 ≤ B := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hE0 : 0 ≤ E := by positivity
  set S : Configuration d → ℝ := fun ω => ∑ x ∈ U.toIntegerCube.vertices,
    TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (d + 1) with hS
  have hGeq : ∀ ω, (∑ i, |ξ i|) ^ 2 * (3 * d * (1 / ((3 : ℝ) ^ U.scale) ^ 2 +
      2 * d * (U.toIntegerCube.size : ℝ) ^ (d - 1) * faceSizeSqSum ω U / U.latticeVolume ^ 2 +
      4 * 9 ^ d * d * marginSizeSum ω U / U.latticeVolume) + S ω / (3 * 3 ^ U.scale) ^ (d + 1)) =
      A + B * faceSizeSqSum ω U + D * marginSizeSum ω U + E * S ω := fun ω => by
    rw [hsize, hvol, ← hL, ← hΞ]
    simp only [hA, hB, hD, hE]
    ring
  have hpoint : ∀ᵐ ω ∂μ, ENNReal.ofReal (∑ j, (cubeCoarsePairing ω U (Pi.single j 1)
      (cubeNuSolution ω U ξ) / U.latticeVolume - ξ j) ^ 2) ≤
      ENNReal.ofReal (A + B * faceSizeSqSum ω U + D * marginSizeSum ω U + E * S ω) := by
    filter_upwards [ae_partitionEvent hd hpc] with ω hPω
    rw [← hGeq ω]
    exact ENNReal.ofReal_le_ofReal (sum_sq_cubeNuGradAvg_sub_le hd0 hPω U ξ)
  obtain ⟨hFSi, hFSb⟩ := hFS U
  obtain ⟨hMi0, hMb⟩ := hmar U
  have hMi : Integrable (fun ω => marginSizeSum ω U) μ := hMi0
  have hSi : Integrable S μ := (hmom (d + 1) U.toIntegerCube.vertices).1
  have hSb : ∫ ω, S ω ∂μ ≤ C₃ * L ^ d := by
    have h := (hmom (d + 1) U.toIntegerCube.vertices).2
    rw [U.card_toIntegerCube_vertices, hvol] at h
    exact h
  have hI1 : Integrable (fun ω => A + B * faceSizeSqSum ω U) μ :=
    (integrable_const A).add (hFSi.const_mul B)
  have hI2 : Integrable (fun ω => A + B * faceSizeSqSum ω U + D * marginSizeSum ω U) μ :=
    hI1.add (hMi.const_mul D)
  have hGi : Integrable (fun ω => A + B * faceSizeSqSum ω U + D * marginSizeSum ω U + E * S ω) μ :=
    hI2.add (hSi.const_mul E)
  have hG0 : ∀ ω, 0 ≤ A + B * faceSizeSqSum ω U + D * marginSizeSum ω U + E * S ω := fun ω => by
    have := faceSizeSqSum_nonneg ω U
    have := marginSizeSum_nonneg ω U
    have : 0 ≤ S ω := Finset.sum_nonneg fun x _ => pow_nonneg (TriadicCube.stoppingSize_nonneg _ _) _
    have : 0 ≤ A := by positivity
    positivity
  have hint : ∫ ω, (A + B * faceSizeSqSum ω U + D * marginSizeSum ω U + E * S ω) ∂μ =
      A + B * ∫ ω, faceSizeSqSum ω U ∂μ + D * ∫ ω, marginSizeSum ω U ∂μ + E * ∫ ω, S ω ∂μ := by
    have e1 := integral_add hI2 (hSi.const_mul E)
    have e2 := integral_add hI1 (hMi.const_mul D)
    have e3 := integral_add (integrable_const A) (hFSi.const_mul B)
    rw [e1, e2, e3]
    simp only [integral_const_mul]
    simp
  have hbound : A + B * ∫ ω, faceSizeSqSum ω U ∂μ + D * ∫ ω, marginSizeSum ω U ∂μ +
      E * ∫ ω, S ω ∂μ ≤ A + B * (C₁ * L ^ (d - 1)) + D * (C₂ * L ^ (d - 1)) + E * (C₃ * L ^ d) := by
    have h1 : ∫ ω, faceSizeSqSum ω U ∂μ ≤ C₁ * L ^ (d - 1) := by rw [← hsize]; exact hFSb
    have h2 : ∫ ω, marginSizeSum ω U ∂μ ≤ C₂ * L ^ (d - 1) := hMb
    have := mul_le_mul_of_nonneg_left h1 hB0
    have := mul_le_mul_of_nonneg_left h2 hD0
    have := mul_le_mul_of_nonneg_left hSb hE0
    linarith
  have harith : A + B * (C₁ * L ^ (d - 1)) + D * (C₂ * L ^ (d - 1)) + E * (C₃ * L ^ d) ≤
      (3 * d * (1 + 2 * d * C₁ + 4 * 9 ^ d * d * C₂) + C₃) * Ξ ^ 2 / L := by
    have h := nablaAffine_arith (Ξ := Ξ) (C₂ := C₂) (k := k) hL1 hC₁ hC₃0
    have hkd : (((k + 1 : ℕ)) : ℝ) = d := by rw [hk]
    rw [hkd] at h
    have hd1 : d - 1 = k := by omega
    have e : A + B * (C₁ * L ^ (d - 1)) + D * (C₂ * L ^ (d - 1)) + E * (C₃ * L ^ d) =
        Ξ ^ 2 * (3 * d * (1 / L ^ 2 + 2 * d * L ^ k * (C₁ * L ^ k) / (L ^ (k + 1)) ^ 2 +
          4 * 9 ^ (k + 1) * d * (C₂ * L ^ k) / L ^ (k + 1))) +
        Ξ ^ 2 * ((C₃ * L ^ (k + 1)) / (3 * L) ^ (k + 1 + 1)) := by
      simp only [hA, hB, hD, hE]
      rw [hd1, hk]
      push_cast
      ring
    rw [e]
    have hd9 : (9 : ℝ) ^ d = 9 ^ (k + 1) := by rw [hk]
    rw [hd9]
    exact h
  calc ∫⁻ ω, ENNReal.ofReal (∑ j, (cubeCoarsePairing ω U (Pi.single j 1)
        (cubeNuSolution ω U ξ) / U.latticeVolume - ξ j) ^ 2) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (A + B * faceSizeSqSum ω U + D * marginSizeSum ω U + E * S ω) ∂μ :=
        lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (∫ ω, (A + B * faceSizeSqSum ω U + D * marginSizeSum ω U + E * S ω) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hGi (ae_of_all _ hG0)).symm
    _ ≤ ENNReal.ofReal ((3 * d * (1 + 2 * d * C₁ + 4 * 9 ^ d * d * C₂) + C₃) * Ξ ^ 2 /
          3 ^ U.scale) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hint]
        exact hbound.trans (harith.trans (le_of_eq (by rw [hL])))

end Rigidity.Percolation
