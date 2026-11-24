import Rigidity.Proofs.Cluster.GeneralCoarseEnergyMoments
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuDirichlet
import Rigidity.Proofs.Percolation.GeneralDim.CubeMuNuComparison
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuLowerBound

/-!
# Display (4.26) of Armstrong and Dario in `L²(P)`, in every dimension

For a resolved cube `U` of side `L` on the partition event, the maximizer `v` of `ν(U, ξ)` is affine
of slope `ξ` on the vertices of `𝒞_*(U)` which are not lattice-interior points of `U`, so the
spatial average of its coarsened gradient differs from `ξ` by the boundary error
(`abs_cubeCoarsePairing_sub_le`, the proof of Lemma 4.5); the boundary error is at most
`|ξ|₁ (F + 2 · 3^d (d M / |U|)^{1/2} |U|)`, `F` and `M` the sizes of the partition cubes at and near
the faces of `U` (`cubeBoundaryError_le_comparison`, as in the comparison (4.29)). Hence
`| |U|⁻¹ ⟨eⱼ, ∇[v]_𝒫⟩_U - ξⱼ | ≤ |ξ|₁ Y(U)` with the comparison error `Y` of Corollary 4.6
(`abs_cubeCoarsePairing_single_div_sub_le`). Off the partition event or for an unresolved cube the
solution vanishes, and on the partition event some vertex of `U` then has a partition cube of side
at least `3L`. The moments of the partition sizes give

`E[∑ⱼ (|U|⁻¹ ⟨eⱼ, ∇[v(·, U, ξ)]_𝒫⟩_U - ξⱼ)²] ≤ C |ξ|₁² 3^{-n}`

for every cube `U` of scale `n`: display (4.26) of Armstrong and Dario in `L²`, in every dimension
`d ≥ 2`, as the two-dimensional `Rigidity.Percolation.exists_lintegral_planarNuGradAvg_sub_le`.
This file proves the pointwise ingredients; the face sizes enter through
`F² ≤ 2d L^{d-1} ∑_{faces} size²` (`faceSizeSum_sq_le`).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- **The boundary error of a maximizer of `ν`** (the proof of Corollary 4.6): for a function `v`
satisfying the first variation of `ν(U, ξ)` on a resolved cube,
`E(v) ≤ |ξ|₁ (F + 2 · 3^d (d M / |U|)^{1/2} |U|)`. -/
theorem cubeBoundaryError_le_comparison (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (ξ : Fin d → ℝ) {v : CubeFun ω U}
    (hv : v ∈ cubeHarmonic ω U)
    (hvar : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w v = cubeFluxPairing ω U ξ w) :
    cubeBoundaryError ω U ξ v ≤ (∑ i, |ξ i|) * (faceSizeSum ω U +
      2 * 3 ^ d * √(d * marginSizeSum ω U / U.latticeVolume) * U.latticeVolume) := by
  set Ξ := ∑ i, |ξ i| with hΞ
  set V := U.latticeVolume with hV
  set F := faceSizeSum ω U with hF
  set M := marginSizeSum ω U with hM
  have hV0 : 0 < V := U.latticeVolume_pos
  have hΞ0 : 0 ≤ Ξ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM0 : 0 ≤ M := marginSizeSum_nonneg ω U
  set E := cubeBoundaryError ω U ξ v with hE
  set B := cubeForm ω U v v with hB
  set W := ∑ z ∈ crossingClusterVertices ω U, cubeBoundaryWeight ω U z ^ 2 with hW
  have hface : ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i, Ξ * 3 ^ (partitionCube ω x).scale +
      ∑ x ∈ U.toIntegerCube.lowerFace i, Ξ * 3 ^ (partitionCube ω x).scale) = Ξ * F := by
    rw [hF]
    unfold faceSizeSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun x _ => by rw [stoppingSize_goodCubes_eq hP x]
  have h3 : W ≤ 4 * d * M := by
    calc W ≤ ∑ z ∈ U.toIntegerCube.vertices, cubeBoundaryWeight ω U z ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => sq_nonneg _
      _ ≤ ∑ z ∈ U.toIntegerCube.vertices, 4 * d * ∑ i : Fin d,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
              (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
                then 1 else 0) :=
          Finset.sum_le_sum fun z _ => cubeBoundaryWeight_sq_le hP U z
      _ = 4 * d * M := by rw [hM, marginSizeSum, Finset.mul_sum]
  have h4 : B ≤ 2 * V * (3 ^ d / 4 * Ξ ^ 2) := by
    have hBF := hvar v hv
    have hle := le_cubeNu (ω := ω) (U := U) ξ hv
    have hν := cubeNu_le (ω := ω) (U := U) ξ
    rw [← hBF] at hle
    have : B / 2 / V ≤ 3 ^ d / 4 * Ξ ^ 2 := by
      have e : (B - B / 2) / V = B / 2 / V := by ring
      rw [e] at hle
      exact hle.trans hν
    rw [div_le_iff₀ hV0] at this
    linarith
  have hτ : ∀ τ : ℝ, 0 < τ → E - Ξ * F ≤
      √(3 ^ d * 2 * d * M) ^ 2 / τ + (Ξ * √(3 ^ d * V / 2)) ^ 2 * τ := by
    intro τ hτ
    have h2 := cubeBoundaryError_le hd hP hU ξ v hτ
    rw [hface] at h2
    rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
    have a : 3 ^ d * W / τ ≤ 3 ^ d * (4 * d * M) / τ := by gcongr
    have b : τ * (2 * B) ≤ τ * (2 * (2 * V * (3 ^ d / 4 * Ξ ^ 2))) := by gcongr
    have e1 : (3 ^ d * (4 * d * M) / τ + τ * (2 * (2 * V * (3 ^ d / 4 * Ξ ^ 2)))) / 2 =
        3 ^ d * 2 * d * M / τ + Ξ ^ 2 * (3 ^ d * V / 2) * τ := by
      field_simp
      ring
    linarith
  have hEF := le_two_mul_of_forall_le_div_add_mul (Real.sqrt_nonneg _)
    (mul_nonneg hΞ0 (Real.sqrt_nonneg _)) hτ
  have hsq : √(3 ^ d * 2 * d * M) * √(3 ^ d * V / 2) = 3 ^ d * √(d * M / V) * V := by
    rw [← Real.sqrt_mul (by positivity)]
    have : 3 ^ d * 2 * d * M * (3 ^ d * V / 2) = (3 ^ d * V) ^ 2 * (d * M / V) := by
      field_simp
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    ring
  have e : 2 * √(3 ^ d * 2 * d * M) * (Ξ * √(3 ^ d * V / 2)) =
      2 * Ξ * (√(3 ^ d * 2 * d * M) * √(3 ^ d * V / 2)) := by ring
  rw [e, hsq] at hEF
  nlinarith

/-- **The spatial average of the coarsened gradient of a maximizer of `ν`** (display (4.26),
pointwise): `| |U|⁻¹ ⟨eⱼ, ∇[v]_𝒫⟩_U - ξⱼ | ≤ |ξ|₁ Y(U)`. -/
theorem abs_cubeCoarsePairing_single_div_sub_le (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (ξ : Fin d → ℝ) {v : CubeFun ω U}
    (hv : v ∈ cubeHarmonic ω U)
    (hvar : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w v = cubeFluxPairing ω U ξ w) (j : Fin d) :
    |cubeCoarsePairing ω U (Pi.single j 1) v / U.latticeVolume - ξ j| ≤
      (∑ i, |ξ i|) * cubeComparisonError ω U := by
  obtain ⟨c, hc⟩ := exists_affine_boundary_of_cubeNu_variation hd hP hU ξ hvar
  have h := abs_cubeCoarsePairing_sub_le hd hP hU ξ (Pi.single j 1) hc
  have hE := cubeBoundaryError_le_comparison hd hP hU ξ hv hvar
  set Ξ := ∑ i, |ξ i| with hΞ
  set V := U.latticeVolume with hV
  have hV0 : 0 < V := U.latticeVolume_pos
  set L : ℝ := (U.toIntegerCube.size : ℝ) with hL
  have hL3 : L = (3 : ℝ) ^ U.scale := U.cast_size_toIntegerCube
  have hL1 : (1 : ℝ) ≤ L := by rw [hL3]; exact one_le_pow₀ (by norm_num)
  have hVL : V = L ^ d := U.latticeVolume_eq_size_pow
  have hs1 : ∑ i, (Pi.single j 1 : Fin d → ℝ) i * ξ i = ξ j := by
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    simp
  have ha1 : ∑ i, |(Pi.single j 1 : Fin d → ℝ) i| = 1 := by
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    simp
  rw [hs1, ha1, one_mul] at h
  have hΞ0 : 0 ≤ Ξ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hξj : |ξ j| ≤ Ξ :=
    Finset.single_le_sum (f := fun i => |ξ i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  have hLd : L ^ (d - 1) * (L - 1) = V * (1 - 1 / L) := by
    rw [hVL]
    have hL0 : L ≠ 0 := by linarith
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  rw [hLd] at h
  have h2 : |cubeCoarsePairing ω U (Pi.single j 1) v / V - ξ j * (1 - 1 / L)| ≤
      cubeBoundaryError ω U ξ v / V := by
    rw [show cubeCoarsePairing ω U (Pi.single j 1) v / V - ξ j * (1 - 1 / L) =
      (cubeCoarsePairing ω U (Pi.single j 1) v - ξ j * (V * (1 - 1 / L))) / V by
        field_simp, abs_div, abs_of_pos hV0]
    exact div_le_div_of_nonneg_right h hV0.le
  have h3 : cubeBoundaryError ω U ξ v / V ≤
      Ξ * (faceSizeSum ω U / V + 2 * 3 ^ d * √(d * marginSizeSum ω U / V)) := by
    rw [div_le_iff₀ hV0]
    calc cubeBoundaryError ω U ξ v ≤ Ξ * (faceSizeSum ω U +
          2 * 3 ^ d * √(d * marginSizeSum ω U / V) * V) := hE
      _ = Ξ * (faceSizeSum ω U / V + 2 * 3 ^ d * √(d * marginSizeSum ω U / V)) * V := by
          field_simp
  have h4 : |ξ j * (1 / L)| ≤ Ξ * (1 / (3 : ℝ) ^ U.scale) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / L), ← hL3]
    exact mul_le_mul_of_nonneg_right hξj (by positivity)
  have e : cubeCoarsePairing ω U (Pi.single j 1) v / V - ξ j =
      (cubeCoarsePairing ω U (Pi.single j 1) v / V - ξ j * (1 - 1 / L)) - ξ j * (1 / L) := by
    ring
  rw [e]
  calc |(cubeCoarsePairing ω U (Pi.single j 1) v / V - ξ j * (1 - 1 / L)) - ξ j * (1 / L)|
      ≤ |cubeCoarsePairing ω U (Pi.single j 1) v / V - ξ j * (1 - 1 / L)| + |ξ j * (1 / L)| :=
        abs_sub _ _
    _ ≤ Ξ * (faceSizeSum ω U / V + 2 * 3 ^ d * √(d * marginSizeSum ω U / V)) +
          Ξ * (1 / (3 : ℝ) ^ U.scale) := add_le_add (h2.trans h3) h4
    _ = Ξ * cubeComparisonError ω U := by
        unfold cubeComparisonError
        ring

/-- On the partition event, an unresolved cube has a vertex whose partition cube has side at least
three times its own: `1 ≤ ∑_{x ∈ U} (size(x) / 3L)^{d+1}`. -/
theorem one_le_sum_size_div_of_not_resolved (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : ¬ PartitionResolved ω U) :
    1 ≤ ∑ x ∈ U.toIntegerCube.vertices,
      (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / (3 * 3 ^ U.scale)) ^ (d + 1) := by
  unfold PartitionResolved at hU
  push Not at hU
  obtain ⟨z, hz, hzs⟩ := hU
  have hzV : z ∈ U.toIntegerCube.vertices := (U.mem_toIntegerCube_vertices z).2 hz
  have h1 : (1 : ℝ) ≤ TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z / (3 * 3 ^ U.scale) := by
    rw [stoppingSize_goodCubes_eq hP z, le_div_iff₀ (by positivity), one_mul,
      show (3 : ℝ) * 3 ^ U.scale = 3 ^ (U.scale + 1) by ring]
    exact pow_le_pow_right₀ (by norm_num) hzs
  calc (1 : ℝ) ≤ (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z /
        (3 * 3 ^ U.scale)) ^ (d + 1) := one_le_pow₀ h1
    _ ≤ _ := Finset.single_le_sum (f := fun x =>
        (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / (3 * 3 ^ U.scale)) ^ (d + 1))
        (fun x _ => pow_nonneg (div_nonneg (TriadicCube.stoppingSize_nonneg _ _)
          (by positivity)) _) hzV

/-- The sum of the squares of the partition sizes on the faces of a cube. -/
noncomputable def faceSizeSqSum (ω : Configuration d) (U : TriadicCube d) : ℝ :=
  ∑ i : Fin d, (∑ x ∈ U.toIntegerCube.upperFace i,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ 2 +
    ∑ x ∈ U.toIntegerCube.lowerFace i, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ 2)

theorem faceSizeSqSum_nonneg (ω : Configuration d) (U : TriadicCube d) :
    0 ≤ faceSizeSqSum ω U :=
  Finset.sum_nonneg fun _ _ => add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- `F² ≤ 2d L^{d-1} ∑_{faces} size²` by the Cauchy–Schwarz inequality. -/
theorem faceSizeSum_sq_le (ω : Configuration d) (U : TriadicCube d) :
    faceSizeSum ω U ^ 2 ≤
      2 * d * (U.toIntegerCube.size : ℝ) ^ (d - 1) * faceSizeSqSum ω U := by
  set A : Fin d → ℝ := fun i => ∑ x ∈ U.toIntegerCube.upperFace i,
    TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x with hA
  set B : Fin d → ℝ := fun i => ∑ x ∈ U.toIntegerCube.lowerFace i,
    TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x with hB
  set N : ℝ := (U.toIntegerCube.size : ℝ) ^ (d - 1) with hN
  have hcs : ∀ (S : Finset (Vertex d)), (S.card : ℝ) ≤ N →
      (∑ x ∈ S, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x) ^ 2 ≤
        N * ∑ x ∈ S, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ 2 := by
    intro S hS
    refine (sq_sum_le_card_mul_sum_sq (s := S)
      (f := fun x => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x)).trans ?_
    exact mul_le_mul_of_nonneg_right hS (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hup : ∀ i, (A i) ^ 2 ≤ N * ∑ x ∈ U.toIntegerCube.upperFace i,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ 2 := fun i =>
    hcs _ (by rw [hN]; exact_mod_cast U.toIntegerCube.card_upperFace_le i)
  have hlow : ∀ i, (B i) ^ 2 ≤ N * ∑ x ∈ U.toIntegerCube.lowerFace i,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ 2 := fun i =>
    hcs _ (by rw [hN]; exact_mod_cast U.toIntegerCube.card_lowerFace_le i)
  have h1 : faceSizeSum ω U ^ 2 ≤ d * ∑ i, (A i + B i) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => A i + B i)
    simpa [faceSizeSum, Finset.card_univ, Fintype.card_fin] using this
  have h2 : ∀ i, (A i + B i) ^ 2 ≤ 2 * (A i ^ 2 + B i ^ 2) := fun i => by
    nlinarith [sq_nonneg (A i - B i)]
  calc faceSizeSum ω U ^ 2 ≤ d * ∑ i, (A i + B i) ^ 2 := h1
    _ ≤ d * ∑ i, 2 * (N * ∑ x ∈ U.toIntegerCube.upperFace i,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ 2 +
        N * ∑ x ∈ U.toIntegerCube.lowerFace i,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _)
        have := h2 i
        have := hup i
        have := hlow i
        linarith
    _ = 2 * d * N * faceSizeSqSum ω U := by
        rw [faceSizeSqSum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

end Rigidity.Percolation
