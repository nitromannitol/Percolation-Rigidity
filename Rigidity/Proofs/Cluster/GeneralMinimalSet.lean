import Rigidity.Proofs.Cluster.GeneralSlopeQuadratic
import Rigidity.Proofs.Cluster.GeneralMuDuality

/-!
# Lemma 5.3 of Armstrong and Dario in every dimension

For a triadic cube `U` of `ℤᵈ`, let `ω(U, q) = ν(U, ā⁻¹ q) - μ(U, q) - q · ā⁻¹ q` (`cubeOmega`, with
`ν` and `μ` replaced by `0` off the event that the partition exists and resolves `U`, as in
dimension two) and `ρ(U) = sup_q |q|⁻² ω(U, q)₊` (`cubeRho`). Lemma 5.3 of Armstrong and Dario
(display (5.6)) bounds `|μ(U, q) + (1/2) q · ā⁻¹ q|` and `|ν(U, ā⁻¹ q) - (1/2) q · ā⁻¹ q|` by
`C |q|² ρ(U)^{1/2}` plus random errors of size `size(U)^{-1/4}`.

Here (`cube_minimalset`), on the partition event and for a resolved cube, with

* `Y(U) = 3^{-n} + |U|⁻¹ ∑_{x ∈ ∂U} size(□_𝒫(x)) + 2 · 3ᵈ (d |U|⁻¹ ∑_{z near ∂U} size^{2d-2})^{1/2}`
  the error of the comparison `q · ξ ≤ -μ(U, q) + ν(U, ξ) + |q|₁ |ξ|₁ Y(U)` (Corollary 4.6,
  display (4.29); `sum_mul_le_neg_cubeMu_add_cubeNu_add_mul`),
* `Λ(U) = d² C₃² |U|⁻¹ ∑_{z ∈ U} size^{2d-2}` the bound `-μ(U, q) ≤ Λ(U) |q|²` of Lemma 4.4, and
* `S` an `ℓ¹` operator bound of `ā⁻¹` (for instance `∑_{i,j} |(ā⁻¹)ᵢⱼ|`, `sum_abs_mulVec_le`),

`|μ(U, q) + (1/2) q · ā⁻¹ q| ≤ (d/2) (2 d Y S + √(4 d (Λ + 1) (ρ(U) + Y S))) |q|²` and
`|ν(U, ā⁻¹ q) - (1/2) q · ā⁻¹ q| ≤ (ρ(U) + d Y S + (d/2) (2 d Y S + √(4 d (Λ + 1) (ρ(U) + Y S)))) |q|²`.

The comparison is Corollary 4.6 with Young's parameter chosen for each slope `ξ`
(`le_two_mul_of_forall_le_div_add_mul`), so that the error is proportional to `|q|₁ |ξ|₁` as in
display (4.29), and `Y(U)` is of order `size(U)^{-1/2}`. As in dimension two, the factor
`√(Λ(U) + 1)` of `ρ(U)^{1/2}` is random, and the tails of `Y(U)` and `Λ(U)` are not part of the
statement.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal Classical Matrix

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The coarse pairing is linear in the slope: `ℓ_q = ∑_i qᵢ ℓ_{eᵢ}`. -/
theorem cubeCoarsePairing_eq_sum_single {U : TriadicCube d} (q : Fin d → ℝ) (w : CubeFun ω U) :
    cubeCoarsePairing ω U q w = ∑ i, q i * cubeCoarsePairing ω U (Pi.single i 1) w := by
  let F : (Fin d → ℝ) →+ ℝ :=
    { toFun := fun r => cubeCoarsePairing ω U r w
      map_zero' := by
        have h := cubeCoarsePairing_smul_add_smul (ω := ω) (U := U) (0 : Fin d → ℝ) 0 0 0 w
        simp only [smul_zero, add_zero, zero_mul] at h
        exact h
      map_add' := fun r s => by
        have h := cubeCoarsePairing_smul_add_smul (ω := ω) (U := U) r s 1 1 w
        simpa only [one_smul, one_mul] using h }
  have hq : q = ∑ i, q i • (Pi.single i 1 : Fin d → ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : cubeCoarsePairing ω U q w = F (∑ i, q i • (Pi.single i 1 : Fin d → ℝ)) := by
    change cubeCoarsePairing ω U q w = cubeCoarsePairing ω U (∑ i, q i • Pi.single i 1) w
    rw [← hq]
  rw [h1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := cubeCoarsePairing_smul_add_smul (ω := ω) (U := U) (Pi.single i 1) 0 (q i) 0 w
  simp only [smul_zero, add_zero, zero_mul] at h
  exact h

/-- **Polarization of `μ`.** On the partition event and for a resolved cube, `μ(U, ·)` is the
quadratic form `μ(U, q) = (1/2) ∑_{i,j} qᵢ qⱼ (μ(U, eᵢ + eⱼ) - μ(U, eᵢ) - μ(U, eⱼ))`. -/
theorem cubeMu_eq_sum_polarization (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (q : Fin d → ℝ) :
    cubeMu ω U q = 1 / 2 * ∑ i, ∑ j, q i * q j *
      (cubeMu ω U (Pi.single i 1 + Pi.single j 1) - cubeMu ω U (Pi.single i 1) -
        cubeMu ω U (Pi.single j 1)) := by
  have hex : ∀ i : Fin d, ∃ u ∈ cubeHarmonic ω U, ∀ w ∈ cubeHarmonic ω U,
      cubeForm ω U w u = cubeCoarsePairing ω U (Pi.single i 1) w := fun i => by
    obtain ⟨u, hu, hvar, -⟩ := exists_cubeMu_minimizer hd hP hU (Pi.single i 1)
    exact ⟨u, hu, hvar⟩
  choose u hu hvar using hex
  have hvol := U.latticeVolume_pos
  have hq : cubeMu ω U q = -(cubeForm ω U (∑ i, q i • u i) (∑ i, q i • u i) / 2) /
      U.latticeVolume := by
    refine cubeMu_eq_of_forall_cubeForm_eq hd hP hU
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hu i)) fun w hw => ?_
    rw [map_sum, cubeCoarsePairing_eq_sum_single]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, hvar i w hw]
  have hpair : ∀ i j, cubeMu ω U (Pi.single i 1 + Pi.single j 1) =
      -(cubeForm ω U (u i + u j) (u i + u j) / 2) / U.latticeVolume := by
    intro i j
    refine cubeMu_eq_of_forall_cubeForm_eq hd hP hU (Submodule.add_mem _ (hu i) (hu j))
      fun w hw => ?_
    rw [map_add, hvar i w hw, hvar j w hw]
    have h := cubeCoarsePairing_smul_add_smul (ω := ω) (U := U) (Pi.single i 1) (Pi.single j 1)
      1 1 w
    simp only [one_smul, one_mul] at h
    rw [h]
  have hone : ∀ i, cubeMu ω U (Pi.single i 1) =
      -(cubeForm ω U (u i) (u i) / 2) / U.latticeVolume :=
    fun i => cubeMu_eq_of_forall_cubeForm_eq hd hP hU (hu i) (hvar i)
  have hexp : cubeForm ω U (∑ i, q i • u i) (∑ i, q i • u i) =
      ∑ i, ∑ j, q i * q j * cubeForm ω U (u i) (u j) := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [cubeForm_symm (u j) (u i)]
    ring
  have hBij : ∀ i j, cubeMu ω U (Pi.single i 1 + Pi.single j 1) - cubeMu ω U (Pi.single i 1) -
      cubeMu ω U (Pi.single j 1) = -(cubeForm ω U (u i) (u j) / U.latticeVolume) := by
    intro i j
    rw [hpair i j, hone i, hone j]
    simp only [map_add, LinearMap.add_apply]
    rw [cubeForm_symm (u j) (u i)]
    field_simp
    ring
  rw [hq, hexp]
  simp only [hBij]
  have e : ∑ i, ∑ j, q i * q j * -(cubeForm ω U (u i) (u j) / U.latticeVolume) =
      -(∑ i, ∑ j, q i * q j * cubeForm ω U (u i) (u j)) / U.latticeVolume := by
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  ring

theorem isSlopeQuadratic_cubeMu (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) : IsSlopeQuadratic (cubeMu ω U) :=
  fun q => cubeMu_eq_sum_polarization hd hP hU q

theorem isSlopeQuadratic_cubeNu (ω : Configuration d) (U : TriadicCube d) :
    IsSlopeQuadratic (cubeNu ω U) :=
  fun ξ => cubeNu_eq_sum_polarization ω U ξ

/-- `x ≤ 2 A B` when `x ≤ A² / τ + B² τ` for every `τ > 0`. -/
theorem le_two_mul_of_forall_le_div_add_mul {x A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ τ : ℝ, 0 < τ → x ≤ A ^ 2 / τ + B ^ 2 * τ) : x ≤ 2 * A * B := by
  rcases hA.eq_or_lt with hA0 | hApos
  · rw [← hA0]
    by_contra hx
    have hx0 : 0 < x := by linarith
    have h1 := h (x / (2 * (B ^ 2 + 1))) (by positivity)
    rw [← hA0] at h1
    have hlt : B ^ 2 * (x / (2 * (B ^ 2 + 1))) < x := by
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith [sq_nonneg B]
    have e : (0 : ℝ) ^ 2 / (x / (2 * (B ^ 2 + 1))) = 0 := by simp
    linarith
  rcases hB.eq_or_lt with hB0 | hBpos
  · rw [← hB0]
    by_contra hx
    have hx0 : 0 < x := by linarith
    have h1 := h (2 * A ^ 2 / x) (by positivity)
    rw [← hB0] at h1
    have e : A ^ 2 / (2 * A ^ 2 / x) = x / 2 := by
      have := hApos.ne'
      field_simp
    have e2 : (0 : ℝ) ^ 2 * (2 * A ^ 2 / x) = 0 := by simp
    linarith
  · have h1 := h (A / B) (div_pos hApos hBpos)
    have e : A ^ 2 / (A / B) + B ^ 2 * (A / B) = 2 * A * B := by
      have := hApos.ne'
      have := hBpos.ne'
      field_simp
      ring
    linarith

/-- **The error of the comparison of `μ` and `ν`** on `U`, per unit of `|q|₁ |ξ|₁`:
`3^{-n} + |U|⁻¹ ∑_{x ∈ ∂U} size + 2 · 3ᵈ (d |U|⁻¹ ∑_{z near ∂U} size^{2d-2})^{1/2}`. -/
noncomputable def cubeComparisonError (ω : Configuration d) (U : TriadicCube d) : ℝ :=
  1 / (3 : ℝ) ^ U.scale + faceSizeSum ω U / U.latticeVolume +
    2 * 3 ^ d * √(d * marginSizeSum ω U / U.latticeVolume)

theorem cubeComparisonError_nonneg (ω : Configuration d) (U : TriadicCube d) :
    0 ≤ cubeComparisonError ω U := by
  have := faceSizeSum_nonneg ω U
  have := U.latticeVolume_pos
  unfold cubeComparisonError
  positivity

/-- **Comparison of `μ` and `ν`** (Armstrong and Dario, Corollary 4.6, display (4.29), one
side): on the partition event and for a resolved cube,
`q · ξ ≤ -μ(U, q) + ν(U, ξ) + |q|₁ |ξ|₁ Y(U)`. -/
theorem sum_mul_le_neg_cubeMu_add_cubeNu_add_mul (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (q ξ : Fin d → ℝ) :
    ∑ i, q i * ξ i ≤ -cubeMu ω U q + cubeNu ω U ξ +
      (∑ i, |q i|) * (∑ i, |ξ i|) * cubeComparisonError ω U := by
  obtain ⟨v, hv, hvar, h1⟩ := exists_cubeMu_le_cubeNu_sub hd hP hU ξ q
  set Q := ∑ i, |q i| with hQ
  set Ξ := ∑ i, |ξ i| with hΞ
  set s := ∑ i, q i * ξ i with hs
  set V := U.latticeVolume with hV
  set F := faceSizeSum ω U with hF
  set M := marginSizeSum ω U with hM
  have hV0 : 0 < V := U.latticeVolume_pos
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hΞ0 : 0 ≤ Ξ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM0 : 0 ≤ M := marginSizeSum_nonneg ω U
  have hL : (U.toIntegerCube.size : ℝ) = (3 : ℝ) ^ U.scale := U.cast_size_toIntegerCube
  rw [hL] at h1
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
  have hE' : E ≤ Ξ * F + 2 * Ξ * (3 ^ d * √(d * M / V) * V) := by
    have e : 2 * √(3 ^ d * 2 * d * M) * (Ξ * √(3 ^ d * V / 2)) =
        2 * Ξ * (√(3 ^ d * 2 * d * M) * √(3 ^ d * V / 2)) := by ring
    rw [e, hsq] at hEF
    linarith
  have hQE : Q * E / V ≤ Q * Ξ * (F / V) + Q * Ξ * (2 * 3 ^ d * √(d * M / V)) := by
    rw [div_le_iff₀ hV0]
    have hV' := hV0.ne'
    calc Q * E ≤ Q * (Ξ * F + 2 * Ξ * (3 ^ d * √(d * M / V) * V)) :=
          mul_le_mul_of_nonneg_left hE' hQ0
      _ = _ := by
          field_simp
  have hs_abs : |s| / (3 : ℝ) ^ U.scale ≤ Q * Ξ * (1 / (3 : ℝ) ^ U.scale) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (abs_sum_mul_le_sum_abs_mul q ξ) (by positivity)
  have hC : Q * Ξ * cubeComparisonError ω U = Q * Ξ * (1 / (3 : ℝ) ^ U.scale) +
      Q * Ξ * (F / V) + Q * Ξ * (2 * 3 ^ d * √(d * M / V)) := by
    unfold cubeComparisonError
    ring
  rw [hC]
  linarith

/-- The bound `Λ(U) = d² C₃² |U|⁻¹ ∑_{z ∈ U} size^{2d-2}` of `-μ(U, ·)` (Lemma 4.4). -/
noncomputable def cubeMuBound (ω : Configuration d) (U : TriadicCube d) : ℝ :=
  d * d * coarseGradConstant d ^ 2 *
    (∑ z ∈ U.toIntegerCube.vertices,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1))) / U.latticeVolume

theorem cubeMuBound_nonneg (ω : Configuration d) (U : TriadicCube d) : 0 ≤ cubeMuBound ω U := by
  have h : 0 ≤ ∑ z ∈ U.toIntegerCube.vertices,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) :=
    Finset.sum_nonneg fun _ _ => pow_nonneg (stoppingSize_nonneg _ _) _
  have := U.latticeVolume_pos
  unfold cubeMuBound
  positivity

/-- **Upper bound for `-μ`** (Armstrong and Dario, Lemma 4.4): `-μ(U, r) ≤ Λ(U) |r|²`. -/
theorem neg_cubeMu_le_cubeMuBound_mul (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (r : Fin d → ℝ) :
    -cubeMu ω U r ≤ cubeMuBound ω U * ∑ i, r i ^ 2 := by
  have h := neg_cubeMu_le hd hP hU r
  have hsum : ∑ z ∈ crossingClusterVertices ω U,
      ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * (d - 1)) ≤
      ∑ z ∈ U.toIntegerCube.vertices,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) := by
    calc _ = ∑ z ∈ crossingClusterVertices ω U,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) :=
          Finset.sum_congr rfl fun z _ => by rw [stoppingSize_goodCubes_eq hP z]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => pow_nonneg (stoppingSize_nonneg _ _) _
  have hr := sq_sum_abs_le_card_mul r
  have hV0 := U.latticeVolume_pos
  calc -cubeMu ω U r ≤ _ := h
    _ ≤ d * coarseGradConstant d ^ 2 * (d * ∑ i, r i ^ 2) *
          (∑ z ∈ U.toIntegerCube.vertices,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1))) /
            U.latticeVolume :=
        (div_le_div_iff_of_pos_right hV0).2 (mul_le_mul
          (mul_le_mul_of_nonneg_left hr (by positivity)) hsum (by positivity) (by positivity))
    _ = cubeMuBound ω U * ∑ i, r i ^ 2 := by
        unfold cubeMuBound
        ring

/-- **The quantity `ω(U, q)` of Armstrong and Dario** (Section 5, before Lemma 5.3), in every
dimension: `ν(U, ā⁻¹ q) - μ(U, q) - q · ā⁻¹ q`, with `ν` and `μ` replaced by `0` off the event
that the partition exists and resolves `U`. -/
noncomputable def cubeOmega (p : unitInterval) (ω : Configuration d) (U : TriadicCube d)
    (q : Fin d → ℝ) : ℝ :=
  ((if PartitionEvent ω ∧ PartitionResolved ω U then
      cubeNu ω U ((cubeAhom p)⁻¹ *ᵥ q) else 0) +
    (if PartitionEvent ω ∧ PartitionResolved ω U then -cubeMu ω U q else 0)) -
    ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i

/-- **The quantity `ρ(U) = sup_q |q|⁻² ω(U, q)₊`** of Armstrong and Dario (the supremum in
display (5.6), the left side of display (5.42) and the proof of Lemma 5.11), in every dimension. -/
noncomputable def cubeRho (p : unitInterval) (ω : Configuration d) (U : TriadicCube d) : ℝ :=
  ⨆ q : Fin d → ℝ, max (cubeOmega p ω U q) 0 / ∑ i, q i ^ 2

/-- `q ↦ ω(U, q)` is a quadratic form. -/
theorem isSlopeQuadratic_cubeOmega (hd : 0 < d) (p : unitInterval) (ω : Configuration d)
    (U : TriadicCube d) : IsSlopeQuadratic (cubeOmega p ω U) := by
  have hdot := isSlopeQuadratic_dotProduct_mulVec (cubeAhom (d := d) p)⁻¹
  by_cases h : PartitionEvent ω ∧ PartitionResolved ω U
  · have e : cubeOmega p ω U = fun q =>
        (cubeNu ω U ((cubeAhom p)⁻¹ *ᵥ q) + -cubeMu ω U q) -
          ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i := by
      funext q
      simp only [cubeOmega, if_pos h]
    rw [e]
    exact (((isSlopeQuadratic_cubeNu ω U).comp_mulVec _).add
      (isSlopeQuadratic_cubeMu hd h.1 h.2).neg).sub hdot
  · have e : cubeOmega p ω U = fun q =>
        ((fun _ => (0 : ℝ)) q + (fun _ => (0 : ℝ)) q) - ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i := by
      funext q
      simp only [cubeOmega, if_neg h]
    rw [e]
    exact (isSlopeQuadratic_zero.add isSlopeQuadratic_zero).sub hdot

/-- The ratio `|q|⁻² g(q)₊` of a quadratic function is bounded. -/
theorem bddAbove_max_div_of_isSlopeQuadratic {g : (Fin d → ℝ) → ℝ} (hg : IsSlopeQuadratic g) :
    BddAbove (Set.range fun q : Fin d → ℝ => max (g q) 0 / ∑ i, q i ^ 2) := by
  refine ⟨∑ i, ∑ j, |slopeMatrix g i j|, Set.forall_mem_range.2 fun q => ?_⟩
  have hK0 : 0 ≤ ∑ i, ∑ j, |slopeMatrix g i j| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  rcases (Finset.sum_nonneg fun i _ => sq_nonneg (q i) : 0 ≤ ∑ i, q i ^ 2).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]
    exact hK0
  · rw [div_le_iff₀ hpos]
    exact max_le ((le_abs_self _).trans (hg.abs_le q)) (by positivity)

theorem bddAbove_cubeOmega_ratio (hd : 0 < d) (p : unitInterval) (ω : Configuration d)
    (U : TriadicCube d) :
    BddAbove (Set.range fun q : Fin d → ℝ => max (cubeOmega p ω U q) 0 / ∑ i, q i ^ 2) :=
  bddAbove_max_div_of_isSlopeQuadratic (isSlopeQuadratic_cubeOmega hd p ω U)

theorem cubeRho_nonneg (hd : 0 < d) (p : unitInterval) (ω : Configuration d)
    (U : TriadicCube d) : 0 ≤ cubeRho p ω U := by
  have h := le_ciSup (bddAbove_cubeOmega_ratio hd p ω U) 0
  rw [cubeRho]
  simpa using h

/-- `ω(U, q) ≤ ρ(U) |q|²`. -/
theorem cubeOmega_le_cubeRho_mul (hd : 0 < d) (p : unitInterval) (ω : Configuration d)
    (U : TriadicCube d) (q : Fin d → ℝ) :
    cubeOmega p ω U q ≤ cubeRho p ω U * ∑ i, q i ^ 2 := by
  rcases (Finset.sum_nonneg fun i _ => sq_nonneg (q i) : 0 ≤ ∑ i, q i ^ 2).eq_or_lt with h0 | hpos
  · have hq : q = 0 := funext fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (q j)).1 h0.symm i
        (Finset.mem_univ i)
      simpa using this
    rw [hq, (isSlopeQuadratic_cubeOmega hd p ω U).apply_zero]
    simp
  · have h := le_ciSup (bddAbove_cubeOmega_ratio hd p ω U) q
    rw [div_le_iff₀ hpos] at h
    exact (le_max_left _ _).trans h

/-- **The comparison of `μ` and `ν` for `ω`**: on the partition event and for a resolved cube,
`ω(U, q) ≥ -d S Y(U) |q|²`, where `S` bounds the `ℓ¹` operator norm of `ā⁻¹`. -/
theorem neg_le_cubeOmega (hd : 0 < d) (p : unitInterval) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) {S : ℝ}
    (hS : ∀ v : Fin d → ℝ, ∑ i, |((cubeAhom p)⁻¹ *ᵥ v) i| ≤ S * ∑ i, |v i|) (q : Fin d → ℝ) :
    -(d * S * cubeComparisonError ω U * ∑ i, q i ^ 2) ≤ cubeOmega p ω U q := by
  have hc : PartitionEvent ω ∧ PartitionResolved ω U := ⟨hP, hU⟩
  have h := sum_mul_le_neg_cubeMu_add_cubeNu_add_mul hd hP hU q ((cubeAhom p)⁻¹ *ᵥ q)
  have hY0 := cubeComparisonError_nonneg ω U
  have hQ0 : 0 ≤ ∑ i, |q i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 : (∑ i, |q i|) * (∑ i, |((cubeAhom p)⁻¹ *ᵥ q) i|) * cubeComparisonError ω U ≤
      (∑ i, |q i|) * (S * ∑ i, |q i|) * cubeComparisonError ω U :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hS q) hQ0) hY0
  have h2 : (∑ i, |q i|) ^ 2 ≤ d * ∑ i, q i ^ 2 := sq_sum_abs_le_card_mul q
  have hS0 : 0 ≤ S := by
    by_contra hneg
    have := hS (Pi.single ⟨0, hd⟩ 1)
    have hpos : 0 < ∑ i, |(Pi.single ⟨0, hd⟩ 1 : Fin d → ℝ) i| := by
      rw [Finset.sum_eq_single ⟨0, hd⟩ (fun j _ hj => by simp [hj]) (by simp)]
      simp
    have : S * ∑ i, |(Pi.single ⟨0, hd⟩ 1 : Fin d → ℝ) i| < 0 :=
      mul_neg_of_neg_of_pos (not_le.1 hneg) hpos
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
      abs_nonneg (((cubeAhom p)⁻¹ *ᵥ (Pi.single ⟨0, hd⟩ 1 : Fin d → ℝ)) i)]
  have h3 : (∑ i, |q i|) * (S * ∑ i, |q i|) * cubeComparisonError ω U ≤
      d * S * cubeComparisonError ω U * ∑ i, q i ^ 2 := by
    have := mul_le_mul_of_nonneg_left h2 (mul_nonneg hS0 hY0)
    nlinarith
  simp only [cubeOmega, if_pos hc]
  linarith

/-- **Lemma 5.3 of Armstrong and Dario** (display (5.6), every dimension, on the partition event,
for a resolved cube): with `Y(U)` the error of the comparison of `μ` and `ν`, `Λ(U)` the bound of
`-μ(U, ·)` from Lemma 4.4 and `S` an `ℓ¹` operator bound of `ā⁻¹`,
`|μ(U, q) + (1/2) q · ā⁻¹ q| ≤ (d/2) (2 d Y S + √(4 d (Λ + 1) (ρ(U) + Y S))) |q|²` and
`|ν(U, ā⁻¹ q) - (1/2) q · ā⁻¹ q| ≤
  (ρ(U) + d Y S + (d/2) (2 d Y S + √(4 d (Λ + 1) (ρ(U) + Y S)))) |q|²`. -/
theorem cube_minimalset (hd : 0 < d) (p : unitInterval) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ v : Fin d → ℝ, ∑ i, |((cubeAhom p)⁻¹ *ᵥ v) i| ≤ S * ∑ i, |v i|) (q : Fin d → ℝ) :
    |cubeMu ω U q + 1 / 2 * ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i| ≤
        d / 2 * (2 * d * cubeComparisonError ω U * S +
          √(4 * d * (cubeMuBound ω U + 1) * (cubeRho p ω U + cubeComparisonError ω U * S))) *
            ∑ i, q i ^ 2 ∧
      |cubeNu ω U ((cubeAhom p)⁻¹ *ᵥ q) - 1 / 2 * ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i| ≤
        (cubeRho p ω U + d * cubeComparisonError ω U * S +
          d / 2 * (2 * d * cubeComparisonError ω U * S +
            √(4 * d * (cubeMuBound ω U + 1) * (cubeRho p ω U + cubeComparisonError ω U * S)))) *
              ∑ i, q i ^ 2 := by
  have hc : PartitionEvent ω ∧ PartitionResolved ω U := ⟨hP, hU⟩
  set Y := cubeComparisonError ω U with hY
  have hY0 : 0 ≤ Y := cubeComparisonError_nonneg ω U
  have hg : IsSlopeQuadratic fun q => -cubeMu ω U q := (isSlopeQuadratic_cubeMu hd hP hU).neg
  have hΛ0 := cubeMuBound_nonneg ω U
  have hρ := cubeRho_nonneg hd p ω U
  have hcomp : ∀ p' q' : Fin d → ℝ, ∑ i, q' i * p' i ≤
      -cubeMu ω U q' + cubeNu ω U p' + Y * ((∑ i, |p' i|) * ∑ i, |q' i|) := fun p' q' => by
    have h := sum_mul_le_neg_cubeMu_add_cubeNu_add_mul hd hP hU q' p'
    linarith
  have hup : ∀ r : Fin d → ℝ, -cubeMu ω U r ≤ (cubeMuBound ω U + 1) * ∑ i, r i ^ 2 :=
    fun r => by
      have h := neg_cubeMu_le_cubeMuBound_mul hd hP hU r
      have hr : 0 ≤ ∑ i, r i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      nlinarith
  have hω : ∀ q' : Fin d → ℝ, cubeNu ω U ((cubeAhom p)⁻¹ *ᵥ q') + -cubeMu ω U q' -
      ∑ i, q' i * ((cubeAhom p)⁻¹ *ᵥ q') i ≤ cubeRho p ω U * ∑ i, q' i ^ 2 := fun q' => by
    have h := cubeOmega_le_cubeRho_mul hd p ω U q'
    simp only [cubeOmega, if_pos hc] at h
    exact h
  have hmain := abs_slopeQuadratic_sub_half_le hd hg (cubeAhom p)⁻¹ hS0 hS hY0
    (by positivity : (0 : ℝ) < cubeMuBound ω U + 1) hρ hcomp hup hω q
  have hq0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨?_, ?_⟩
  · rw [show cubeMu ω U q + 1 / 2 * ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i =
      -(-cubeMu ω U q - 1 / 2 * ∑ i, q i * ((cubeAhom p)⁻¹ *ᵥ q) i) by ring, abs_neg]
    exact hmain
  · have hlow := neg_le_cubeOmega hd p hP hU hS q
    have hupω := cubeOmega_le_cubeRho_mul hd p ω U q
    simp only [cubeOmega, if_pos hc] at hlow hupω
    rw [← hY] at hlow
    rw [abs_le] at hmain ⊢
    obtain ⟨hm1, hm2⟩ := hmain
    have k1 : 0 ≤ cubeRho p ω U * ∑ i, q i ^ 2 := mul_nonneg hρ hq0
    have k2 : 0 ≤ d * Y * S * ∑ i, q i ^ 2 := by positivity
    constructor <;> nlinarith

end Rigidity.Percolation
