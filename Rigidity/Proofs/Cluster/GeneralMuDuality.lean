import Rigidity.Proofs.Cluster.GeneralMuQuadratic
import Rigidity.Proofs.Cluster.GeneralAhomIsotropic
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuLowerBoundMean

/-!
# The convex duality inequality between the limits of `-μ` and `ν`, in every dimension

On resolved cubes, the comparison of `μ` and `ν` with boundary errors (Armstrong and Dario,
Corollary 4.6; `exists_cubeMu_le_cubeNu_sub`), the bound of the boundary error through the
boundary weights (`cubeBoundaryError_le`) with Young's parameter `τ = 3^{-m/2}`, and the energy
bound `B(v, v) ≤ 2 |U| ν(U, ξ) ≤ (3^d/2) |U| |ξ|₁²` of the maximizer give, for all slopes `q`, `ξ`,

`q · ξ ≤ -μ(U, q) + ν(U, ξ) + ε(U)`

with an error `ε(U)` built from the partition sizes at the faces and near the faces of `U`. Taking
expectations (with `q · ξ ≤ |q · ξ| 1{U unresolved} + ν(U, ξ)` off the resolved event) and letting
the scale tend to infinity,

`q · ξ ≤ lim E[-μ(□_m, q)] + lim E[ν(□_m, ξ)] = lim E[-μ(□_m, q)] + (1/2) ξ · ā ξ`

(`sum_mul_le_cubeMuLimit_add_cubeNuLimit`). This is one of the two inequalities identifying the
limit of `-μ` as `(1/2) q · ā⁻¹ q` (Armstrong and Dario, Section 5, after Definition 5.1); with
`ā = σ I` it gives `|q|² / (2σ) ≤ lim E[-μ(□_m, q)]` (`cubeMuLimit_ge_of_cubeAhom_eq_smul_one`).
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The partition sizes summed over the faces of `U`. -/
noncomputable def faceSizeSum (ω : Configuration d) (U : TriadicCube d) : ℝ :=
  ∑ i : Fin d, (∑ x ∈ U.toIntegerCube.upperFace i,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x +
    ∑ x ∈ U.toIntegerCube.lowerFace i, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x)

/-- The partition sizes near the faces of `U`, as in the lower bound for `ν`. -/
noncomputable def marginSizeSum (ω : Configuration d) (U : TriadicCube d) : ℝ :=
  ∑ z ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
    TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
      (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
        then 1 else 0)

theorem faceSizeSum_nonneg (ω : Configuration d) (U : TriadicCube d) : 0 ≤ faceSizeSum ω U :=
  Finset.sum_nonneg fun _ _ => add_nonneg
    (Finset.sum_nonneg fun _ _ => stoppingSize_nonneg _ _)
    (Finset.sum_nonneg fun _ _ => stoppingSize_nonneg _ _)

theorem marginSizeSum_nonneg (ω : Configuration d) (U : TriadicCube d) :
    0 ≤ marginSizeSum ω U :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (pow_nonneg (stoppingSize_nonneg _ _) _) (by split_ifs <;> norm_num)

/-- **Comparison of `μ` and `ν` for arbitrary slopes** on resolved cubes (Armstrong and Dario,
Corollary 4.6, with the boundary error bounded through the partition sizes at and near the faces
of `U`). -/
theorem sum_mul_le_neg_cubeMu_add_cubeNu (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (q ξ : Fin d → ℝ) :
    ∑ i, q i * ξ i ≤ -cubeMu ω U q + cubeNu ω U ξ +
      (|∑ i, q i * ξ i| / (3 : ℝ) ^ U.scale +
        (∑ i, |q i|) * (∑ i, |ξ i|) / U.latticeVolume * faceSizeSum ω U +
        2 * d * 3 ^ d * (∑ i, |q i|) * √((3 : ℝ) ^ U.scale) / U.latticeVolume *
          marginSizeSum ω U +
        3 ^ d * (∑ i, |q i|) * (∑ i, |ξ i|) ^ 2 / (2 * √((3 : ℝ) ^ U.scale))) := by
  obtain ⟨v, hv, hvar, h1⟩ := exists_cubeMu_le_cubeNu_sub hd hP hU ξ q
  set Q := ∑ i, |q i| with hQ
  set Ξ := ∑ i, |ξ i| with hΞ
  set s := ∑ i, q i * ξ i with hs
  set V := U.latticeVolume with hV
  set R := √((3 : ℝ) ^ U.scale) with hR
  have hV0 : 0 < V := U.latticeVolume_pos
  have hR0 : 0 < R := Real.sqrt_pos.2 (by positivity)
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hΞ0 : 0 ≤ Ξ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hL : (U.toIntegerCube.size : ℝ) = (3 : ℝ) ^ U.scale := U.cast_size_toIntegerCube
  rw [hL] at h1
  have hτ : 0 < 1 / R := by positivity
  have h2 := cubeBoundaryError_le hd hP hU ξ v hτ
  set E := cubeBoundaryError ω U ξ v with hE
  set B := cubeForm ω U v v with hB
  set W := ∑ z ∈ crossingClusterVertices ω U, cubeBoundaryWeight ω U z ^ 2 with hW
  have hface : ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i, Ξ * 3 ^ (partitionCube ω x).scale +
      ∑ x ∈ U.toIntegerCube.lowerFace i, Ξ * 3 ^ (partitionCube ω x).scale) =
      Ξ * faceSizeSum ω U := by
    unfold faceSizeSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun x _ => by rw [stoppingSize_goodCubes_eq hP x]
  rw [hface] at h2
  have h3 : W ≤ 4 * d * marginSizeSum ω U := by
    calc W ≤ ∑ z ∈ U.toIntegerCube.vertices, cubeBoundaryWeight ω U z ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => sq_nonneg _
      _ ≤ ∑ z ∈ U.toIntegerCube.vertices, 4 * d * ∑ i : Fin d,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
              (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
                then 1 else 0) :=
          Finset.sum_le_sum fun z _ => cubeBoundaryWeight_sq_le hP U z
      _ = 4 * d * marginSizeSum ω U := by rw [marginSizeSum, Finset.mul_sum]
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
  have hE' : Q * E / V ≤ Q * Ξ / V * faceSizeSum ω U +
      2 * d * 3 ^ d * Q * R / V * marginSizeSum ω U + 3 ^ d * Q * Ξ ^ 2 / (2 * R) := by
    have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hB0 : 0 ≤ B := cubeForm_self_nonneg v
    have h5 : E ≤ Ξ * faceSizeSum ω U + (3 ^ d * (4 * d * marginSizeSum ω U) * R +
        2 * (2 * V * (3 ^ d / 4 * Ξ ^ 2)) / R) / 2 := by
      refine h2.trans ?_
      have e1 : 3 ^ d * W / (1 / R) = 3 ^ d * W * R := by field_simp
      have e2 : 1 / R * (2 * B) = 2 * B / R := by ring
      rw [e1, e2]
      gcongr
    calc Q * E / V ≤ Q * (Ξ * faceSizeSum ω U + (3 ^ d * (4 * d * marginSizeSum ω U) * R +
          2 * (2 * V * (3 ^ d / 4 * Ξ ^ 2)) / R) / 2) / V := by gcongr
      _ = _ := by
          field_simp
          ring
  linarith

/-- The event that some partition size in `U` exceeds the side of `U`. -/
def LargePartitionSize (U : TriadicCube d) : Set (Configuration d) :=
  {ω | ∃ z ∈ U.toIntegerCube.vertices,
    (3 : ℝ) ^ U.scale < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z}

theorem measurableSet_largePartitionSize (U : TriadicCube d) :
    MeasurableSet (LargePartitionSize U) :=
  measurableSet_setOf.2 (Measurable.exists fun z => measurable_const.and
    (measurableSet_setOf.1 (measurableSet_lt measurable_const
      (measurable_stoppingSize_goodCubes z))))

theorem mem_largePartitionSize_of_not_resolved (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : ¬ PartitionResolved ω U) : ω ∈ LargePartitionSize U := by
  unfold PartitionResolved at hU
  push Not at hU
  obtain ⟨z, hz, hlt⟩ := hU
  refine ⟨z, (U.mem_toIntegerCube_vertices z).2 hz, ?_⟩
  rw [stoppingSize_goodCubes_eq hP z]
  exact pow_lt_pow_right₀ (by norm_num) hlt

/-- **The pointwise comparison with the unresolved event.** -/
theorem sum_mul_le_indicator (hd : 0 < d) (hP : PartitionEvent ω) (U : TriadicCube d)
    (q ξ : Fin d → ℝ) :
    ∑ i, q i * ξ i ≤ (if PartitionEvent ω ∧ PartitionResolved ω U then -cubeMu ω U q else 0) +
      (1 * cubeNu ω U ξ +
        (∑ i, |q i|) * (∑ i, |ξ i|) / U.latticeVolume * faceSizeSum ω U +
        2 * d * 3 ^ d * (∑ i, |q i|) * √((3 : ℝ) ^ U.scale) / U.latticeVolume *
          marginSizeSum ω U +
        |∑ i, q i * ξ i| * (LargePartitionSize U).indicator 1 ω +
        (|∑ i, q i * ξ i| / (3 : ℝ) ^ U.scale +
          3 ^ d * (∑ i, |q i|) * (∑ i, |ξ i|) ^ 2 / (2 * √((3 : ℝ) ^ U.scale)))) := by
  have hV0 := U.latticeVolume_pos
  have hF := faceSizeSum_nonneg ω U
  have hM := marginSizeSum_nonneg ω U
  have hI0 : (0 : ℝ) ≤ (LargePartitionSize U).indicator 1 ω :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hν0 := cubeNu_nonneg (ω := ω) (U := U) ξ
  have hQ0 : 0 ≤ ∑ i, |q i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hΞ0 : 0 ≤ ∑ i, |ξ i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hc2 : 0 ≤ (∑ i, |q i|) * (∑ i, |ξ i|) / U.latticeVolume * faceSizeSum ω U := by positivity
  have hc3 : 0 ≤ 2 * d * 3 ^ d * (∑ i, |q i|) * √((3 : ℝ) ^ U.scale) / U.latticeVolume *
      marginSizeSum ω U := by positivity
  have hc4 : 0 ≤ |∑ i, q i * ξ i| * (LargePartitionSize U).indicator 1 ω := by positivity
  have hc5 : 0 ≤ |∑ i, q i * ξ i| / (3 : ℝ) ^ U.scale +
      3 ^ d * (∑ i, |q i|) * (∑ i, |ξ i|) ^ 2 / (2 * √((3 : ℝ) ^ U.scale)) := by positivity
  by_cases hU : PartitionResolved ω U
  · rw [if_pos ⟨hP, hU⟩]
    have h := sum_mul_le_neg_cubeMu_add_cubeNu hd hP hU q ξ
    linarith
  · rw [if_neg fun h => hU h.2]
    rw [Set.indicator_of_mem (mem_largePartitionSize_of_not_resolved hP hU), Pi.one_apply,
      mul_one]
    have := le_abs_self (∑ i, q i * ξ i)
    linarith

/-- **The duality inequality in expectation**, for the cubes at the origin. -/
theorem exists_sum_mul_le_cubeMuMean_add_cubeNuMean [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ (q ξ : Fin d → ℝ) (m : ℕ),
      ∑ i, q i * ξ i ≤ cubeMuMean p m q + cubeNuMean p m ξ +
        ((∑ i, |q i|) * (∑ i, |ξ i|) * C + 2 * d * 3 ^ d * (∑ i, |q i|) * C +
          |∑ i, q i * ξ i| + 3 ^ d * (∑ i, |q i|) * (∑ i, |ξ i|) ^ 2 / 2) / √((3 : ℝ) ^ m) +
        |∑ i, q i * ξ i| * C * Real.exp (-c * (3 : ℝ) ^ m) := by
  have hd0 : 0 < d := by omega
  obtain ⟨CF, hCF, hfac⟩ := exists_integral_sum_faces_le hd hpc
  obtain ⟨CM, hCM, hmar⟩ := exists_integral_sum_margin_le hd hpc
  obtain ⟨Cr, cr, hcr, hres⟩ := exists_measure_not_resolved_le hd hpc
  refine ⟨max (max CF CM) (max Cr 0), cr, by positivity, hcr, fun q ξ m => ?_⟩
  set C := max (max CF CM) (max Cr 0) with hCdef
  have hCF' : CF ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCM' : CM ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCr' : Cr ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  set U : TriadicCube d := ⟨m, 0⟩ with hUdef
  set μ := latticeBondLaw d p with hμ
  set Q := ∑ i, |q i| with hQ
  set Ξ := ∑ i, |ξ i| with hΞ
  set s := ∑ i, q i * ξ i with hs
  set V := U.latticeVolume with hV
  set R := √((3 : ℝ) ^ m) with hR
  have hV0 : 0 < V := U.latticeVolume_pos
  have hR0 : 0 < R := Real.sqrt_pos.2 (by positivity)
  have hRR : R ^ 2 = (3 : ℝ) ^ m := Real.sq_sqrt (by positivity)
  have hVm : V = ((3 : ℝ) ^ m) ^ d := rfl
  have h3R : R ≤ (3 : ℝ) ^ m := by
    have h1 : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
    rw [hR]
    calc √((3 : ℝ) ^ m) ≤ √((3 : ℝ) ^ m * 3 ^ m) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 3 ^ m := Real.sqrt_mul_self (by positivity)
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hΞ0 : 0 ≤ Ξ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  -- the pointwise inequality, almost surely
  have hae : ∀ᵐ ω ∂μ, s ≤ (if PartitionEvent ω ∧ PartitionResolved ω U then -cubeMu ω U q
      else 0) + (1 * cubeNu ω U ξ + Q * Ξ / V * faceSizeSum ω U +
        2 * d * 3 ^ d * Q * R / V * marginSizeSum ω U +
        |s| * (LargePartitionSize U).indicator 1 ω +
        (|s| / (3 : ℝ) ^ U.scale + 3 ^ d * Q * Ξ ^ 2 / (2 * R))) := by
    filter_upwards [ae_partitionEvent hd hpc] with ω hP
    exact sum_mul_le_indicator hd0 hP U q ξ
  have hint := le_integral_add_of_ae_le (integrable_neg_cubeMu_indicator hd hpc U q)
    (integrable_cubeNu p U ξ)
    (show Integrable (fun ω => faceSizeSum ω U) μ from (hfac U).1)
    (show Integrable (fun ω => marginSizeSum ω U) μ from (hmar U).1)
    ((integrable_const (1 : ℝ)).indicator (measurableSet_largePartitionSize U)) _ _ _ _ _ hae
  rw [← cubeMuMean_eq_integral hd0, one_mul] at hint
  -- the expectations of the error terms
  have hF : ∫ ω, faceSizeSum ω U ∂μ ≤ C * ((3 : ℝ) ^ m) ^ (d - 1) :=
    (hfac U).2.trans (mul_le_mul_of_nonneg_right hCF' (by positivity))
  have hM : ∫ ω, marginSizeSum ω U ∂μ ≤ C * ((3 : ℝ) ^ m) ^ (d - 1) :=
    (hmar U).2.trans (mul_le_mul_of_nonneg_right hCM' (by positivity))
  have hA : ∫ ω, (LargePartitionSize U).indicator (1 : Configuration d → ℝ) ω ∂μ ≤
      C * Real.exp (-cr * (3 : ℝ) ^ m) := by
    rw [integral_indicator_one (measurableSet_largePartitionSize U), measureReal_def]
    have hsub : LargePartitionSize U ≤ᵐ[μ]
        {ω | ∃ z ∈ U.vertices, U.scale < (partitionCube ω z).scale} := by
      filter_upwards [ae_partitionEvent hd hpc] with ω hP
      rintro ⟨z, hz, hlt⟩
      refine ⟨z, (U.mem_toIntegerCube_vertices z).1 hz, ?_⟩
      rw [stoppingSize_goodCubes_eq hP z] at hlt
      exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hlt
    have h1 := (measure_mono_ae hsub).trans (hres U)
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_ofReal'] at h2
    exact h2.trans (max_le (mul_le_mul_of_nonneg_right hCr' (Real.exp_pos _).le)
      (by positivity))
  have hVd : ((3 : ℝ) ^ m) ^ (d - 1) / V = 1 / (3 : ℝ) ^ m := by
    rw [hVm]
    have h3 : (0 : ℝ) < 3 ^ m := by positivity
    rw [show ((3 : ℝ) ^ m) ^ d = ((3 : ℝ) ^ m) ^ (d - 1) * 3 ^ m by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]]
    field_simp
  have hcF : Q * Ξ / V * ∫ ω, faceSizeSum ω U ∂μ ≤ Q * Ξ * C / R := by
    calc Q * Ξ / V * ∫ ω, faceSizeSum ω U ∂μ ≤ Q * Ξ / V * (C * ((3 : ℝ) ^ m) ^ (d - 1)) :=
          mul_le_mul_of_nonneg_left hF (by positivity)
      _ = Q * Ξ * C * (((3 : ℝ) ^ m) ^ (d - 1) / V) := by ring
      _ = Q * Ξ * C / (3 : ℝ) ^ m := by rw [hVd]; ring
      _ ≤ Q * Ξ * C / R := div_le_div_of_nonneg_left (by positivity) hR0 h3R
  have hcM : 2 * d * 3 ^ d * Q * R / V * ∫ ω, marginSizeSum ω U ∂μ ≤
      2 * d * 3 ^ d * Q * C / R := by
    calc 2 * d * 3 ^ d * Q * R / V * ∫ ω, marginSizeSum ω U ∂μ
        ≤ 2 * d * 3 ^ d * Q * R / V * (C * ((3 : ℝ) ^ m) ^ (d - 1)) :=
          mul_le_mul_of_nonneg_left hM (by positivity)
      _ = 2 * d * 3 ^ d * Q * C * R * (((3 : ℝ) ^ m) ^ (d - 1) / V) := by ring
      _ = 2 * d * 3 ^ d * Q * C * R / (3 : ℝ) ^ m := by rw [hVd]; ring
      _ = 2 * d * 3 ^ d * Q * C / R := by
          rw [← hRR]
          field_simp
  have hcA : |s| * ∫ ω, (LargePartitionSize U).indicator (1 : Configuration d → ℝ) ω ∂μ ≤
      |s| * C * Real.exp (-cr * (3 : ℝ) ^ m) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hA (abs_nonneg _)
  have hc5 : |s| / (3 : ℝ) ^ U.scale ≤ |s| / R :=
    div_le_div_of_nonneg_left (abs_nonneg _) hR0 h3R
  have hfin : (Q * Ξ * C + 2 * d * 3 ^ d * Q * C + |s| + 3 ^ d * Q * Ξ ^ 2 / 2) / R =
      Q * Ξ * C / R + 2 * d * 3 ^ d * Q * C / R + |s| / R + 3 ^ d * Q * Ξ ^ 2 / (2 * R) := by
    field_simp
  have hcA' : |s| * ∫ ω, (LargePartitionSize U).indicator (fun _ => (1 : ℝ)) ω ∂μ ≤
      |s| * C * Real.exp (-cr * (3 : ℝ) ^ m) := hcA
  have hnu : ∫ ω, cubeNu ω U ξ ∂μ = cubeNuMean p m ξ := rfl
  rw [hnu] at hint
  rw [hfin]
  linarith

/-- **The duality inequality between the limits** (Armstrong and Dario, Section 5, after
Definition 5.1, in every dimension `d ≥ 2`): `q · ξ ≤ lim E[-μ(□_m, q)] + lim E[ν(□_m, ξ)]`. -/
theorem sum_mul_le_cubeMuLimit_add_cubeNuLimit [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (q ξ : Fin d → ℝ) :
    ∑ i, q i * ξ i ≤ cubeMuLimit p q + cubeNuLimit p ξ := by
  obtain ⟨C, c, hC, hc, h⟩ := exists_sum_mul_le_cubeMuMean_add_cubeNuMean hd hpc
  set K := (∑ i, |q i|) * (∑ i, |ξ i|) * C + 2 * d * 3 ^ d * (∑ i, |q i|) * C +
    |∑ i, q i * ξ i| + 3 ^ d * (∑ i, |q i|) * (∑ i, |ξ i|) ^ 2 / 2
  have hlim : Tendsto (fun m : ℕ => cubeMuMean p m q + cubeNuMean p m ξ +
      K / √((3 : ℝ) ^ m) + |∑ i, q i * ξ i| * C * Real.exp (-c * (3 : ℝ) ^ m)) atTop
      (𝓝 (cubeMuLimit p q + cubeNuLimit p ξ + K * 0 + |∑ i, q i * ξ i| * C * 0)) := by
    refine (((tendsto_cubeMuLimit hd hpc q).add (tendsto_cubeNuLimit hd hpc ξ)).add ?_).add
      ((tendsto_exp_neg_mul_three_pow hc).const_mul _)
    have := tendsto_one_div_sqrt_three_pow_atTop.const_mul K
    simpa only [mul_one_div] using this
  simp only [mul_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim fun m => h q ξ m

/-- **Lower bound for the limit of `-μ`**: if `ā = σ I`, then `|q|² / (2σ) ≤ lim E[-μ(□_m, q)]`
(the lower bound of (5.1) for `μ`, from the duality inequality with `ξ = q / σ`). -/
theorem cubeMuLimit_ge_of_cubeAhom_eq_smul_one [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {σ : ℝ} (hσ : 0 < σ)
    (hA : cubeAhom (d := d) p = σ • (1 : Matrix (Fin d) (Fin d) ℝ)) (q : Fin d → ℝ) :
    (∑ i, q i ^ 2) / (2 * σ) ≤ cubeMuLimit p q := by
  have h := sum_mul_le_cubeMuLimit_add_cubeNuLimit hd hpc q (σ⁻¹ • q)
  rw [cubeNuLimit_eq_cubeAhom hd hpc, hA] at h
  have hsum : ∑ i, ∑ j, (σ⁻¹ • q) i * (σ • (1 : Matrix (Fin d) (Fin d) ℝ)) i j * (σ⁻¹ • q) j =
      σ⁻¹ * ∑ i, q i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hji => by
      simp [Matrix.one_apply_ne' hji]) (fun h => absurd (Finset.mem_univ i) h)]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Matrix.one_apply_eq]
    field_simp
  have hlhs : ∑ i, q i * (σ⁻¹ • q) i = σ⁻¹ * ∑ i, q i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsum, hlhs] at h
  have e : (∑ i, q i ^ 2) / (2 * σ) = σ⁻¹ * ∑ i, q i ^ 2 - 1 / 2 * (σ⁻¹ * ∑ i, q i ^ 2) := by
    field_simp
    ring
  rw [e]
  linarith

end Rigidity.Percolation
