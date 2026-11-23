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

end Rigidity.Percolation
