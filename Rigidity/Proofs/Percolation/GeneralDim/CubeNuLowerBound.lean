import Rigidity.Proofs.Percolation.GeneralDim.CubeSizeMoments
import Rigidity.Proofs.Percolation.GeneralDim.CubeMuLowerBound
import Rigidity.Proofs.Percolation.GeneralDim.CubeMuUpperBound

/-!
# Deterministic lower bound for `ν` on triadic cubes of `ℤ^d`

For a resolved triadic cube `U` of side `L` on the partition event, the comparison of `μ(U, κ p)`
and `ν(U, p)` (Corollary 4.6), the upper bound for `-μ` (Lemma 4.4) and the bound on the boundary
error (proof of Lemma 4.5) give, for every `κ > 0`,

`κ |p|² ≤ ν(U, p) + d C₃² κ² |p|₁² S₁ / |U| + κ |p|² / L +
  κ |p|₁² (S₂ / |U| + 3^d (4 d S₃ √L / |U| + 1 / √L) / 2)`,

with `S₁ = ∑_{x ∈ U} s_x^{2d-2}`, `S₂` the sum of the partition sizes over the faces of `U` and
`S₃ = ∑_{z ∈ U} ∑_i s_z^{2d-2} 1{margin_i(z) < s_z}`, `s_x` the partition sizes. This is the
deterministic step of the proof of Lemma 4.7 of Armstrong and Dario, (4.31); the random terms are
controlled in expectation by `CubeSizeMoments`.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation Rigidity.External
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ}

theorem coarseGradConstant_pos (hd : 0 < d) : 0 < coarseGradConstant d := by
  unfold coarseGradConstant
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

/-- The square of the boundary weight is controlled by the tail-weighted partition sizes. -/
theorem cubeBoundaryWeight_sq_le {ω : Configuration d} (hP : PartitionEvent ω)
    (U : TriadicCube d) (z : Vertex d) :
    cubeBoundaryWeight ω U z ^ 2 ≤ 4 * d * ∑ i : Fin d,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
        (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
          then 1 else 0) := by
  have h := cubeBoundaryWeight_le hP U z
  rw [← stoppingSize_goodCubes_eq hP z] at h
  set s := TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
  set a : Fin d → ℝ := fun i => 2 * s ^ (d - 1) * (if (U.margin z i : ℝ) < s then 1 else 0)
  have hW0 := cubeBoundaryWeight_nonneg ω U z
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
  rw [Finset.card_univ, Fintype.card_fin] at hcs
  have ha2 : ∀ i, a i ^ 2 = 4 * (s ^ (2 * (d - 1)) *
      (if (U.margin z i : ℝ) < s then 1 else 0)) := by
    intro i
    simp only [a]
    split_ifs
    · rw [pow_mul]; ring
    · ring
  calc cubeBoundaryWeight ω U z ^ 2 ≤ (∑ i, a i) ^ 2 := pow_le_pow_left₀ hW0 h 2
    _ ≤ (d : ℝ) * ∑ i, a i ^ 2 := hcs
    _ = 4 * d * ∑ i : Fin d, s ^ (2 * (d - 1)) * (if (U.margin z i : ℝ) < s then 1 else 0) := by
        simp only [ha2, ← Finset.mul_sum]
        ring

/-- **Deterministic lower bound for `ν`** (Armstrong and Dario, proof of Lemma 4.7). -/
theorem le_cubeNu_add_of_resolved (hd : 0 < d) {ω : Configuration d} (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (p : Fin d → ℝ)
    (hp : 0 < ∑ i, |p i|) {κ : ℝ} (hκ : 0 < κ) :
    κ * ∑ i, p i ^ 2 ≤ cubeNu ω U p +
      d * coarseGradConstant d ^ 2 * κ ^ 2 * (∑ i, |p i|) ^ 2 *
        (∑ z ∈ U.toIntegerCube.vertices,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1))) /
          U.latticeVolume +
      κ * (∑ i, p i ^ 2) / (3 : ℝ) ^ U.scale +
      κ * (∑ i, |p i|) ^ 2 * ((∑ i : Fin d,
        (∑ x ∈ U.toIntegerCube.upperFace i, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x +
          ∑ x ∈ U.toIntegerCube.lowerFace i,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x)) / U.latticeVolume +
        3 ^ d * (4 * d * (∑ z ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
            (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
              then 1 else 0)) * √((3 : ℝ) ^ U.scale) / U.latticeVolume +
          1 / √((3 : ℝ) ^ U.scale)) / 2) := by
  -- the quantities of the statement
  obtain ⟨S₁, hS₁⟩ : ∃ x : ℝ, x = ∑ z ∈ U.toIntegerCube.vertices,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) := ⟨_, rfl⟩
  obtain ⟨S₂, hS₂⟩ : ∃ x : ℝ, x = ∑ i : Fin d,
      (∑ x ∈ U.toIntegerCube.upperFace i, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x +
        ∑ x ∈ U.toIntegerCube.lowerFace i,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x) := ⟨_, rfl⟩
  obtain ⟨S₃, hS₃⟩ : ∃ x : ℝ, x = ∑ z ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
        (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
          then 1 else 0) := ⟨_, rfl⟩
  rw [← hS₁, ← hS₂, ← hS₃]
  obtain ⟨P, hPdef⟩ : ∃ x : ℝ, x = ∑ i, |p i| := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ x : ℝ, x = ∑ i, p i ^ 2 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ x : ℝ, x = (3 : ℝ) ^ U.scale := ⟨_, rfl⟩
  rw [← hPdef, ← hSdef, ← hL]
  rw [← hPdef] at hp
  have hvol := U.latticeVolume_pos
  have hL0 : 0 < L := by rw [hL]; positivity
  have hsL : 0 < √L := Real.sqrt_pos.2 hL0
  obtain ⟨v, hv, hvar, hle⟩ := exists_cubeMu_le_cubeNu_sub hd hP hU p (κ • p)
  have hs : ∑ i, (κ • p) i * p i = κ * S := by
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hP' : ∑ i, |(κ • p) i| = κ * P := by
    rw [hPdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hκ]
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  have hsize : (U.toIntegerCube.size : ℝ) = L := by
    rw [hL]
    change ((3 ^ U.scale : ℕ) : ℝ) = _
    push_cast
    rfl
  rw [hs, hP', abs_of_nonneg (by positivity : 0 ≤ κ * S), hsize] at hle
  -- the upper bound for `-μ`
  have hmu := neg_cubeMu_le hd hP hU (κ • p)
  rw [hP'] at hmu
  have hC1 : ∑ z ∈ crossingClusterVertices ω U, ((3 : ℝ) ^ (partitionCube ω z).scale) ^
      (2 * (d - 1)) ≤ S₁ := by
    rw [hS₁]
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun z _ _ => by positivity).trans (le_of_eq (Finset.sum_congr rfl fun z _ => ?_))
    rw [stoppingSize_goodCubes_eq hP z]
  have hmu' : -cubeMu ω U (κ • p) ≤ d * coarseGradConstant d ^ 2 * κ ^ 2 * P ^ 2 * S₁ /
      U.latticeVolume := by
    refine hmu.trans (div_le_div_of_nonneg_right ?_ hvol.le)
    rw [show (d : ℝ) * coarseGradConstant d ^ 2 * (κ * P) ^ 2 =
      d * coarseGradConstant d ^ 2 * κ ^ 2 * P ^ 2 by ring]
    exact mul_le_mul_of_nonneg_left hC1 (by positivity)
  -- the boundary error
  have hτ0 : 0 < 1 / (P * √L) := by positivity
  have hBE := cubeBoundaryError_le hd hP hU p v hτ0
  have hW : ∑ z ∈ crossingClusterVertices ω U, cubeBoundaryWeight ω U z ^ 2 ≤ 4 * d * S₃ := by
    calc ∑ z ∈ crossingClusterVertices ω U, cubeBoundaryWeight ω U z ^ 2
        ≤ ∑ z ∈ crossingClusterVertices ω U, 4 * d * ∑ i : Fin d,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
              (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
                then 1 else 0) :=
          Finset.sum_le_sum fun z _ => cubeBoundaryWeight_sq_le hP U z
      _ ≤ ∑ z ∈ U.toIntegerCube.vertices, 4 * d * ∑ i : Fin d,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
              (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
                then 1 else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun z _ _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
          exact mul_nonneg (pow_nonneg (stoppingSize_nonneg _ _) _) (by split_ifs <;> norm_num)
      _ = 4 * d * S₃ := by rw [hS₃, Finset.mul_sum]
  have hfaces : ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i,
      (∑ j, |p j|) * 3 ^ (partitionCube ω x).scale + ∑ x ∈ U.toIntegerCube.lowerFace i,
        (∑ j, |p j|) * 3 ^ (partitionCube ω x).scale) = P * S₂ := by
    rw [hS₂, hPdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun x _ => ?_ <;>
      rw [stoppingSize_goodCubes_eq hP x]
  have hB : 2 * cubeForm ω U v v ≤ 3 ^ d * U.latticeVolume * P ^ 2 := by
    have h1 := cubeForm_le_of_cubeNu_variation p hv hvar
    have h2 := cubeNu_le (ω := ω) (U := U) p
    rw [← hPdef] at h2
    nlinarith
  rw [hfaces] at hBE
  have hBE' : cubeBoundaryError ω U p v ≤ P * S₂ +
      (3 ^ d * (4 * d * S₃) / (1 / (P * √L)) + 1 / (P * √L) * (3 ^ d * U.latticeVolume * P ^ 2)) /
        2 := by
    refine hBE.trans ?_
    have h1 : (3 ^ d * ∑ z ∈ crossingClusterVertices ω U, cubeBoundaryWeight ω U z ^ 2) /
        (1 / (P * √L)) ≤ 3 ^ d * (4 * d * S₃) / (1 / (P * √L)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by positivity)) hτ0.le
    have h2 : 1 / (P * √L) * (2 * cubeForm ω U v v) ≤
        1 / (P * √L) * (3 ^ d * U.latticeVolume * P ^ 2) :=
      mul_le_mul_of_nonneg_left hB hτ0.le
    linarith
  -- assembling
  have hkey : κ * P * (P * S₂ + (3 ^ d * (4 * d * S₃) / (1 / (P * √L)) + 1 / (P * √L) *
      (3 ^ d * U.latticeVolume * P ^ 2)) / 2) / U.latticeVolume = κ * P ^ 2 *
        (S₂ / U.latticeVolume + 3 ^ d * (4 * d * S₃ * √L / U.latticeVolume + 1 / √L) / 2) := by
    field_simp
  have hBEterm : κ * P * cubeBoundaryError ω U p v / U.latticeVolume ≤
      κ * P ^ 2 * (S₂ / U.latticeVolume +
        3 ^ d * (4 * d * S₃ * √L / U.latticeVolume + 1 / √L) / 2) := by
    rw [← hkey]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hBE' (by positivity)) hvol.le
  linarith

end Rigidity.Percolation
