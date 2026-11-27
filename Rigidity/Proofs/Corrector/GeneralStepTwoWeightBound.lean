import Rigidity.Proofs.Corrector.GeneralStepTwoWeightMoments

/-!
# The weight of the Step 2 sum on `ℤᵈ` under its majorant

On the partition event of the good cubes of `ℤᵈ`, the sides at the two endpoints of an edge differ
by at most a factor `3`, so `m_a = max(s(x), s(y)) ≤ 3 s(x)` (`max_partSide_le`). If the plane
gradient bound satisfies `G ≤ 1 + Λ`, the factor `F_a = (κ m_a)^{7d} (Σ_{B_a} G)²` of the weight is
at most `T⁹` for the sum `T` of `1 + Λ` over the box of radius `3κ s(x)`, which has at least
`(3κ s(x))^d` points and lies in the Euclidean ball of radius `3dκ s(x)`. Hence
(`stepTwoWeight_le_weightMajorant`)

`W(u) ≤ Σ_a 1{|a - u| ≤ 3dκ σ(a)} T(a)⁹ = weightMajorant Λ (3dκ) (3dκ) u`.

This is the planar file `DarioStepTwoWeightBound` on `ℤᵈ`: the planar partition is replaced by the
partition into good cubes of `ℤᵈ` (`partSide`, `partSide_eq`), the power `14 = 7 · 2` by `7d`, the
`(3κ s)²` points of the box by `(3κ s)^d`, and the Euclidean radius `2r` of a box of radius `r` by
`d r`, so that the radii `6κ` of the majorant become `3dκ`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open Rigidity.Poincare.GeneralDim (supBox mem_supBox card_supBox)
open scoped Classical ENNReal

variable {d : ℕ}

/-- The side of the partition cube at the head of an edge is at most three times the side at its
tail. -/
theorem partSide_head_le {ω : Configuration d} (hP : PartitionEvent ω) (a : LatticeEdge d) :
    partSide ω (edgeHead a) ≤ 3 * partSide ω a.1 := by
  rw [partSide_eq hP, partSide_eq hP]
  have h := (partitionCube_scales_close hP (x := edgeHead a) (y := a.1) fun i => by
    rw [abs_sub_comm]; exact abs_sub_edgeHead_le a i).1
  calc 3 ^ (partitionCube ω (edgeHead a)).scale ≤ 3 ^ ((partitionCube ω a.1).scale + 1) :=
        Nat.pow_le_pow_right (by norm_num) h
    _ = 3 * 3 ^ (partitionCube ω a.1).scale := by ring

theorem max_partSide_le {ω : Configuration d} (hP : PartitionEvent ω) (a : LatticeEdge d) :
    max (partSide ω a.1) (partSide ω (edgeHead a)) ≤ 3 * partSide ω a.1 :=
  max_le (by omega) (partSide_head_le hP a)

/-- On the partition event the stopping size of the good cubes is the side of the partition
cube. -/
theorem stoppingSize_eq_partSide {ω : Configuration d} (hP : PartitionEvent ω) (v : Vertex d) :
    TriadicCube.stoppingSize (TriadicCube.goodCubes ω) v = (partSide ω v : ℝ) := by
  rw [partSide_eq hP, stoppingSize_goodCubes_eq hP]
  norm_num

/-- The points of the box of radius `r` around `x` are within Euclidean distance `d r` of `x`. -/
theorem norm_le_of_mem_supBox {x z : Vertex d} {r : ℕ} (h : z ∈ supBox x r) :
    ‖latticeEuclideanEmbedding (z - x)‖ ≤ d * r :=
  (norm_sub_le_of_mem_supBox h).1

/-- **The radius with one bond closed**: on the partition event of `ω`,
`max(max(s(x), s(y)), s♭(x)) ≤ 3 max(s(x), s♭(x))` for the edge `a` from `x` to `y`, with `s♭` the
side of the partition cubes of the configuration with the bond `e` closed. -/
theorem max_partSide_setBond_le {ω : Configuration d} (hP : PartitionEvent ω) (e : Bond d)
    (a : LatticeEdge d) :
    max (max (partSide ω a.1) (partSide ω (edgeHead a))) (partSide (setBond e false ω) a.1) ≤
      3 * max (partSide ω a.1) (partSide (setBond e false ω) a.1) :=
  max_le ((max_partSide_le hP a).trans (Nat.mul_le_mul_left 3 (le_max_left _ _)))
    ((le_max_right _ _).trans (le_mul_of_one_le_left (Nat.zero_le _) (by norm_num)))

/-- On the partition events of `ω` and of the configuration with the bond `β(a)` closed, the radius
of the edge `a` is `max(s(x), s♭(x))`. -/
theorem edgeRadius_eq_partSide {ω : Configuration d} (β : LatticeEdge d → Bond d)
    (a : LatticeEdge d) (hP : PartitionEvent ω) (hP' : PartitionEvent (setBond (β a) false ω)) :
    edgeRadius β a ω = max (partSide ω a.1 : ℝ) (partSide (setBond (β a) false ω) a.1 : ℝ) := by
  unfold edgeRadius flipSize
  rw [stoppingSize_eq_partSide hP, stoppingSize_eq_partSide hP']

section Grad

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **The weight under its majorant**: on the partition event, if `G ≤ 1 + Λ` with `Λ ≥ 0`, then
`W(u) ≤ Σ_a 1{|a - u| ≤ 3dκ σ(a)} T(a)⁹` with `T(a)` the sum of `1 + Λ` over the ball of radius
`3dκ σ(a)` around `a`. -/
theorem stepTwoWeight_le_weightMajorant {ω : Configuration d} (hP : PartitionEvent ω)
    {κ : ℕ} {i : Fin d} {Λ : Vertex d → Configuration d → ℝ}
    (hΛ0 : ∀ z, 0 ≤ Λ z ω) (hGΛ : ∀ z, planeGrad hG hGv i ω z ≤ 1 + Λ z ω) (u : Vertex d) :
    stepTwoWeight hG hGv κ i ω u ≤ weightMajorant Λ (3 * d * κ) (3 * d * κ) u ω := by
  unfold stepTwoWeight weightMajorant
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hu : u ∈ stepTwoBox κ ω a
  swap
  · rw [if_neg hu]; positivity
  rw [if_pos hu]
  have hm := max_partSide_le hP a
  have hσ := stoppingSize_eq_partSide hP a.1
  set s := partSide ω a.1 with hs
  -- the box of the edge and the box of radius `3κ s`
  have hRle : stepTwoRadius κ ω a ≤ 3 * κ * s := by
    unfold stepTwoRadius
    calc κ * max (partSide ω a.1) (partSide ω (edgeHead a)) ≤ κ * (3 * s) :=
          Nat.mul_le_mul_left _ hm
      _ = 3 * κ * s := by ring
  set S := supBox a.1 (3 * κ * s) with hS
  have hsubB : stepTwoBox κ ω a ⊆ S := by
    rw [hS, supBox_eq_boxFinset]
    exact boxFinset_mono hRle
  have hcond : ‖latticeEuclideanEmbedding (a.1 - u)‖ ≤
      3 * d * κ * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a.1 := by
    have hu' : a.1 ∈ supBox u (3 * κ * s) := by
      rw [mem_supBox]
      intro k
      rw [abs_sub_comm]
      exact (mem_supBox.1 (hsubB hu)) k
    have h1 := norm_le_of_mem_supBox hu'
    rw [hσ]
    push_cast at h1
    linarith
  rw [if_pos hcond]
  -- the finite sum `T`
  set T : ℝ := ∑ z ∈ S, (1 + Λ z ω) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun z _ => by linarith [hΛ0 z]
  have hcardT : ((3 * κ * s : ℕ) : ℝ) ^ d ≤ T := by
    have hc : (S.card : ℝ) ≤ T := by
      calc (S.card : ℝ) = ∑ _z ∈ S, (1 : ℝ) := by simp
        _ ≤ T := Finset.sum_le_sum fun z _ => by linarith [hΛ0 z]
    refine le_trans ?_ hc
    rw [hS, card_supBox]
    push_cast
    have h0 : (0 : ℝ) ≤ 3 * κ * s := by positivity
    exact pow_le_pow_left₀ h0 (by linarith) d
  have hGsum : ∑ z ∈ stepTwoBox κ ω a, planeGrad hG hGv i ω z ≤ T :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsubB fun z _ _ => planeGrad_nonneg hG hGv i ω z).trans
      (Finset.sum_le_sum fun z _ => hGΛ z)
  have hG0 : 0 ≤ ∑ z ∈ stepTwoBox κ ω a, planeGrad hG hGv i ω z :=
    Finset.sum_nonneg fun z _ => planeGrad_nonneg hG hGv i ω z
  have hrad : (stepTwoRadius κ ω a : ℝ) ≤ 3 * κ * s := by exact_mod_cast hRle
  have hF : stepTwoFactor hG hGv κ i ω a ≤ T ^ 9 := by
    unfold stepTwoFactor
    have hr0 : (0 : ℝ) ≤ stepTwoRadius κ ω a := Nat.cast_nonneg _
    have hrd : (stepTwoRadius κ ω a : ℝ) ^ d ≤ T := by
      refine le_trans ?_ hcardT
      push_cast
      exact pow_le_pow_left₀ hr0 hrad d
    have h7 : (stepTwoRadius κ ω a : ℝ) ^ (7 * d) ≤ T ^ 7 := by
      rw [mul_comm 7 d, pow_mul]
      exact pow_le_pow_left₀ (by positivity) hrd 7
    calc (stepTwoRadius κ ω a : ℝ) ^ (7 * d) *
          (∑ z ∈ stepTwoBox κ ω a, planeGrad hG hGv i ω z) ^ 2 ≤ T ^ 7 * T ^ 2 :=
          mul_le_mul h7 (pow_le_pow_left₀ hG0 hGsum 2) (sq_nonneg _) (by positivity)
      _ = T ^ 9 := by ring
  -- the finite sum under the ball sum
  have hball : ENNReal.ofReal T ≤ stepOneBallSum Λ (3 * d * κ) a.1 ω := by
    unfold stepOneBallSum
    rw [hT, ENNReal.ofReal_sum_of_nonneg fun z _ => by linarith [hΛ0 z]]
    refine le_trans (le_of_eq ?_) (ENNReal.sum_le_tsum S)
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [if_pos]
    have h1 := norm_le_of_mem_supBox hz
    rw [hσ]
    push_cast at h1
    linarith
  calc ENNReal.ofReal (stepTwoFactor hG hGv κ i ω a) ≤ ENNReal.ofReal (T ^ 9) :=
        ENNReal.ofReal_le_ofReal hF
    _ = ENNReal.ofReal T ^ (9 : ℝ) := by
        rw [ENNReal.ofReal_pow hT0, ← ENNReal.rpow_natCast]; norm_num
    _ ≤ stepOneBallSum Λ (3 * d * κ) a.1 ω ^ (9 : ℝ) := ENNReal.rpow_le_rpow hball (by norm_num)

end Grad

end Rigidity.Corrector.GeneralDim
