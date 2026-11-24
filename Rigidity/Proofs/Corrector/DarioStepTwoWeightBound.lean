import Rigidity.Proofs.Corrector.DarioStepTwoWeightMoments

/-!
# The weight of the Step 2 sum under its majorant

On the planar partition event, the sides at the two endpoints of an edge differ by at most a
factor `3`, so `m_a = max(s(x), s(y)) ≤ 3 s(x)` (`max_planarSide_le`). If the plane gradient
bound satisfies `G ≤ 1 + Λ`, the factor `F_a = (κ m_a)¹⁴ (Σ_{B_a} G)²` of the weight is at most
`T⁹` for the sum `T` of `1 + Λ` over the box of radius `3κ s(x)`, which has at least
`(3κ s(x))²` points and lies in the Euclidean ball of radius `6κ s(x)`. Hence
(`stepTwoWeight_le_weightMajorant`)

`W(u) ≤ Σ_a 1{|a - u| ≤ 6κ σ(a)} T(a)⁹ = weightMajorant Λ (6κ) (6κ) u`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

theorem planarSide_head_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω) (a : LatticeEdge) :
    planarSide ω (edgeHead a) ≤ 3 * planarSide ω a.1 := by
  rw [planarSide_eq hP, planarSide_eq hP]
  have h := (planarPartCube_scales_close hP (x := edgeHead a) (y := a.1) fun i => by
    rw [abs_sub_comm]; exact abs_sub_edgeHead_le a i).1
  calc 3 ^ (planarPartCube ω (edgeHead a)).scale ≤ 3 ^ ((planarPartCube ω a.1).scale + 1) :=
        Nat.pow_le_pow_right (by norm_num) h
    _ = 3 * 3 ^ (planarPartCube ω a.1).scale := by ring

theorem max_planarSide_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω) (a : LatticeEdge) :
    max (planarSide ω a.1) (planarSide ω (edgeHead a)) ≤ 3 * planarSide ω a.1 :=
  max_le (by omega) (planarSide_head_le hP a)

theorem stoppingSize_eq_planarSide {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (v : Vertex 2) : TriadicCube.stoppingSize (planarGoodCubes ω) v = (planarSide ω v : ℝ) := by
  rw [planarSide_eq hP, TriadicCube.stoppingSize_eq_of_mem (planarPartCube_spec hP _).1
    (planarPartCube_spec hP _).2]
  push_cast
  rfl

theorem norm_le_of_mem_supBox {x z : Vertex 2} {r : ℕ} (h : z ∈ supBox x r) :
    ‖latticeEuclideanEmbedding (z - x)‖ ≤ 2 * r := by
  have h1 := norm_latticeEuclideanEmbedding_le_sum (z - x)
  have h0 := (mem_supBox.1 h) 0
  have h1' := (mem_supBox.1 h) 1
  have a0 : |(((z - x) 0 : ℤ) : ℝ)| ≤ r := by
    simp only [Pi.sub_apply]; exact_mod_cast h0
  have a1 : |(((z - x) 1 : ℤ) : ℝ)| ≤ r := by
    simp only [Pi.sub_apply]; exact_mod_cast h1'
  linarith

section Grad

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **The weight under its majorant.** -/
theorem stepTwoWeight_le_weightMajorant {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {κ : ℕ} {i : Fin 2} {Λ : Vertex 2 → Configuration 2 → ℝ}
    (hΛ0 : ∀ z, 0 ≤ Λ z ω) (hGΛ : ∀ z, planeGrad hG hGv i ω z ≤ 1 + Λ z ω) (u : Vertex 2) :
    stepTwoWeight hG hGv κ i ω u ≤ weightMajorant Λ (6 * κ) (6 * κ) u ω := by
  unfold stepTwoWeight weightMajorant
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hu : u ∈ stepTwoBox κ ω a
  swap
  · rw [if_neg hu]; positivity
  rw [if_pos hu]
  set s := planarSide ω a.1 with hs
  have hs1 : 1 ≤ s := by rw [hs, planarSide_eq hP]; exact Nat.one_le_pow _ _ (by norm_num)
  have hm := max_planarSide_le hP a
  have hσ := stoppingSize_eq_planarSide hP a.1
  -- the box of the edge and the box of radius `3κ s`
  set S := supBox a.1 (3 * κ * s) with hS
  have hsubB : stepTwoBox κ ω a ⊆ S := by
    unfold stepTwoBox stepTwoRadius
    refine supBox_mono ?_
    rw [← hs]
    calc κ * max (planarSide ω a.1) (planarSide ω (edgeHead a)) ≤ κ * (3 * s) :=
          Nat.mul_le_mul_left _ hm
      _ = 3 * κ * s := by ring
  have hcond : ‖latticeEuclideanEmbedding (a.1 - u)‖ ≤
      (6 * κ : ℝ) * TriadicCube.stoppingSize (planarGoodCubes ω) a.1 := by
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
  have hcardT : ((3 * κ * s : ℕ) : ℝ) ^ 2 ≤ T := by
    have hc : (S.card : ℝ) ≤ T := by
      calc (S.card : ℝ) = ∑ _z ∈ S, (1 : ℝ) := by simp
        _ ≤ T := Finset.sum_le_sum fun z _ => by linarith [hΛ0 z]
    refine le_trans ?_ hc
    rw [hS, card_supBox]
    push_cast
    nlinarith
  have hGsum : ∑ z ∈ stepTwoBox κ ω a, planeGrad hG hGv i ω z ≤ T :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsubB fun z _ _ => planeGrad_nonneg hG hGv i ω z).trans
      (Finset.sum_le_sum fun z _ => hGΛ z)
  have hG0 : 0 ≤ ∑ z ∈ stepTwoBox κ ω a, planeGrad hG hGv i ω z :=
    Finset.sum_nonneg fun z _ => planeGrad_nonneg hG hGv i ω z
  have hrad : (stepTwoRadius κ ω a : ℝ) ≤ 3 * κ * s := by
    unfold stepTwoRadius
    rw [← hs]
    have : κ * max (planarSide ω a.1) (planarSide ω (edgeHead a)) ≤ 3 * κ * s := by
      calc κ * max (planarSide ω a.1) (planarSide ω (edgeHead a)) ≤ κ * (3 * s) :=
            Nat.mul_le_mul_left _ hm
        _ = 3 * κ * s := by ring
    exact_mod_cast this
  have hF : stepTwoFactor hG hGv κ i ω a ≤ T ^ 9 := by
    unfold stepTwoFactor
    have h14 : (stepTwoRadius κ ω a : ℝ) ^ 14 ≤ T ^ 7 := by
      have hr0 : (0 : ℝ) ≤ stepTwoRadius κ ω a := Nat.cast_nonneg _
      have hr2 : (stepTwoRadius κ ω a : ℝ) ^ 2 ≤ T := by
        refine le_trans ?_ hcardT
        push_cast
        exact pow_le_pow_left₀ hr0 hrad 2
      calc (stepTwoRadius κ ω a : ℝ) ^ 14 = ((stepTwoRadius κ ω a : ℝ) ^ 2) ^ 7 := by ring
        _ ≤ T ^ 7 := pow_le_pow_left₀ (by positivity) hr2 7
    calc (stepTwoRadius κ ω a : ℝ) ^ 14 *
          (∑ z ∈ stepTwoBox κ ω a, planeGrad hG hGv i ω z) ^ 2 ≤ T ^ 7 * T ^ 2 :=
          mul_le_mul h14 (pow_le_pow_left₀ hG0 hGsum 2) (sq_nonneg _) (by positivity)
      _ = T ^ 9 := by ring
  -- the finite sum under the ball sum
  have hball : ENNReal.ofReal T ≤ stepOneBallSum Λ (6 * κ) a.1 ω := by
    unfold stepOneBallSum
    rw [hT, ENNReal.ofReal_sum_of_nonneg fun z _ => by linarith [hΛ0 z]]
    refine le_trans (le_of_eq ?_) (ENNReal.sum_le_tsum S)
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [if_pos]
    have h1 := norm_le_of_mem_supBox hz
    rw [hσ]
    push_cast at h1
    have : (2 : ℝ) * (3 * κ * s) ≤ 6 * κ * s := by ring_nf; exact le_rfl
    linarith
  calc ENNReal.ofReal (stepTwoFactor hG hGv κ i ω a) ≤ ENNReal.ofReal (T ^ 9) :=
        ENNReal.ofReal_le_ofReal hF
    _ = ENNReal.ofReal T ^ (9 : ℝ) := by
        rw [ENNReal.ofReal_pow hT0, ← ENNReal.rpow_natCast]; norm_num
    _ ≤ stepOneBallSum Λ (6 * κ) a.1 ω ^ (9 : ℝ) := ENNReal.rpow_le_rpow hball (by norm_num)

end Grad

end Rigidity.Corrector
