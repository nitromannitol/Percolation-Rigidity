import Rigidity.Proofs.Corrector.GeneralStepTwoWeightBound
import Rigidity.Proofs.Corrector.GeneralStepRegionSummable

/-!
# The path weight of the Step 2 sum on `ℤᵈ` under ball sums

On the partition event of the good cubes of `ℤᵈ`, with `σ` the stopping size of the good cubes and
`s` the side of the partition cubes:

* `stepRegion_subset_supBox`: the anchor region of `z` (the union of the partition cubes of `z` and
  `z + e_j`) lies in the box of radius `3s(z)` around `z`; it has at most `(1 + 3^d) σ(z)^d` points
  (`card_stepRegion_le`, from `GeneralStepRegionSummable`);
* `regionWeight_le_weightMajorant`: the number `N(z)` of anchor regions through `z`, weighted by
  their sizes, is at most the majorant `Σ_a 1{|a - z| ≤ 3dσ(a)} T₀(a)⁹` with `T₀(a)` the number of
  points within `4dσ(a)` of `a`, since `(1 + 3^d) σ(a)^d ≤ T₀(a)` (`ballCount_le`);
* `pathWeight_le_ballSum`: the path weight `|R(y)| Σ_{z ∈ R(y)} c(z) N(z)` is at most
  `(1 + 3^d) σ(y)^d Σ_{|z - y| ≤ 3dσ(y)} c'(z) N'(z)` for any `c' ≥ c`;
* `planeGrad_le_of_lipschitz`: if the corrector increments at each vertex of the infinite cluster
  are at most `Λ`, the plane gradient bound is at most `1 + 2dΛ`.

This is the planar file `DarioStepTwoPathBound` on `ℤᵈ`. The anchor region of `z` is here the union
of two neighbouring partition cubes, of sides at most `3s(z)`, instead of the ninefold enlargement
of the smaller one, so the box of radius `6s(z)` and the `81σ(z)²` points of the planar region
become the box of radius `3s(z)` and `(1 + 3^d) σ(z)^d` points; the Euclidean radius of a box of
radius `r` is `d r` instead of `2r`, so the radii `12, 10` of the planar majorant become `3d, 4d`;
and the plane gradient bound sums `2d` instead of `4` increments.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open Rigidity.Poincare.GeneralDim (supBox mem_supBox card_supBox)
open scoped Classical ENNReal

variable {d : ℕ}

/-- **The anchor region lies in the box of radius `3s(z)`.** -/
theorem stepRegion_subset_supBox {ω : Configuration d} (hP : PartitionEvent ω)
    (z : Vertex d) (j : Fin d) : stepRegion ω z j ⊆ supBox z (3 * partSide ω z) := by
  intro w hw
  rw [mem_supBox]
  intro i
  push_cast
  rcases (mem_stepRegion_iff ω).1 hw with hw | hw
  · have h := abs_sub_le_of_mem_partitionCube hP hw (s := partSide ω z)
      (partSide_eq hP z).ge i
    have h0 : (0 : ℤ) ≤ partSide ω z := Nat.cast_nonneg _
    linarith
  · have hsc := (partitionCube_scales_close hP (x := z + LatticeProb.unit j) (y := z)
      fun i => (abs_sub_add_unit_le z j i).2).1
    have hs : 3 ^ (partitionCube ω (z + LatticeProb.unit j)).scale ≤ 3 * partSide ω z := by
      rw [partSide_eq hP z]
      calc 3 ^ (partitionCube ω (z + LatticeProb.unit j)).scale
          ≤ 3 ^ ((partitionCube ω z).scale + 1) := Nat.pow_le_pow_right (by norm_num) hsc
        _ = 3 * 3 ^ (partitionCube ω z).scale := by ring
    have h1 := abs_sub_le_of_mem_partitionCube hP hw hs i
    have h2 := (abs_sub_add_unit_le z j i).2
    have h3 := abs_sub_le (w i) ((z + LatticeProb.unit j) i) (z i)
    push_cast at h1
    linarith

theorem regionWeight_le {ω : Configuration d} (hP : PartitionEvent ω) (j : Fin d)
    (z : Vertex d) :
    regionWeight ω j z ≤ ∑' y, if z ∈ supBox y (3 * partSide ω y) then
      ENNReal.ofReal ((1 + 3 ^ d) * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y ^ d)
    else 0 := by
  unfold regionWeight
  refine ENNReal.tsum_le_tsum fun y => ?_
  split_ifs with h1 h2
  · rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (card_stepRegion_le hP y j)
  · exact absurd (stepRegion_subset_supBox hP y j h1) h2
  · positivity
  · exact le_rfl

/-- `(1 + 3^d) σ(y)^d` is at most the number of points within `4dσ(y)` of `y`. -/
theorem ballCount_le [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω) (y : Vertex d) :
    ENNReal.ofReal ((1 + 3 ^ d) * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y ^ d) ≤
      sizeBallSum (fun _ _ => 0) (4 * d) y ω := by
  have hσ := stoppingSize_eq_partSide hP y
  have hs1 : 1 ≤ partSide ω y := by
    rw [partSide_eq hP]; exact Nat.one_le_pow _ _ (by norm_num)
  have hs1' : (1 : ℝ) ≤ partSide ω y := by exact_mod_cast hs1
  have h4 : (1 : ℝ) + 3 ^ d ≤ 4 ^ d := by
    have h := pow_add_pow_le (zero_le_one : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 3) (NeZero.ne d)
    rw [one_pow] at h
    norm_num at h
    exact h
  unfold sizeBallSum
  calc ENNReal.ofReal ((1 + 3 ^ d) * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y ^ d)
      ≤ ((supBox y (4 * partSide ω y)).card : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_natCast, card_supBox, hσ]
        refine ENNReal.ofReal_le_ofReal ?_
        push_cast
        calc (1 + 3 ^ d) * (partSide ω y : ℝ) ^ d ≤ 4 ^ d * (partSide ω y : ℝ) ^ d :=
              mul_le_mul_of_nonneg_right h4 (by positivity)
          _ = (4 * (partSide ω y : ℝ)) ^ d := (mul_pow _ _ _).symm
          _ ≤ (2 * (4 * (partSide ω y : ℝ)) + 1) ^ d :=
              pow_le_pow_left₀ (by positivity) (by linarith) d
    _ = ∑ w ∈ supBox y (4 * partSide ω y),
          (if ‖latticeEuclideanEmbedding (w - y)‖ ≤
              4 * d * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y then
            ENNReal.ofReal (1 + (fun (_ : Vertex d) (_ : Configuration d) => (0 : ℝ)) w ω)
          else 0) := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        refine Finset.sum_congr rfl fun w hw => ?_
        have h1 := norm_le_of_mem_supBox hw
        rw [if_pos (by rw [hσ]; push_cast at h1; linarith)]
        simp
    _ ≤ _ := ENNReal.sum_le_tsum _

/-- **The weighted number of anchor regions through `z` under the majorant.** -/
theorem regionWeight_le_weightMajorant [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω)
    (j : Fin d) (z : Vertex d) :
    regionWeight ω j z ≤ weightMajorant (fun _ _ => 0) (3 * d) (4 * d) z ω := by
  set g : LatticeEdge d → ℝ≥0∞ := fun a =>
    if ‖latticeEuclideanEmbedding (a.1 - z)‖ ≤
        3 * d * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) a.1 then
      sizeBallSum (fun _ _ => 0) (4 * d) a.1 ω ^ (9 : ℝ) else 0 with hg
  refine (regionWeight_le hP j z).trans ?_
  calc (∑' y, if z ∈ supBox y (3 * partSide ω y) then
        ENNReal.ofReal ((1 + 3 ^ d) * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y ^ d)
      else 0)
      ≤ ∑' y, ∑' k : Fin d, g (y, k) := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        split_ifs with h
        · have hc : ‖latticeEuclideanEmbedding (y - z)‖ ≤
              3 * d * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y := by
            have h1 := (norm_sub_le_of_mem_supBox h).2
            rw [stoppingSize_eq_partSide hP]
            push_cast at h1
            linarith
          have hb1 : 1 ≤ sizeBallSum (fun _ _ => 0) (4 * d) y ω := by
            refine le_trans ?_ (ballCount_le hP y)
            rw [← ENNReal.ofReal_one]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [stoppingSize_eq_partSide hP]
            have hs1 : 1 ≤ partSide ω y := by
              rw [partSide_eq hP]; exact Nat.one_le_pow _ _ (by norm_num)
            have hs1' : (1 : ℝ) ≤ partSide ω y := by exact_mod_cast hs1
            have h3 : (1 : ℝ) ≤ 1 + 3 ^ d := le_add_of_nonneg_right (by positivity)
            exact one_le_mul_of_one_le_of_one_le h3 (one_le_pow₀ hs1')
          refine le_trans ?_ (ENNReal.le_tsum (0 : Fin d))
          simp only [hg, if_pos hc]
          calc ENNReal.ofReal
                ((1 + 3 ^ d) * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y ^ d)
              ≤ sizeBallSum (fun _ _ => 0) (4 * d) y ω := ballCount_le hP y
            _ = sizeBallSum (fun _ _ => 0) (4 * d) y ω ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
            _ ≤ sizeBallSum (fun _ _ => 0) (4 * d) y ω ^ (9 : ℝ) :=
                ENNReal.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
        · positivity
    _ = ∑' a : LatticeEdge d, g a := (ENNReal.tsum_prod (f := fun v k => g (v, k))).symm
    _ = weightMajorant (fun _ _ => 0) (3 * d) (4 * d) z ω := rfl

/-- **The path weight under a ball sum.** -/
theorem pathWeight_le_ballSum [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω)
    {c : Vertex d → ℝ} {c' : Vertex d → ℝ≥0∞} (hc : ∀ z, ENNReal.ofReal (c z) ≤ c' z)
    (j : Fin d) (y : Vertex d) :
    pathWeight c ω j y ≤
      ENNReal.ofReal ((1 + 3 ^ d) * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y ^ d) *
        ∑' z, if ‖latticeEuclideanEmbedding (z - y)‖ ≤
            3 * d * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y then
          c' z * weightMajorant (fun _ _ => 0) (3 * d) (4 * d) z ω else 0 := by
  unfold pathWeight
  refine mul_le_mul' ?_ ?_
  · rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (card_stepRegion_le hP y j)
  · calc ∑ z ∈ stepRegion ω y j, ENNReal.ofReal (c z) * regionWeight ω j z
        ≤ ∑ z ∈ stepRegion ω y j, (if ‖latticeEuclideanEmbedding (z - y)‖ ≤
            3 * d * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y then
          c' z * weightMajorant (fun _ _ => 0) (3 * d) (4 * d) z ω else 0) :=
          Finset.sum_le_sum fun z hz => by
            have h1 := norm_le_of_mem_supBox (stepRegion_subset_supBox hP y j hz)
            rw [if_pos (by rw [stoppingSize_eq_partSide hP]; push_cast at h1; linarith)]
            exact mul_le_mul' (hc z) (regionWeight_le_weightMajorant hP j z)
      _ ≤ _ := ENNReal.sum_le_tsum _

section Grad

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- **The plane gradient bound under a bound of the corrector increments.** -/
theorem planeGrad_le_of_lipschitz {ω : Configuration d} {i : Fin d} {Λ : Vertex d → ℝ}
    (hΛ0 : ∀ z, 0 ≤ Λ z)
    (hlip : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ x) (z : Vertex d) :
    planeGrad hG hGv i ω z ≤ 1 + 2 * d * Λ z := by
  have key : ∀ y, (openGraph ω).Adj z y →
      |correctorDiff hG hGv (Pi.single i 1) ω z y| ≤ Λ z := by
    intro y hy
    by_cases hz : ω ∈ infiniteComponentEvent z
    · exact hlip z hz y hy
    · have hy' : ω ∉ infiniteComponentEvent y := fun h =>
        hz (mem_infiniteComponentEvent_of_adj hy.symm h)
      have : correctorDiff hG hGv (Pi.single i 1) ω z y = 0 := by
        unfold correctorDiff
        rw [dif_neg fun h => hy' h.2]
      rw [this, abs_zero]
      exact hΛ0 z
  have t : ∀ k : Fin d, (if EdgeOpen ω (z, k) then
      |correctorDiff hG hGv (Pi.single i 1) ω z (z + LatticeProb.unit k)| else 0) ≤ Λ z := by
    intro k
    split_ifs with h
    · exact key (z + LatticeProb.unit k) h
    · exact hΛ0 z
  have t' : ∀ k : Fin d, (if EdgeOpen ω (z - LatticeProb.unit k, k) then
      |correctorDiff hG hGv (Pi.single i 1) ω z (z - LatticeProb.unit k)| else 0) ≤ Λ z := by
    intro k
    split_ifs with h
    · have hadj : (openGraph ω).Adj z (z - LatticeProb.unit k) := by
        have : (openGraph ω).Adj (z - LatticeProb.unit k)
            (z - LatticeProb.unit k + LatticeProb.unit k) := h
        rw [sub_add_cancel] at this
        exact this.symm
      exact key _ hadj
    · exact hΛ0 z
  unfold planeGrad
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
    fun k (_ : k ∈ Finset.univ) =>
    add_le_add (t k) (t' k)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith

end Grad

end Rigidity.Corrector.GeneralDim
