import Rigidity.Proofs.Regularity.PlanarCorrectorSupBound

/-!
# The density of the cluster in the balls around the vertices of a box

From the density of the cluster in the triadic cubes inside the balls `B_{54 · 3^m}` around the
origin (`ClusterCubeDensity C 0 54 ℓ κ`), every ball `B_{9 · 3^m}(x)` with `|x_i| ≤ 27 · 3^m`
carries at least `κ 9^m` vertices of the cluster (`card_componentEuclideanBall_ge`): it contains the
triadic cube of scale `m` nearest to `x`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.S2
open Rigidity.External
open scoped Classical

variable {ω : Configuration 2}

/-- The index of the triadic cube of scale `m` containing `x`. -/
noncomputable def nearIndex (m : ℕ) (x : Vertex 2) : Vertex 2 :=
  fun i => (x i + ((3 : ℤ) ^ m - 1) / 2) / 3 ^ m

theorem two_mul_abs_sub_nearIndex_lt (m : ℕ) (x : Vertex 2) (i : Fin 2) :
    2 * |x i - 3 ^ m * nearIndex m x i| < 3 ^ m := by
  have ho : (3 : ℤ) ^ m % 2 = 1 := Int.odd_iff.mp (Odd.pow ⟨1, by norm_num⟩)
  have hT : (0 : ℤ) < 3 ^ m := by positivity
  have hd := Int.emod_add_mul_ediv (x i + ((3 : ℤ) ^ m - 1) / 2) (3 ^ m)
  have h0 := Int.emod_nonneg (x i + ((3 : ℤ) ^ m - 1) / 2) hT.ne'
  have h1 := Int.emod_lt_of_pos (x i + ((3 : ℤ) ^ m - 1) / 2) hT
  have hh := Int.emod_add_mul_ediv ((3 : ℤ) ^ m) 2
  unfold nearIndex
  generalize (x i + ((3 : ℤ) ^ m - 1) / 2) % 3 ^ m = r at hd h0 h1
  generalize 3 ^ m * ((x i + ((3 : ℤ) ^ m - 1) / 2) / 3 ^ m) = P at hd ⊢
  rcases abs_cases (x i - P) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

/-- **The cluster carries a fixed proportion of the balls around the vertices of a box.** -/
theorem card_componentEuclideanBall_ge (C : OpenComponent ω) {ℓ κ : ℝ}
    (hcube : ClusterCubeDensity C 0 54 ℓ κ) {m : ℕ} (hm : ℓ ≤ 3 ^ m) {x : Vertex 2}
    (hx : ∀ i, |x i| ≤ 27 * 3 ^ m) :
    κ * 9 ^ m ≤ (componentEuclideanBall C x (9 * 3 ^ m)).card := by
  have hT : (0 : ℝ) < 3 ^ m := by positivity
  have hnear : ∀ i, |((x i : ℤ) : ℝ) - 3 ^ m * ((nearIndex m x i : ℤ) : ℝ)| < 3 ^ m / 2 := by
    intro i
    have h := two_mul_abs_sub_nearIndex_lt m x i
    have h' : ((2 * |x i - 3 ^ m * nearIndex m x i| : ℤ) : ℝ) < (((3 : ℤ) ^ m : ℤ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    linarith
  have hcubeY : ∀ y ∈ triadicCube 2 m (nearIndex m x), ∀ i,
      |((y i : ℤ) : ℝ) - ((x i : ℤ) : ℝ)| ≤ 3 ^ m := by
    intro y hy i
    have h1 : |((y i : ℤ) : ℝ) - 3 ^ m * ((nearIndex m x i : ℤ) : ℝ)| < 3 ^ m / 2 := hy i
    have h2 := hnear i
    have a := abs_sub_le ((y i : ℤ) : ℝ) (3 ^ m * ((nearIndex m x i : ℤ) : ℝ)) ((x i : ℤ) : ℝ)
    rw [abs_sub_comm (3 ^ m * ((nearIndex m x i : ℤ) : ℝ)) ((x i : ℤ) : ℝ)] at a
    linarith
  have hin : ∀ y ∈ triadicCube 2 m (nearIndex m x),
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) <
        54 * 3 ^ m := by
    intro y hy
    have hy0 : ∀ i, |((y i : ℤ) : ℝ) - latticeEuclideanEmbedding (0 : Vertex 2) i| ≤ 28 * 3 ^ m := by
      intro i
      have e : latticeEuclideanEmbedding (0 : Vertex 2) i = 0 := by
        simp [latticeEuclideanEmbedding]
      rw [e, sub_zero]
      have h1 := hcubeY y hy i
      have h2 : |((x i : ℤ) : ℝ)| ≤ 27 * 3 ^ m := by
        have := hx i
        have h' : ((|x i| : ℤ) : ℝ) ≤ ((27 * 3 ^ m : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at h'
        exact h'
      have a := abs_sub_abs_le_abs_sub ((y i : ℤ) : ℝ) ((x i : ℤ) : ℝ)
      linarith
    have hd := dist_latticeEuclideanEmbedding_le (by positivity) hy0
    have hs : Real.sqrt ((2 : ℕ) : ℝ) ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    calc dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2))
        ≤ Real.sqrt ((2 : ℕ) : ℝ) * (28 * 3 ^ m) := hd
      _ ≤ 3 / 2 * (28 * 3 ^ m) := mul_le_mul_of_nonneg_right hs (by positivity)
      _ < 54 * 3 ^ m := by linarith
  have h := hcube m (nearIndex m x) hm hin
  have hle : (clusterCubePoints C 0 (54 * 3 ^ m) m (nearIndex m x)).card ≤
      (componentEuclideanBall C x (9 * 3 ^ m)).card := by
    refine Finset.card_le_card fun y hy => ?_
    simp only [clusterCubePoints, mem_filter] at hy
    rw [mem_componentEuclideanBall]
    have hy' : y.val ∈ triadicCube 2 m (nearIndex m x) := fun i => hy.2 i
    have hxy : ∀ i, |((y.val i : ℤ) : ℝ) - latticeEuclideanEmbedding x i| ≤ 3 ^ m := by
      intro i
      exact hcubeY y.val hy' i
    have hd := dist_latticeEuclideanEmbedding_le (by positivity) hxy
    have hs : Real.sqrt ((2 : ℕ) : ℝ) ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    calc dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x)
        ≤ Real.sqrt ((2 : ℕ) : ℝ) * 3 ^ m := hd
      _ ≤ 3 / 2 * 3 ^ m := mul_le_mul_of_nonneg_right hs (by positivity)
      _ < 9 * 3 ^ m := by linarith
  calc κ * 9 ^ m = κ * 3 ^ (2 * m) := by rw [pow_mul]; norm_num
    _ ≤ _ := h
    _ ≤ _ := by exact_mod_cast hle

end Rigidity.Proofs.Regularity
