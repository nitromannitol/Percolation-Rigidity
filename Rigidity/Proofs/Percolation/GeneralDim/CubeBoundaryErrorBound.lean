import Rigidity.Proofs.Percolation.GeneralDim.CubeNablaAffine
import Rigidity.Proofs.Percolation.GeneralDim.CubeMuUpperBound

/-!
# The boundary error of the coarsened gradient of the `ν` maximizer, in `ℤ^d`

The variation part of the boundary error of `CubeNablaAffine` is a weighted variation over the
open edges of the cluster `C_*(U)`, with weight `W_∂(z)` the number of vertices of the faces of
`U` (counted once per face) whose partition cube has `z` in its crossing cluster. By the
Cauchy–Schwarz inequality, a vertex having at most `3^d` open neighbours, and Young's inequality
with a free parameter `τ > 0`, it is at most `(3^d ∑_z W_∂(z)² / τ + 2 τ B(v, v)) / 2`
(Armstrong and Dario, proof of Lemma 4.5, the Hölder step in the proof of (4.27), with the sum
over the boundary partition cubes written through the weight `W_∂`).
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The number of vertices of the faces of `U`, counted once per face, whose partition cube has
`z` in its crossing cluster. -/
noncomputable def cubeBoundaryWeight (ω : Configuration d) (U : TriadicCube d) (z : Vertex d) :
    ℝ :=
  ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i,
      (if z ∈ crossingClusterVertices ω (partitionCube ω x) then (1 : ℝ) else 0) +
    ∑ x ∈ U.toIntegerCube.lowerFace i,
      (if z ∈ crossingClusterVertices ω (partitionCube ω x) then (1 : ℝ) else 0))

theorem cubeBoundaryWeight_nonneg (ω : Configuration d) (U : TriadicCube d) (z : Vertex d) :
    0 ≤ cubeBoundaryWeight ω U z :=
  Finset.sum_nonneg fun _ _ => add_nonneg
    (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
    (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)

/-- **Young's inequality from a Cauchy–Schwarz bound.** -/
theorem le_half_div_add_mul_of_sq_le {X M N τ : ℝ} (hX : 0 ≤ X) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hτ : 0 < τ) (h : X ^ 2 ≤ M * N) : X ≤ (M / τ + τ * N) / 2 := by
  have hS : 0 ≤ M + τ ^ 2 * N := by positivity
  have h1 : 4 * τ ^ 2 * (M * N) ≤ (M + τ ^ 2 * N) ^ 2 := by
    nlinarith [sq_nonneg (M - τ ^ 2 * N)]
  have h2 : (2 * τ * X) ^ 2 ≤ 4 * τ ^ 2 * (M * N) := by
    have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 4 * τ ^ 2)
    nlinarith
  have key : 2 * τ * X ≤ M + τ ^ 2 * N :=
    (pow_le_pow_iff_left₀ (by positivity) hS two_ne_zero).1 (h2.trans h1)
  have e : M / τ + τ * N = (M + τ ^ 2 * N) / τ := by
    field_simp
  rw [e, le_div_iff₀ two_pos, le_div_iff₀ hτ]
  linarith

/-- The variations over the crossing clusters of the boundary partition cubes add up to the
variation over the open edges of the cluster weighted by `W_∂`. -/
theorem sum_faces_partitionCubeVariation_le (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (f : Vertex d → ℝ) :
    ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i, partitionCubeVariation ω f x +
      ∑ x ∈ U.toIntegerCube.lowerFace i, partitionCubeVariation ω f x) ≤
    ∑ z ∈ crossingClusterVertices ω U, ∑ y ∈ crossingClusterVertices ω U,
      (if (openGraph ω).Adj z y then cubeBoundaryWeight ω U z * |f z - f y| else 0) := by
  set C := crossingClusterVertices ω U
  set A : Vertex d → ℝ := fun z => ∑ y ∈ C, if (openGraph ω).Adj z y then |f z - f y| else 0
    with hA
  set I : Vertex d → Vertex d → ℝ := fun x z =>
    if z ∈ crossingClusterVertices ω (partitionCube ω x) then (1 : ℝ) else 0 with hI
  have hA0 : ∀ z, 0 ≤ A z := fun z => Finset.sum_nonneg fun y _ => by
    split_ifs <;> positivity
  have hx : ∀ x ∈ U.toIntegerCube.vertices,
      partitionCubeVariation ω f x ≤ ∑ z ∈ C, I x z * A z := by
    intro x hxU
    have hxU' := (U.mem_toIntegerCube_vertices x).1 hxU
    have hsub : crossingClusterVertices ω (partitionCube ω x) ⊆ C := by
      intro z hz
      exact mem_crossingClusterVertices.2 (crossingCluster_partitionCube_subset hd hP hxU'
        (hU x hxU') (mem_crossingClusterVertices.1 hz))
    unfold partitionCubeVariation
    calc ∑ z ∈ crossingClusterVertices ω (partitionCube ω x),
          vertexVariation ω (crossingClusterVertices ω (partitionCube ω x)) f z
        ≤ ∑ z ∈ crossingClusterVertices ω (partitionCube ω x), A z :=
          Finset.sum_le_sum fun z _ => vertexVariation_mono ω hsub f z
      _ = ∑ z ∈ C, I x z * A z := by
          rw [← Finset.inter_eq_right.2 hsub, ← Finset.sum_ite_mem C]
          refine Finset.sum_congr rfl fun z _ => ?_
          simp only [hI]
          split_ifs <;> simp
  have hface : ∀ F : Finset (Vertex d), F ⊆ U.toIntegerCube.vertices →
      ∑ x ∈ F, partitionCubeVariation ω f x ≤ ∑ z ∈ C, (∑ x ∈ F, I x z) * A z := by
    intro F hF
    calc ∑ x ∈ F, partitionCubeVariation ω f x ≤ ∑ x ∈ F, ∑ z ∈ C, I x z * A z :=
          Finset.sum_le_sum fun x hx' => hx x (hF hx')
      _ = ∑ z ∈ C, (∑ x ∈ F, I x z) * A z := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_mul]
  have hup : ∀ i, U.toIntegerCube.upperFace i ⊆ U.toIntegerCube.vertices := fun i =>
    Finset.filter_subset _ _
  have hlow : ∀ i, U.toIntegerCube.lowerFace i ⊆ U.toIntegerCube.vertices := fun i =>
    Finset.filter_subset _ _
  calc ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i, partitionCubeVariation ω f x +
        ∑ x ∈ U.toIntegerCube.lowerFace i, partitionCubeVariation ω f x)
      ≤ ∑ i, (∑ z ∈ C, (∑ x ∈ U.toIntegerCube.upperFace i, I x z) * A z +
          ∑ z ∈ C, (∑ x ∈ U.toIntegerCube.lowerFace i, I x z) * A z) :=
        Finset.sum_le_sum fun i _ => add_le_add (hface _ (hup i)) (hface _ (hlow i))
    _ = ∑ z ∈ C, cubeBoundaryWeight ω U z * A z := by
        simp only [← Finset.sum_add_distrib, ← add_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← Finset.sum_mul]
        rfl
    _ = _ := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> simp

/-- **Bound on the boundary error** (Armstrong and Dario, proof of Lemma 4.5, (4.27)). For every
`τ > 0`, the boundary error of a function `v` on the cluster is at most the sides of the boundary
partition cubes, times `|p|₁`, plus `(3^d ∑_z W_∂(z)² / τ + 2 τ B(v, v)) / 2`. -/
theorem cubeBoundaryError_le (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (p : Fin d → ℝ) (v : CubeFun ω U) {τ : ℝ} (hτ : 0 < τ) :
    cubeBoundaryError ω U p v ≤
      ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i, (∑ j, |p j|) * 3 ^ (partitionCube ω x).scale +
        ∑ x ∈ U.toIntegerCube.lowerFace i, (∑ j, |p j|) * 3 ^ (partitionCube ω x).scale) +
      ((3 ^ d * ∑ z ∈ crossingClusterVertices ω U, cubeBoundaryWeight ω U z ^ 2) / τ +
        τ * (2 * cubeForm ω U v v)) / 2 := by
  set C := crossingClusterVertices ω U
  set f := cubeExtend ω U v
  set W := cubeBoundaryWeight ω U
  set X := ∑ z ∈ C, ∑ y ∈ C, (if (openGraph ω).Adj z y then W z * |f z - f y| else 0)
  have hvar : ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i, partitionCubeVariation ω f x +
      ∑ x ∈ U.toIntegerCube.lowerFace i, partitionCubeVariation ω f x) ≤ X :=
    sum_faces_partitionCubeVariation_le hd hP hU f
  have hsplit : cubeBoundaryError ω U p v =
      ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i, partitionCubeVariation ω f x +
        ∑ x ∈ U.toIntegerCube.lowerFace i, partitionCubeVariation ω f x) +
      ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i, (∑ j, |p j|) * 3 ^ (partitionCube ω x).scale +
        ∑ x ∈ U.toIntegerCube.lowerFace i, (∑ j, |p j|) * 3 ^ (partitionCube ω x).scale) := by
    rw [cubeBoundaryError, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring
  -- Cauchy–Schwarz over the ordered pairs of open neighbours
  set F : Vertex d × Vertex d → ℝ := fun e => if (openGraph ω).Adj e.1 e.2 then W e.1 else 0
  set G : Vertex d × Vertex d → ℝ := fun e =>
    if (openGraph ω).Adj e.1 e.2 then |f e.1 - f e.2| else 0
  have hXFG : X = ∑ e ∈ C ×ˢ C, F e * G e := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [F, G]
    split_ifs <;> simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (C ×ˢ C) F G
  have hG2 : ∑ e ∈ C ×ˢ C, G e ^ 2 = 2 * cubeForm ω U v v := by
    rw [cubeForm_self_eq_sum, Finset.sum_product]
    rw [show (2 : ℝ) * ((1 / 2) * ∑ x ∈ C, ∑ y ∈ C, (if (openGraph ω).Adj x y then
        (f x - f y) * (f x - f y) else 0)) = ∑ x ∈ C, ∑ y ∈ C, (if (openGraph ω).Adj x y then
        (f x - f y) * (f x - f y) else 0) by ring]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [G]
    split_ifs
    · rw [sq_abs, sq]
    · simp
  have hF2 : ∑ e ∈ C ×ˢ C, F e ^ 2 ≤ 3 ^ d * ∑ z ∈ C, W z ^ 2 := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    have hrow : ∑ y ∈ C, F (z, y) ^ 2 = ((C.filter fun y => (openGraph ω).Adj z y).card : ℝ) *
        W z ^ 2 := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [F]
      split_ifs <;> simp
    rw [hrow]
    have hcard := card_filter_openGraph_adj_le (ω := ω) C z
    have hcard' : ((C.filter fun y => (openGraph ω).Adj z y).card : ℝ) ≤ 3 ^ d := by
      exact_mod_cast hcard
    exact mul_le_mul_of_nonneg_right hcard' (sq_nonneg _)
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun y _ => by
    split_ifs
    · exact mul_nonneg (cubeBoundaryWeight_nonneg _ _ _) (abs_nonneg _)
    · exact le_rfl
  have hM0 : 0 ≤ 3 ^ d * ∑ z ∈ C, W z ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hN0 : 0 ≤ 2 * cubeForm ω U v v := mul_nonneg (by norm_num) (cubeForm_self_nonneg v)
  have hsq : X ^ 2 ≤ (3 ^ d * ∑ z ∈ C, W z ^ 2) * (2 * cubeForm ω U v v) := by
    rw [hXFG]
    calc (∑ e ∈ C ×ˢ C, F e * G e) ^ 2
        ≤ (∑ e ∈ C ×ˢ C, F e ^ 2) * ∑ e ∈ C ×ˢ C, G e ^ 2 := hcs
      _ ≤ (3 ^ d * ∑ z ∈ C, W z ^ 2) * (2 * cubeForm ω U v v) := by
          rw [hG2]
          exact mul_le_mul_of_nonneg_right hF2 hN0
  have hY := le_half_div_add_mul_of_sq_le hX0 hM0 hN0 hτ hsq
  rw [hsplit]
  linarith

end Rigidity.Percolation
