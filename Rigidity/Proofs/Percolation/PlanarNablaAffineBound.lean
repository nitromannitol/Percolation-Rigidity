import Rigidity.Proofs.Percolation.PlanarNablaAffine

/-!
# Boundary error for the coarsened gradient of the `ν` maximizer

The variation part of the boundary error is a weighted variation over the open edges of the
cluster, with weight `W_∂(a)` the number of boundary vertices of `U` (counted once per face) whose
window contains `a`. By the Cauchy–Schwarz inequality and Young's inequality with a free
parameter `t > 0`, it is at most `(9 ∑ W_∂² / t + 2 t B v v) / 2`.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- **Cauchy–Schwarz** for variations weighted by a function of the first vertex. -/
theorem sum_adj_abs_mul_sq_le {U : TriadicCube 2} (u : ClusterFun ω U)
    (W : ↥(clusterVertices ω U) → ℝ) :
    (∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
        (if (openGraph ω).Adj x.1 y.1 then |u x - u y| else 0) * W x) ^ 2 ≤
      (∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
        (if (openGraph ω).Adj x.1 y.1 then W x ^ 2 else 0)) * (2 * clusterForm ω U u u) := by
  rw [two_mul_clusterForm_self]
  simp only [← Finset.sum_product']
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ ×ˢ Finset.univ)
    (fun p : ↥(clusterVertices ω U) × ↥(clusterVertices ω U) =>
      if (openGraph ω).Adj p.1.1 p.2.1 then W p.1 else 0)
    (fun p : ↥(clusterVertices ω U) × ↥(clusterVertices ω U) =>
      if (openGraph ω).Adj p.1.1 p.2.1 then |u p.1 - u p.2| else 0)
  have e1 : ∀ p : ↥(clusterVertices ω U) × ↥(clusterVertices ω U),
      (if (openGraph ω).Adj p.1.1 p.2.1 then |u p.1 - u p.2| else 0) * W p.1 =
      (if (openGraph ω).Adj p.1.1 p.2.1 then W p.1 else 0) *
        (if (openGraph ω).Adj p.1.1 p.2.1 then |u p.1 - u p.2| else 0) := by
    intro p
    split_ifs <;> ring
  have e2 : ∀ p : ↥(clusterVertices ω U) × ↥(clusterVertices ω U),
      (if (openGraph ω).Adj p.1.1 p.2.1 then W p.1 ^ 2 else 0) =
      (if (openGraph ω).Adj p.1.1 p.2.1 then W p.1 else 0) ^ 2 := by
    intro p
    split_ifs <;> simp
  simp only [e1, e2]
  exact hcs

/-- The boundary weight: the number of boundary vertices of `U`, counted once per face, whose
window contains `a`. -/
noncomputable def boundaryWeight (ω : Configuration 2) (U : TriadicCube 2) (a : Vertex 2) : ℝ :=
  ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i,
      (if a ∈ planarClusterWindow ω U x then 1 else 0) +
    ∑ x ∈ U.toIntegerCube.lowerFace i, (if a ∈ planarClusterWindow ω U x then 1 else 0))

theorem planarClusterWindow_subset (U : TriadicCube 2) (x : Vertex 2) :
    planarClusterWindow ω U x ⊆ clusterVertices ω U := by
  intro a ha
  exact mem_clusterVertices.2 (Finset.mem_filter.1 ha).2

/-- The variation part of the boundary error is a weighted variation. -/
theorem sum_faces_edgeVariationIn_le {U : TriadicCube 2} (v : ClusterFun ω U) :
    ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i,
        edgeVariationIn ω (planarClusterWindow ω U x) (clusterExtend ω U v) +
      ∑ x ∈ U.toIntegerCube.lowerFace i,
        edgeVariationIn ω (planarClusterWindow ω U x) (clusterExtend ω U v)) ≤
      ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
        (if (openGraph ω).Adj x.1 y.1 then |v x - v y| else 0) * boundaryWeight ω U x.1 := by
  have hS := planarClusterWindow_subset (ω := ω) U
  have hface : ∀ F : Finset (Vertex 2), ∑ x ∈ F,
      edgeVariationIn ω (planarClusterWindow ω U x) (clusterExtend ω U v) ≤
      ∑ a : ↥(clusterVertices ω U), ∑ b : ↥(clusterVertices ω U),
        (if (openGraph ω).Adj a.1 b.1 then |v a - v b| else 0) *
          ∑ x ∈ F, (if a.1 ∈ planarClusterWindow ω U x then 1 else 0) :=
    fun F => sum_edgeVariationIn_le v F _ hS
  calc ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i,
        edgeVariationIn ω (planarClusterWindow ω U x) (clusterExtend ω U v) +
      ∑ x ∈ U.toIntegerCube.lowerFace i,
        edgeVariationIn ω (planarClusterWindow ω U x) (clusterExtend ω U v))
      ≤ ∑ i, (∑ a : ↥(clusterVertices ω U), ∑ b : ↥(clusterVertices ω U),
          (if (openGraph ω).Adj a.1 b.1 then |v a - v b| else 0) *
            ∑ x ∈ U.toIntegerCube.upperFace i,
              (if a.1 ∈ planarClusterWindow ω U x then 1 else 0) +
        ∑ a : ↥(clusterVertices ω U), ∑ b : ↥(clusterVertices ω U),
          (if (openGraph ω).Adj a.1 b.1 then |v a - v b| else 0) *
            ∑ x ∈ U.toIntegerCube.lowerFace i,
              (if a.1 ∈ planarClusterWindow ω U x then 1 else 0)) :=
        Finset.sum_le_sum fun i _ => add_le_add (hface _) (hface _)
    _ = _ := by
        simp only [← Finset.sum_add_distrib, ← mul_add]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.mul_sum, boundaryWeight]

theorem boundaryWeight_nonneg (U : TriadicCube 2) (a : Vertex 2) :
    0 ≤ boundaryWeight ω U a :=
  Finset.sum_nonneg fun _ _ => add_nonneg
    (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
    (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)

/-- **Young's inequality** for a quantity controlled by Cauchy–Schwarz. -/
theorem le_of_sq_le_mul {X T B t : ℝ} (hX : 0 ≤ X) (hT : 0 ≤ T) (hB : 0 ≤ B) (ht : 0 < t)
    (h : X ^ 2 ≤ T * B) : X ≤ (T / t + t * B) / 2 := by
  have h1 : 0 ≤ (T / t + t * B) / 2 := by positivity
  have h2 : X ^ 2 ≤ ((T / t + t * B) / 2) ^ 2 := by
    refine h.trans ?_
    have : ((T / t + t * B) / 2) ^ 2 - T * B = ((T / t - t * B) / 2) ^ 2 := by
      field_simp
      ring
    nlinarith [sq_nonneg ((T / t - t * B) / 2)]
  exact (pow_le_pow_iff_left₀ hX h1 (by norm_num)).1 h2

/-- **Boundary error bound.** For every `t > 0`, the boundary error of a function `v` on the
cluster is at most `(9 ∑ W_∂² / t + 2 t B v v) / 2` plus `|p|₁` times the sum of the sides of the
partition cubes of the boundary vertices. -/
theorem boundaryError_le {U : TriadicCube 2} (p : Fin 2 → ℝ) (v : ClusterFun ω U) {t : ℝ}
    (ht : 0 < t) :
    boundaryError ω U p v ≤
      (9 * (∑ x : ↥(clusterVertices ω U), boundaryWeight ω U x.1 ^ 2) / t +
        t * (2 * clusterForm ω U v v)) / 2 +
      (|p 0| + |p 1|) * ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i,
        (3 : ℝ) ^ (planarPartCube ω x).scale +
        ∑ x ∈ U.toIntegerCube.lowerFace i, (3 : ℝ) ^ (planarPartCube ω x).scale) := by
  set X := ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
    (if (openGraph ω).Adj x.1 y.1 then |v x - v y| else 0) * boundaryWeight ω U x.1 with hX
  set T := ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
    (if (openGraph ω).Adj x.1 y.1 then boundaryWeight ω U x.1 ^ 2 else 0) with hT
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (by split_ifs <;> positivity) (boundaryWeight_nonneg U x.1)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  have hB0 : 0 ≤ 2 * clusterForm ω U v v := by
    have := clusterForm_self_nonneg v
    linarith
  have hCS : X ^ 2 ≤ T * (2 * clusterForm ω U v v) :=
    sum_adj_abs_mul_sq_le v (fun x => boundaryWeight ω U x.1)
  have hT9 : T ≤ 9 * ∑ x : ↥(clusterVertices ω U), boundaryWeight ω U x.1 ^ 2 :=
    sum_adj_le_nine_mul (fun x => boundaryWeight ω U x.1 ^ 2) (fun _ => sq_nonneg _)
  have hXle := le_of_sq_le_mul hX0 hT0 hB0 ht hCS
  have hsplit : boundaryError ω U p v =
      ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i,
        edgeVariationIn ω (planarClusterWindow ω U x) (clusterExtend ω U v) +
      ∑ x ∈ U.toIntegerCube.lowerFace i,
        edgeVariationIn ω (planarClusterWindow ω U x) (clusterExtend ω U v)) +
      (|p 0| + |p 1|) * ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i,
        (3 : ℝ) ^ (planarPartCube ω x).scale +
        ∑ x ∈ U.toIntegerCube.lowerFace i, (3 : ℝ) ^ (planarPartCube ω x).scale) := by
    rw [boundaryError, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, mul_add, Finset.mul_sum,
      Finset.mul_sum]
    ring
  rw [hsplit]
  have hvar := sum_faces_edgeVariationIn_le (ω := ω) (U := U) v
  have hT9' : T / t ≤ 9 * (∑ x : ↥(clusterVertices ω U), boundaryWeight ω U x.1 ^ 2) / t :=
    div_le_div_of_nonneg_right hT9 ht.le
  linarith

end Rigidity.Percolation
