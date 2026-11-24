import Rigidity.Proofs.Cluster.GeneralInnerCells
import Rigidity.Proofs.Cluster.GeneralEdgePairing
import Rigidity.Proofs.Cluster.MeyersPartitionBox

/-!
# The coarsened gradient on a subcube through the Dirichlet form, in every dimension

For a function `w` on the crossing cluster `𝒞_*(V)` of a triadic cube `V`, extended by zero, the
energy densities `|∇w 1_{𝐚≠0}|²` on `𝒞_*(V)` sum to the Dirichlet form `B(w, w)` of `μ`
(`sum_clusterGradSq_eq_cubeForm`). On a resolved cube, Lemma 3.3 with `s = 2` gives
`∑_{x ∈ V} |∇[w]_𝒫|²(x) ≤ K² W^{2d-1} B(w, w)` for `W ≥ size(□_𝒫)` on `𝒞_*(V)`
(`sum_gradNormIn_coarse_sq_le_cubeForm`, the deterministic part of display (4.24) of Armstrong and
Dario). Combined with the removal of the boundary layer of width `3^j` and the Meyers estimate on
cells covering the cluster of the inner cube (`latticeEdgePairing_cubeExtend_sq_le_of_meyers`), the
pairing of the coarsened gradient of `w` with a field `g`, `|g| ≤ G`, satisfies

`⟨∇[w]_𝒫, g⟩_V² ≤ (4d G² |V| K² A C_M^{1/p} N + 16 d² G² 3^{(d-1)n + j} K² W^{2d-1}) B(w, w)`

(`latticeEdgePairing_cubeExtend_sq_le_cubeForm`; with the cells of scale `j` of the inner cube,
`N = 3^d`: `latticeEdgePairing_innerCubeCells_sq_le`). This is the deterministic part of Steps 2
and 3 of the proof of Lemma 5.5 of Armstrong and Dario for one subcube, in every dimension
`d ≥ 1`, as in the two-dimensional `Rigidity.Proofs.Cluster.edgePairing_innerCells_sq_le`; for
`w = u(·, □_m, q)|_V - u(·, V, q)`, `B(w, w)` is twice the summand of the energy of the
differences of Lemma 5.4.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The energy densities of a function on the cluster sum to its Dirichlet form. -/
theorem sum_clusterGradSq_eq_cubeForm (V : TriadicCube d) (w : CubeFun ω V) :
    ∑ x ∈ crossingClusterVertices ω V,
        clusterGradSq ω (crossingClusterVertices ω V) (cubeExtend ω V w) x =
      cubeForm ω V w w := by
  set S := crossingClusterVertices ω V with hS
  rw [cubeForm_apply, Finset.mul_sum]
  rw [← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold clusterGradSq
  congr 1
  have hnb : ∑ y ∈ ((openGraph ω).neighborFinset x.1).filter (· ∈ S),
      (cubeExtend ω V w x.1 - cubeExtend ω V w y) ^ 2 =
      ∑ y ∈ S, (if (openGraph ω).Adj x.1 y then
        (cubeExtend ω V w x.1 - cubeExtend ω V w y) ^ 2 else 0) := by
    rw [← Finset.sum_filter]
    congr 1
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact and_comm
  rw [hnb, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [cubeFormTerm, cubeExtend_apply_of_mem w x.2, cubeExtend_apply_of_mem w y.2]
  split_ifs <;> ring

/-- The energy densities summed over the vertices of `V` give the Dirichlet form. -/
theorem sum_clusterEnergy_eq_cubeForm (V : TriadicCube d) (w : CubeFun ω V) :
    ∑ x ∈ V.toIntegerCube.vertices,
        clusterEnergy ω (crossingClusterVertices ω V) (cubeExtend ω V w) x = cubeForm ω V w w := by
  rw [← sum_clusterGradSq_eq_cubeForm V w]
  have hsub : crossingClusterVertices ω V ⊆ V.toIntegerCube.vertices := Finset.filter_subset _ _
  rw [← Finset.sum_subset hsub fun x _ hx => by rw [clusterEnergy, if_neg hx]]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [clusterEnergy, if_pos hx]

/-- **The energy of a coarsened function on a resolved cube.** For `W ≥ size(□_𝒫)` on the
cluster of `V`, `∑_{x ∈ V} |∇[w]_𝒫|²(x) ≤ K² W^{2d-1} B(w, w)`. -/
theorem sum_gradNormIn_coarse_sq_le_cubeForm (hd : 0 < d) (hP : PartitionEvent ω)
    {V : TriadicCube d} (hV : PartitionResolved ω V) (w : CubeFun ω V) {W : ℝ}
    (hW : ∀ z ∈ crossingClusterVertices ω V, (3 : ℝ) ^ (partitionCube ω z).scale ≤ W) :
    ∑ x ∈ V.toIntegerCube.vertices, gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
        (fun x => cubeExtend ω V w (partitionAnchor ω x)) x ^ 2 ≤
      coarseGradConstant d ^ 2 * (W ^ (2 * d - 1) * cubeForm ω V w w) := by
  have h := partition_sum_gradNormIn_coarseAnchor_rpow_le hd hP hV (cubeExtend ω V w) (s := 2)
    (by norm_num)
  simp only [Real.rpow_two] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  rw [← sum_clusterGradSq_eq_cubeForm V w, Finset.mul_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  have he : ((3 : ℝ) ^ (partitionCube ω z).scale) ^ ((2 : ℝ) * (d : ℝ) - 1) =
      ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * d - 1) := by
    rw [show (2 : ℝ) * (d : ℝ) - 1 = ((2 * d - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub (by omega), Nat.cast_mul]; norm_num, Real.rpow_natCast]
  rw [he, gradNormIn_openGraph_eq, Real.sq_sqrt (clusterGradSq_nonneg _ _ _ _)]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) (hW z hz) _) (clusterGradSq_nonneg _ _ _ _)

/-- The cardinality of the vertex set of a triadic cube. -/
theorem card_toIntegerCube_vertices_pow (V : TriadicCube d) :
    (V.toIntegerCube.vertices.card : ℝ) = ((3 : ℝ) ^ V.scale) ^ d := by
  rw [IntegerCube.card_vertices_eq]
  change ((((3 ^ V.scale : ℕ) ^ d : ℕ)) : ℝ) = _
  push_cast
  ring

/-- **The coarsened gradient on a subcube through the Meyers estimate** (Armstrong and Dario,
proof of Lemma 5.5, Steps 2 and 3, deterministic part, every dimension `d ≥ 1`). Let `V` be a
resolved triadic cube of scale `n` whose vertices have partition cubes of scale less than `j < n`,
`w` a function on its cluster, `g` a field with `|g| ≤ G`, `Wt ≥ size(□_𝒫)` a weight, and let a
finite family of cells cover the cluster of the inner cube `innerCube V j`, with triples inside
`V`, overlap at most `N`, the Meyers estimate with exponent `p > 1` (Hölder conjugate `q`) and
constant `C_M`, and `(avg_{□'} Wt^{(2d-1)q})^{1/q} ≤ A`. Then
`⟨∇[w]_𝒫, g⟩_V² ≤ 4d G² |V| K² A C_M^{1/p} N B(w, w) + 16 d² G² 3^{(d-1)n + j} ∑_V |∇[w]_𝒫|²`. -/
theorem latticeEdgePairing_cubeExtend_sq_le_of_meyers (hd : 0 < d) (hP : PartitionEvent ω)
    {V : TriadicCube d} (hVr : PartitionResolved ω V) {j : ℕ} (hj : j < V.scale)
    (hres : ∀ x ∈ V.vertices, (partitionCube ω x).scale < j) (w : CubeFun ω V)
    {g : Vertex d → Fin d → ℝ} {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) (Wt : Vertex d → ℝ)
    (hWt : ∀ z, (3 : ℝ) ^ (partitionCube ω z).scale ≤ Wt z)
    {p q CM A : ℝ} (hpq : p.HolderConjugate q) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A)
    (I : Finset (ℕ × Vertex d)) {N : ℕ}
    (hcov : ∀ z ∈ partitionBoxCluster ω (innerCube V j), ∃ c ∈ I, z ∈ cube c.1 c.2)
    (hV : ∀ c ∈ I, enl 1 c.1 c.2 ⊆ V.toIntegerCube.vertices)
    (hN : ∀ x, (I.filter fun c => x ∈ enl 1 c.1 c.2).card ≤ N)
    (hA : ∀ c ∈ I, avg (cube c.1 c.2) (fun x => (Wt x ^ (2 * d - 1)) ^ q) ^ (1 / q) ≤ A)
    (hM : ∀ c ∈ I, avg (cube c.1 c.2) (fun x =>
        clusterEnergy ω (crossingClusterVertices ω V) (cubeExtend ω V w) x ^ p) ≤
      CM * avg (enl 1 c.1 c.2)
        (clusterEnergy ω (crossingClusterVertices ω V) (cubeExtend ω V w)) ^ p) :
    latticeEdgePairing V.toIntegerCube.vertices g
        (fun x => cubeExtend ω V w (partitionAnchor ω x)) ^ 2 ≤
      4 * d * G ^ 2 * ((3 : ℝ) ^ V.scale) ^ d *
        (coarseGradConstant d ^ 2 * (A * (CM ^ (1 / p) * ((N : ℝ) * cubeForm ω V w w)))) +
      16 * d ^ 2 * G ^ 2 * ((3 : ℝ) ^ V.scale) ^ (d - 1) * 3 ^ j *
        ∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
            (fun x => cubeExtend ω V w (partitionAnchor ω x)) x ^ 2 := by
  have hBr := partitionBoxResolved_innerCube hP hj hres
  set B := innerCube V j with hBdef
  have hBV : (↑B.vertices : Set (Vertex d)) ⊆ V.vertices := fun x hx =>
    (V.mem_toIntegerCube_vertices x).1 (innerCube_subset hj hx)
  have hBU : partitionBoxCluster ω B ⊆ crossingClusterVertices ω V :=
    partitionBoxCluster_subset_crossingClusterVertices hd hP hBr hVr hBV
  have hWt0 : ∀ x, 0 ≤ Wt x := fun x => (by positivity : (0 : ℝ) ≤ 3 ^ _).trans (hWt x)
  have hsplit := latticeEdgePairing_sq_le_of_subset (innerCube_subset hj) hg
    (fun x => cubeExtend ω V w (partitionAnchor ω x))
  have hmey := partitionBox_coarse_energy_le_of_meyers hd hP hBr hBU (cubeExtend ω V w) Wt hWt0
    (fun z _ => hWt z) hpq hCM hA0 I hcov hV hN hA hM
  rw [sum_clusterEnergy_eq_cubeForm V w] at hmey
  refine hsplit.trans (add_le_add ?_ ?_)
  · have hcard : (B.vertices.card : ℝ) ≤ ((3 : ℝ) ^ V.scale) ^ d := by
      rw [← TriadicCube.latticeVolume, ← V.card_toIntegerCube_vertices]
      exact_mod_cast Finset.card_le_card (innerCube_subset hj)
    have hrest : 0 ≤ coarseGradConstant d ^ 2 *
        (A * (CM ^ (1 / p) * ((N : ℝ) * cubeForm ω V w w))) := by
      have hB0 := cubeForm_self_nonneg (ω := ω) (U := V) w
      positivity
    calc 4 * d * G ^ 2 * B.vertices.card *
          ∑ x ∈ B.vertices, gradNormIn (nearestNeighborGraph d) B.vertices
            (fun x => cubeExtend ω V w (partitionAnchor ω x)) x ^ 2
        ≤ 4 * d * G ^ 2 * B.vertices.card * (coarseGradConstant d ^ 2 *
            (A * (CM ^ (1 / p) * ((N : ℝ) * cubeForm ω V w w)))) :=
          mul_le_mul_of_nonneg_left hmey (by positivity)
      _ ≤ 4 * d * G ^ 2 * ((3 : ℝ) ^ V.scale) ^ d * (coarseGradConstant d ^ 2 *
            (A * (CM ^ (1 / p) * ((N : ℝ) * cubeForm ω V w w)))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by positivity)) hrest
  · have hlayer := card_sdiff_innerCube_le (V := V) hj
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun x _ => sq_nonneg _)
    calc 8 * d * G ^ 2 * ((V.toIntegerCube.vertices \ B.vertices).card : ℝ)
        ≤ 8 * d * G ^ 2 * (2 * d * ((3 : ℝ) ^ V.scale) ^ (d - 1) * 3 ^ j) :=
          mul_le_mul_of_nonneg_left hlayer (by positivity)
      _ = 16 * d ^ 2 * G ^ 2 * ((3 : ℝ) ^ V.scale) ^ (d - 1) * 3 ^ j := by ring

/-- **The pairing of the coarsened gradient with a bounded field, by the Dirichlet form**
(Armstrong and Dario, proof of Lemma 5.5, Steps 2 and 3, deterministic part, every dimension
`d ≥ 1`). Under the hypotheses of `latticeEdgePairing_cubeExtend_sq_le_of_meyers`, with
`size(□_𝒫) ≤ W` on `𝒞_*(V)`,
`⟨∇[w]_𝒫, g⟩_V² ≤ (4d G² |V| K² A C_M^{1/p} N + 16 d² G² 3^{(d-1)n + j} K² W^{2d-1}) B(w, w)`. -/
theorem latticeEdgePairing_cubeExtend_sq_le_cubeForm (hd : 0 < d) (hP : PartitionEvent ω)
    {V : TriadicCube d} (hVr : PartitionResolved ω V) {j : ℕ} (hj : j < V.scale)
    (hres : ∀ x ∈ V.vertices, (partitionCube ω x).scale < j) (w : CubeFun ω V)
    {g : Vertex d → Fin d → ℝ} {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) (Wt : Vertex d → ℝ)
    (hWt : ∀ z, (3 : ℝ) ^ (partitionCube ω z).scale ≤ Wt z) {W : ℝ}
    (hW : ∀ z ∈ crossingClusterVertices ω V, (3 : ℝ) ^ (partitionCube ω z).scale ≤ W)
    {p q CM A : ℝ} (hpq : p.HolderConjugate q) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A)
    (I : Finset (ℕ × Vertex d)) {N : ℕ}
    (hcov : ∀ z ∈ partitionBoxCluster ω (innerCube V j), ∃ c ∈ I, z ∈ cube c.1 c.2)
    (hV : ∀ c ∈ I, enl 1 c.1 c.2 ⊆ V.toIntegerCube.vertices)
    (hN : ∀ x, (I.filter fun c => x ∈ enl 1 c.1 c.2).card ≤ N)
    (hA : ∀ c ∈ I, avg (cube c.1 c.2) (fun x => (Wt x ^ (2 * d - 1)) ^ q) ^ (1 / q) ≤ A)
    (hM : ∀ c ∈ I, avg (cube c.1 c.2) (fun x =>
        clusterEnergy ω (crossingClusterVertices ω V) (cubeExtend ω V w) x ^ p) ≤
      CM * avg (enl 1 c.1 c.2)
        (clusterEnergy ω (crossingClusterVertices ω V) (cubeExtend ω V w)) ^ p) :
    latticeEdgePairing V.toIntegerCube.vertices g
        (fun x => cubeExtend ω V w (partitionAnchor ω x)) ^ 2 ≤
      (4 * d * G ^ 2 * ((3 : ℝ) ^ V.scale) ^ d *
          (coarseGradConstant d ^ 2 * (A * (CM ^ (1 / p) * (N : ℝ)))) +
        16 * d ^ 2 * G ^ 2 * ((3 : ℝ) ^ V.scale) ^ (d - 1) * 3 ^ j *
          (coarseGradConstant d ^ 2 * W ^ (2 * d - 1))) *
        cubeForm ω V w w := by
  have h := latticeEdgePairing_cubeExtend_sq_le_of_meyers hd hP hVr hj hres w hg Wt hWt hpq hCM
    hA0 I hcov hV hN hA hM
  have h2 := sum_gradNormIn_coarse_sq_le_cubeForm hd hP hVr w hW
  refine h.trans (le_of_le_of_eq (add_le_add_right
    (mul_le_mul_of_nonneg_left h2 (by positivity)) _) ?_)
  ring

/-- **The pairing with the cells of the inner cube** (Armstrong and Dario, proof of Lemma 5.5,
Steps 2 and 3, deterministic part, every dimension `d ≥ 1`): the bound
`latticeEdgePairing_cubeExtend_sq_le_cubeForm` with the cells of scale `j` of the inner cube,
whose triples lie in `V` and overlap at most `3^d` times; the remaining hypotheses are the
partition scales less than `j` on `V`, the Meyers estimate on the cells, the bound on the cell
averages of the weight and the bound on the weight. -/
theorem latticeEdgePairing_innerCubeCells_sq_le (hd : 0 < d) (hP : PartitionEvent ω)
    {V : TriadicCube d} (hVr : PartitionResolved ω V) {j : ℕ} (hj : j < V.scale)
    (hres : ∀ x ∈ V.vertices, (partitionCube ω x).scale < j) (w : CubeFun ω V)
    {g : Vertex d → Fin d → ℝ} {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) (Wt : Vertex d → ℝ)
    (hWt : ∀ z, (3 : ℝ) ^ (partitionCube ω z).scale ≤ Wt z) {W : ℝ}
    (hW : ∀ z ∈ crossingClusterVertices ω V, (3 : ℝ) ^ (partitionCube ω z).scale ≤ W)
    {p q CM A : ℝ} (hpq : p.HolderConjugate q) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A)
    (hA : ∀ c ∈ innerCubeCells V j,
      avg (cube c.1 c.2) (fun x => (Wt x ^ (2 * d - 1)) ^ q) ^ (1 / q) ≤ A)
    (hM : ∀ c ∈ innerCubeCells V j, avg (cube c.1 c.2) (fun x =>
        clusterEnergy ω (crossingClusterVertices ω V) (cubeExtend ω V w) x ^ p) ≤
      CM * avg (enl 1 c.1 c.2)
        (clusterEnergy ω (crossingClusterVertices ω V) (cubeExtend ω V w)) ^ p) :
    latticeEdgePairing V.toIntegerCube.vertices g
        (fun x => cubeExtend ω V w (partitionAnchor ω x)) ^ 2 ≤
      (4 * d * G ^ 2 * ((3 : ℝ) ^ V.scale) ^ d *
          (coarseGradConstant d ^ 2 * (A * (CM ^ (1 / p) * ((3 ^ d : ℕ) : ℝ)))) +
        16 * d ^ 2 * G ^ 2 * ((3 : ℝ) ^ V.scale) ^ (d - 1) * 3 ^ j *
          (coarseGradConstant d ^ 2 * W ^ (2 * d - 1))) *
        cubeForm ω V w w :=
  latticeEdgePairing_cubeExtend_sq_le_cubeForm hd hP hVr hj hres w hg Wt hWt hW hpq hCM hA0
    (innerCubeCells V j) (fun _ hz => innerCubeCells_cover V j (mem_partitionBoxCluster.1 hz).1)
    (fun _ hc => innerCubeCells_enl_subset hj hc) (fun x => card_innerCubeCells_filter_le V j x)
    hA hM

end Rigidity.Percolation
