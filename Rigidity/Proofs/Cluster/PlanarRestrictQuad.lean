import Rigidity.Proofs.Cluster.PlanarInnerSquare

/-!
# The coarsened gradient on a subcube through the Dirichlet form

For a function `w` on the cluster `𝒞(V)` of a triadic cube `V`, extended by zero, the sum over
`𝒞(V)` of the energy densities `|∇w 1_{𝐚≠0}|²` is the Dirichlet form `B(w, w)` of `μ`
(`sum_clusterGradSq_eq_clusterForm`). Hence, combined with the removal of the boundary layer of
width `3^j` and the Meyers estimate inside the inner square, the pairing of the coarsened gradient
of `w` with a field `g`, `|g| ≤ G`, satisfies
`⟨∇[w]_𝒫, g⟩_V² ≤ 8 G² |V| C² (∑ W^{3q})^{1/q} C_M^{1/p} N B(w, w)
  + 64 G² 3^{n+j} ∑_V |∇[w]_𝒫|²`
when the partition cubes of `V` have scale at most `j < n` and `W ≥ 3 planarReach`
(`edgePairing_clusterExtend_sq_le_of_meyers`). With `w = u(·, □_m, q)|_V - u(·, V, q)` the form
`B(w, w)` is twice the summand of the energy of the differences of Lemma 5.4 (`planarMuDefect`);
this is the deterministic estimate behind display (5.19) of Armstrong and Dario (Lemma 5.5,
Step 3), the boundary term being estimated in Steps 2 and 4.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

/-- The energy densities of a function on the cluster sum to its Dirichlet form. -/
theorem sum_clusterGradSq_eq_clusterForm (V : TriadicCube 2) (w : ClusterFun ω V) :
    ∑ x ∈ clusterVertices ω V,
        clusterGradSq ω (clusterVertices ω V) (clusterExtend ω V w) x =
      clusterForm ω V w w := by
  set S := clusterVertices ω V with hS
  rw [clusterForm_apply, Finset.mul_sum]
  rw [← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold clusterGradSq
  congr 1
  rw [Finset.sum_filter]
  have hfilt : ∀ y : Vertex 2, (if y ∈ S then (if (openGraph ω).Adj x.1 y then
      (clusterExtend ω V w x.1 - clusterExtend ω V w y) ^ 2 else 0) else 0) =
      if h : y ∈ S then clusterFormTerm ω w w x ⟨y, h⟩ else 0 := by
    intro y
    by_cases hy : y ∈ S
    · rw [if_pos hy, dif_pos hy, clusterFormTerm, clusterExtend_apply_of_mem w x.2,
        clusterExtend_apply_of_mem w hy]
      split_ifs <;> ring
    · rw [if_neg hy, dif_neg hy]
  have hnb : ∑ y ∈ (openGraph ω).neighborFinset x.1,
      (if y ∈ S then (clusterExtend ω V w x.1 - clusterExtend ω V w y) ^ 2 else 0) =
      ∑ y ∈ S, (if (openGraph ω).Adj x.1 y then
        (clusterExtend ω V w x.1 - clusterExtend ω V w y) ^ 2 else 0) := by
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    congr 1
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact and_comm
  rw [hnb, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [clusterFormTerm, clusterExtend_apply_of_mem w x.2, clusterExtend_apply_of_mem w y.2]
  split_ifs <;> ring

/-- **The coarsened gradient on a subcube through the Dirichlet form** (Armstrong and Dario,
proof of Lemma 5.5, Steps 2 and 3, deterministic part, in dimension two). Let `V` be a triadic
cube of scale `n` whose vertices have planar partition cubes of scale at most `j < n`, `w` a
function on its cluster, `g` a field with `|g| ≤ G`, `W ≥ 3 planarReach` a weight, and let a finite
family of cells cover the cluster of the inner square `innerSquare V j`, with triples inside `V`,
overlap at most `N` and the Meyers estimate with exponent `p > 1` (Hölder conjugate `q`) and
constant `C_M`. Then
`⟨∇[w]_𝒫, g⟩_V² ≤ 8 G² 9^n C² (∑_{𝒞(B)} W^{3q})^{1/q} C_M^{1/p} N B(w, w)
  + 64 G² 3^{n+j} ∑_V |∇[w]_𝒫|²`. -/
theorem edgePairing_clusterExtend_sq_le_of_meyers (hP : PlanarPartitionEvent ω)
    {V : TriadicCube 2} {j : ℕ} (hj : j < V.scale)
    (hres : ∀ x ∈ V.vertices, (planarPartCube ω x).scale ≤ j) (w : ClusterFun ω V)
    {g : Vertex 2 → Fin 2 → ℝ} {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) (Wt : Vertex 2 → ℝ)
    (hWt : ∀ z, 3 * planarReach ω z ≤ ENNReal.ofReal (Wt z))
    {p q CM : ℝ} (hpq : p.HolderConjugate q) (hCM : 0 ≤ CM) (I : Finset (ℕ × Vertex 2)) {N : ℕ}
    (hcov : ∀ z ∈ boxClusterVertices ω (innerSquare V j), ∃ c ∈ I, z ∈ cube c.1 c.2)
    (hV : ∀ c ∈ I, enl 1 c.1 c.2 ⊆ V.toIntegerCube.vertices)
    (hN : ∀ x, (I.filter fun c => x ∈ enl 1 c.1 c.2).card ≤ N)
    (hM : ∀ c ∈ I, avg (cube c.1 c.2) (fun x =>
        clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ p) ≤
      CM * avg (enl 1 c.1 c.2) (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^ p) :
    edgePairing V.toIntegerCube.vertices g
        (fun x => clusterExtend ω V w (planarCoarseAnchor ω x)) ^ 2 ≤
      8 * G ^ 2 * 9 ^ V.scale *
        ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
          (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2 *
          ((∑ z ∈ boxClusterVertices ω (innerSquare V j), (Wt z ^ 3) ^ q) ^ (1 / q) *
            (CM ^ (1 / p) * ((N : ℝ) * clusterForm ω V w w)))) +
      64 * G ^ 2 * 3 ^ (V.scale + j) *
        ∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
            (fun x => clusterExtend ω V w (planarCoarseAnchor ω x)) x ^ 2 := by
  have hBr := planarBoxResolved_innerSquare hP hj hres
  set B := innerSquare V j with hBdef
  have hWt' : ∀ z ∈ boxClusterVertices ω B,
      (3 : ℝ) ^ (planarBoxCoarseData hP B hBr).pairReachScale z ≤ Wt z := by
    intro z _
    have h1 := (three_pow_pairReachScale_le_planarReach_box hP hBr z).trans (hWt z)
    have h2 : ENNReal.ofReal ((3 : ℝ) ^ (planarBoxCoarseData hP B hBr).pairReachScale z) =
        (3 : ℝ≥0∞) ^ (planarBoxCoarseData hP B hBr).pairReachScale z := by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    rw [← h2] at h1
    have hpos : (0 : ℝ) < Wt z := by
      by_contra hcon
      push Not at hcon
      rw [ENNReal.ofReal_of_nonpos hcon] at h1
      have : (0 : ℝ) < (3 : ℝ) ^ (planarBoxCoarseData hP B hBr).pairReachScale z := by positivity
      exact absurd h1 (not_le.2 (ENNReal.ofReal_pos.2 this))
    exact (ENNReal.ofReal_le_ofReal_iff hpos.le).1 h1
  have h := edgePairing_coarse_sq_le_of_meyers hP hBr (innerSquare_subset hj)
    (clusterExtend ω V w) hg Wt hWt' hpq hCM I hcov hV hN hM
  have hsum : ∑ x ∈ V.toIntegerCube.vertices,
      clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x = clusterForm ω V w w := by
    rw [← sum_clusterGradSq_eq_clusterForm V w]
    have hsub : clusterVertices ω V ⊆ V.toIntegerCube.vertices := Finset.filter_subset _ _
    rw [← Finset.sum_subset hsub fun x _ hx => by rw [clusterEnergy, if_neg hx]]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [clusterEnergy, if_pos hx]
  rw [hsum] at h
  refine h.trans (add_le_add ?_ ?_)
  · have hcard : (B.vertices.card : ℝ) ≤ 9 ^ V.scale := by
      have h1 : B.vertices.card ≤ V.toIntegerCube.vertices.card :=
        Finset.card_le_card (innerSquare_subset hj)
      have h2 : (V.toIntegerCube.vertices.card : ℝ) = 9 ^ V.scale := by
        rw [IntegerCube.card_vertices_eq]
        change ((((3 ^ V.scale : ℕ) ^ 2 : ℕ)) : ℝ) = _
        push_cast
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      calc (B.vertices.card : ℝ) ≤ V.toIntegerCube.vertices.card := by exact_mod_cast h1
        _ = 9 ^ V.scale := h2
    have hrest : 0 ≤ (2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
          (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2 *
          ((∑ z ∈ boxClusterVertices ω B, (Wt z ^ 3) ^ q) ^ (1 / q) *
            (CM ^ (1 / p) * ((N : ℝ) * clusterForm ω V w w))) := by
      have hq0 : 0 ≤ ∑ z ∈ boxClusterVertices ω B, (Wt z ^ 3) ^ q := by
        refine Finset.sum_nonneg fun z hz => Real.rpow_nonneg (pow_nonneg ?_ 3) q
        exact ((by positivity : (0 : ℝ) ≤ 3 ^ _).trans (hWt' z hz))
      have hB0 := clusterForm_self_nonneg (ω := ω) (U := V) w
      positivity
    have hG : 0 ≤ 8 * G ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hG) hrest
  · have hlayer := card_sdiff_innerSquare_le hj
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun x _ => sq_nonneg _)
    calc 16 * G ^ 2 * ((V.toIntegerCube.vertices \ B.vertices).card : ℝ)
        ≤ 16 * G ^ 2 * (4 * 3 ^ (V.scale + j)) :=
          mul_le_mul_of_nonneg_left hlayer (by positivity)
      _ = 64 * G ^ 2 * 3 ^ (V.scale + j) := by ring

end Rigidity.Proofs.Cluster
