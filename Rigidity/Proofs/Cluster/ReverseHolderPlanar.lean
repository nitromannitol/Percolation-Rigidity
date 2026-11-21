import Rigidity.Proofs.Cluster.ReverseHolderPartition
import Rigidity.Proofs.Cluster.PlanarSobolevTwo

/-!
# The reverse Hölder inequality on a resolved planar cube given the moment bound

Armstrong–Dario, Lemma 3.6, deterministic part, for the planar partition (`d = 2`, so
`2_* = 1`). Let `□_{m+1} = ⟨m + 1, c⟩` be a triadic cube resolved by the planar partition and
`U = 𝒞(□_{m+1})` its cluster. The cluster contains every vertex of `□_{m+1}` joined to it by an open
edge (`mem_clusterVertices_of_adj_mem`), and the Sobolev inequality on `U` (Proposition 3.4 with
`s = 2`, `exists_planar_sum_sq_le`) is the hypothesis `ClusterSobolevTwo` with the cell size
`size(z) = ((3^{ρ(z)})² + 3^{ρ'(z)})^{1/4}`, where `ρ` and `ρ'` are the reach scales of the planar
coarse-graining data. The remaining hypotheses of `planar_reverse_holder_cube_of_moment` are:

* `□_{m+1}` is resolved by the planar partition;
* the moment bound `∑_{z ∈ U} ((3^{ρ(z)})² + 3^{ρ'(z)})^s ≤ C_G |□_{m+1}|` (in the source, the scale
  condition `3^m ≥ 𝓜_{4s}(𝒫)`);
* `u` is harmonic on `U`.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical

theorem lowerSobolevTwo_two : lowerSobolevTwo 2 = 1 := by
  unfold lowerSobolevTwo
  norm_num

/-- The cluster of a resolved planar cube contains every vertex of the cube joined to it by an open
edge. -/
theorem mem_clusterVertices_of_adj_mem {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {Q : TriadicCube 2} (hQ : PlanarResolved ω Q) {z y : Vertex 2}
    (hz : z ∈ clusterVertices ω Q) (hadj : (openGraph ω).Adj z y) (hy : y ∈ Q.vertices) :
    y ∈ clusterVertices ω Q := by
  have hzC := mem_clusterVertices.1 hz
  have hyz : ReachIn ω Q.vertices y z :=
    ⟨SimpleGraph.Walk.cons hadj.symm SimpleGraph.Walk.nil, fun w hw => by
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hy
      · exact hzC.1⟩
  exact mem_clusterVertices.2 (mem_planarCubeCluster_of_reachIn hP hQ hy hzC.1 (hyz.trans hzC.2))

/-- **Reverse Hölder inequality on the cluster of a resolved planar cube, given the moment bound of
the reach scales** (Armstrong–Dario, Lemma 3.6, deterministic part, for the planar partition), for
every triadic cube `⟨m + 1, c⟩` and its central subcube `cube m (3^{m+1} c)`; `t` is the Hölder
conjugate of `s`. -/
theorem planar_reverse_holder_cube_of_moment :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration 2) (hP : PlanarPartitionEvent ω) (m : ℕ) (c : Vertex 2)
      (hU : PlanarResolved ω ⟨m + 1, c⟩),
      ∀ {CG s t : ℝ}, 0 ≤ CG → s.HolderConjugate t →
      ∑ z ∈ clusterVertices ω ⟨m + 1, c⟩,
          (((3 : ℝ) ^ (planarCoarseData hP ⟨m + 1, c⟩ hU).reachScale z) ^ 2 +
            (3 : ℝ) ^ (planarCoarseData hP ⟨m + 1, c⟩ hU).pairReachScale z) ^ s ≤
          CG * (3 : ℝ) ^ ((m + 1) * 2) →
      ∀ u : Vertex 2 → ℝ, (∀ x ∈ clusterVertices ω ⟨m + 1, c⟩,
          (∀ y, (openGraph ω).Adj x y → y ∈ clusterVertices ω ⟨m + 1, c⟩) →
            openLaplacian ω u x = 0) →
      (1 / (3 : ℝ) ^ (m * 2)) * ∑ x ∈ (clusterVertices ω ⟨m + 1, c⟩).filter
          (· ∈ cube m (centralPoint m c)),
          clusterGradSq ω (clusterVertices ω ⟨m + 1, c⟩) u x ≤
        K * CG ^ (2 / s) *
          ((1 / (3 : ℝ) ^ ((m + 1) * 2)) * ∑ x ∈ clusterVertices ω ⟨m + 1, c⟩,
            clusterGradSq ω (clusterVertices ω ⟨m + 1, c⟩) u x ^ (t / 2)) ^ (2 / t) := by
  obtain ⟨K₀, hK₀, hK⟩ := exists_planar_sum_sq_le
  refine ⟨8 * ((2 : ℕ) : ℝ) * K₀ * (3 : ℝ) ^ (2 + 2), by positivity, ?_⟩
  intro ω hP m c hU CG s t hCG hst hmom u hu
  set Q : TriadicCube 2 := ⟨m + 1, c⟩ with hQ
  set U := clusterVertices ω Q with hUdef
  set P := planarCoarseData hP Q hU with hPdef
  set weight : Vertex 2 → ℝ := fun z => ((3 : ℝ) ^ P.reachScale z) ^ 2 +
    (3 : ℝ) ^ P.pairReachScale z with hweight
  have hw0 : ∀ z, 0 ≤ weight z := fun z => by positivity
  set size : Vertex 2 → ℝ := fun z => weight z ^ ((1 : ℝ) / 4) with hsizedef
  have hsize4 : ∀ z, size z ^ (2 * ((2 : ℕ) : ℝ)) = weight z := fun z => by
    rw [hsizedef, ← Real.rpow_mul (hw0 z)]
    norm_num
  have hclosed : ∀ z ∈ U, ∀ y, (openGraph ω).Adj z y → y ∈ enl 1 m (centralPoint m c) →
      y ∈ U := fun z hz y hadj hy =>
    mem_clusterVertices_of_adj_mem hP hU hz hadj
      ((triadicCube_vertices_eq_enl_centralPoint m c y).mpr hy)
  have hSob : ClusterSobolevTwo ω U size K₀ := by
    intro w hw
    have h := hK ω hP Q hU w hw
    rw [lowerSobolevTwo_two]
    have hterm : ∀ z, size z ^ (2 * ((2 : ℕ) : ℝ)) * clusterGradSq ω U w z ^ ((1 : ℝ) / 2) =
        weight z * gradNormIn (openGraph ω) U w z := fun z => by
      rw [hsize4, gradNormIn_openGraph_eq, Real.sqrt_eq_rpow]
    rw [Finset.sum_congr rfl fun z _ => hterm z, show (2 : ℝ) / 1 = 2 by norm_num, Real.rpow_two]
    exact h
  have hgood : ∑ x ∈ U, size x ^ (2 * ((2 : ℕ) : ℝ) * s) ≤ CG * (3 : ℝ) ^ ((m + 1) * 2) := by
    refine (Finset.sum_congr rfl fun z _ => ?_).trans_le hmom
    rw [hsizedef, ← Real.rpow_mul (hw0 z)]
    congr 1
    push_cast
    ring
  have h := reverse_holder_triadic ω (by norm_num) m (centralPoint m c) U
    (U.filter (· ∈ cube m (centralPoint m c))) (Finset.filter_subset _ _)
    (fun x hx => (Finset.mem_filter.mp hx).2) hclosed size
    (fun z => Real.rpow_nonneg (hw0 z) _) hK₀ hCG hst hSob hgood u hu
  rw [lowerSobolevTwo_two] at h
  simp only [mul_one] at h
  exact h.trans_eq (by ring)

end Rigidity.Proofs.Cluster
