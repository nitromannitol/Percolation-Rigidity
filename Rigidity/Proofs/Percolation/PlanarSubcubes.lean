import Rigidity.Proofs.Percolation.PlanarNablaAffine

/-!
# Restriction to resolved subcubes

For a vertex `x` and a scale `n`, `scaleCube n x` is the triadic cube of scale `n` containing `x`.
If `V ⊆ U` are triadic cubes, both resolved by the planar partition, then the cluster of `V` is
contained in the cluster of `U`, and the restriction of a function of `A_*(U)` to the cluster of
`V` lies in `A_*(V)`; its extension and its coarsening agree with those of the original function on
`V`. These are the deterministic facts behind the subadditivity of `μ` and `ν` (Armstrong and
Dario, Lemma 4.8).
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The triadic cube of scale `n` containing a vertex. -/
def scaleCube (n : ℕ) (x : Vertex 2) : TriadicCube 2 := (⟨0, x⟩ : TriadicCube 2).ancestor n

theorem mem_unitCube (x : Vertex 2) : x ∈ (⟨0, x⟩ : TriadicCube 2).vertices := by
  intro i
  change |2 * (x i - (3 : ℤ) ^ 0 * x i)| < (3 : ℤ) ^ 0
  simp

theorem mem_scaleCube (n : ℕ) (x : Vertex 2) : x ∈ (scaleCube n x).vertices :=
  (⟨0, x⟩ : TriadicCube 2).vertices_subset_ancestor n (mem_unitCube x)

theorem scale_scaleCube (n : ℕ) (x : Vertex 2) : (scaleCube n x).scale = n := by
  unfold scaleCube
  rw [TriadicCube.scale_ancestor]
  simp

/-- Vertices of the same scale-`n` cube have the same scale-`n` cube. -/
theorem scaleCube_eq_of_mem {n : ℕ} {x y : Vertex 2} (hy : y ∈ (scaleCube n x).vertices) :
    scaleCube n y = scaleCube n x :=
  TriadicCube.eq_of_mem_of_scale_eq (by rw [scale_scaleCube, scale_scaleCube])
    (mem_scaleCube n y) hy

/-- A scale-`n` cube containing a vertex of `U`, with `n` at most the scale of `U`, lies in `U`. -/
theorem scaleCube_subset {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale) {x : Vertex 2}
    (hx : x ∈ U.vertices) : (scaleCube n x).vertices ⊆ U.vertices :=
  TriadicCube.vertices_subset_of_mem_of_scale_le (mem_scaleCube n x) hx
    (by rw [scale_scaleCube]; exact hn)

/-- Clusters of nested resolved cubes are nested. -/
theorem planarCubeCluster_subset {U V : TriadicCube 2} (hVU : V.vertices ⊆ U.vertices) :
    planarCubeCluster ω V ⊆ planarCubeCluster ω U :=
  fun _y hy => ⟨hVU hy.1, hy.2.mono hVU⟩

theorem clusterVertices_subset {U V : TriadicCube 2} (hVU : V.vertices ⊆ U.vertices) :
    clusterVertices ω V ⊆ clusterVertices ω U := fun _y hy =>
  mem_clusterVertices.2 (planarCubeCluster_subset hVU (mem_clusterVertices.1 hy))

/-- The restriction of a function on the cluster of `U` to the cluster of `V`. -/
noncomputable def clusterRestrict {U V : TriadicCube 2} (hVU : V.vertices ⊆ U.vertices)
    (u : ClusterFun ω U) : ClusterFun ω V :=
  fun y => u ⟨y.1, clusterVertices_subset hVU y.2⟩

theorem clusterExtend_restrict {U V : TriadicCube 2} (hVU : V.vertices ⊆ U.vertices)
    (u : ClusterFun ω U) {y : Vertex 2} (hy : y ∈ clusterVertices ω V) :
    clusterExtend ω V (clusterRestrict hVU u) y = clusterExtend ω U u y := by
  rw [clusterExtend_apply_of_mem _ hy, clusterExtend_apply_of_mem _ (clusterVertices_subset hVU hy)]
  rfl

/-- An open neighbour of an interior vertex of the cluster of `V` lies in the cluster of `V`. -/
theorem mem_clusterVertices_of_adj (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) {y z : Vertex 2}
    (hy : y ∈ clusterVertices ω V) (hint : V.IsInterior y) (hyz : (openGraph ω).Adj y z) :
    z ∈ clusterVertices ω V := by
  have hzV : z ∈ V.vertices := hint z fun i => by
    have h := Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω hyz) i
    rw [abs_sub_comm]
    exact h
  have hyC := mem_clusterVertices.1 hy
  have hzy : ReachIn ω V.vertices z y :=
    ⟨SimpleGraph.Walk.cons hyz.symm SimpleGraph.Walk.nil, fun w hw => by
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hzV
      · exact hyC.1⟩
  exact mem_clusterVertices.2
    (mem_planarCubeCluster_of_reachIn hP hV hzV hyC.1 (hzy.trans hyC.2))

/-- Sums over the cluster as a type and as a finite set. -/
theorem sum_cluster_eq {U : TriadicCube 2} (u : ClusterFun ω U) (F : Vertex 2 → ℝ → ℝ) :
    ∑ z : ↥(clusterVertices ω U), F z.1 (u z) =
      ∑ z ∈ clusterVertices ω U, F z (clusterExtend ω U u z) := by
  rw [← Finset.sum_coe_sort (clusterVertices ω U)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [clusterExtend_apply_of_mem u z.2]

/-- **Restriction preserves harmonicity.** -/
theorem clusterRestrict_mem_clusterHarmonic (hP : PlanarPartitionEvent ω) {U V : TriadicCube 2}
    (hV : PlanarResolved ω V) (hVU : V.vertices ⊆ U.vertices) {u : ClusterFun ω U}
    (hu : u ∈ clusterHarmonic ω U) : clusterRestrict hVU u ∈ clusterHarmonic ω V := by
  rw [mem_clusterHarmonic]
  intro y hint
  have hyU : y.1 ∈ clusterVertices ω U := clusterVertices_subset hVU y.2
  have hintU : U.IsInterior y.1 := fun z hz => hVU (hint z hz)
  have h0 := mem_clusterHarmonic.1 hu ⟨y.1, hyU⟩ hintU
  rw [clusterLaplacianAt_apply] at h0 ⊢
  set c := clusterExtend ω U u y.1 with hc
  have hcV : clusterRestrict hVU u y = c := by
    rw [hc, ← clusterExtend_restrict hVU u y.2, clusterExtend_apply_of_mem _ y.2]
  have hcU : u ⟨y.1, hyU⟩ = c := by
    rw [hc, clusterExtend_apply_of_mem u hyU]
  set F : Vertex 2 → ℝ → ℝ := fun z t => if (openGraph ω).Adj y.1 z then t - c else 0 with hF
  have eV : ∑ z : ↥(clusterVertices ω V),
      (if (openGraph ω).Adj y.1 z.1 then clusterRestrict hVU u z - clusterRestrict hVU u y
        else 0) = ∑ z ∈ clusterVertices ω V, F z (clusterExtend ω U u z) := by
    rw [hcV]
    have e1 : ∑ z ∈ clusterVertices ω V, F z (clusterExtend ω U u z) =
        ∑ z ∈ clusterVertices ω V, F z (clusterExtend ω V (clusterRestrict hVU u) z) :=
      Finset.sum_congr rfl fun z hz => by rw [clusterExtend_restrict hVU u hz]
    rw [e1, ← sum_cluster_eq (clusterRestrict hVU u) F]
  have eU : ∑ z : ↥(clusterVertices ω U),
      (if (openGraph ω).Adj y.1 z.1 then u z - u ⟨y.1, hyU⟩ else 0) =
      ∑ z ∈ clusterVertices ω U, F z (clusterExtend ω U u z) := by
    rw [hcU, ← sum_cluster_eq u F]
  have esub : ∑ z ∈ clusterVertices ω V, F z (clusterExtend ω U u z) =
      ∑ z ∈ clusterVertices ω U, F z (clusterExtend ω U u z) := by
    refine Finset.sum_subset (clusterVertices_subset hVU) fun z _ hzV => ?_
    simp only [hF]
    rw [if_neg]
    intro hyz
    exact hzV (mem_clusterVertices_of_adj hP hV y.2 hint hyz)
  rw [eV, esub, ← eU]
  exact h0

/-- **Restriction commutes with coarsening.** -/
theorem coarsen_restrict (hP : PlanarPartitionEvent ω) {U V : TriadicCube 2}
    (hV : PlanarResolved ω V) (hVU : V.vertices ⊆ U.vertices) (u : ClusterFun ω U)
    {x : Vertex 2} (hx : x ∈ V.vertices) :
    coarsen ω V (clusterRestrict hVU u) x = coarsen ω U u x := by
  unfold coarsen
  exact clusterExtend_restrict hVU u
    (mem_clusterVertices.2 (planarAnchor_mem_planarCubeCluster hP hV hx))

end Rigidity.Percolation
