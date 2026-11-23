import Rigidity.Proofs.Dirichlet.PlanarClusterEdges

/-!
# Testing a harmonic function in `μ` on a subcube

Let `U` be a triadic cube of the plane, `u` harmonic on `C_*(U)` off the boundary of `U`, and
`T ⊆ U` a triadic cube resolved by the partition. Then `u` restricted to `C_*(T)` is harmonic on
`C_*(T)` off the boundary of `T` (an open neighbour of an interior vertex of `C_*(T)` lies in `T`
and is joined to it, hence lies in `C_*(T)`), so it is a competitor in the definition of `μ(T, q)`
(Armstrong and Dario, Definition 4.1). Its Dirichlet form is at most the energy density of the
cluster conductance of `U` summed over `T`, and its coarse pairing is the pairing of `q` with the
increments of the coarsened function `u(z̄(□_𝒫(·)))` over the edges inside `T`. This is the test of
Step 1 of the proof of Lemma 6.2 of the source (display (6.20)).
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Dirichlet

variable {ω : Configuration 2}

theorem TriadicCube.isInterior_mono {T U : TriadicCube 2} (hTU : T.vertices ⊆ U.vertices)
    {x : Vertex 2} (hx : T.IsInterior x) : U.IsInterior x := fun y hy => hTU (hx y hy)

/-- **Restriction to a subcube preserves harmonicity.** -/
theorem restrict_mem_clusterHarmonic (hP : PlanarPartitionEvent ω) {T U : TriadicCube 2}
    (hTU : T.vertices ⊆ U.vertices) (hT : PlanarResolved ω T) {u : Vertex 2 → ℝ}
    (hu : (fun x : ↥(clusterVertices ω U) => u x) ∈ clusterHarmonic ω U) :
    (fun x : ↥(clusterVertices ω T) => u x) ∈ clusterHarmonic ω T := by
  rw [mem_clusterHarmonic]
  intro x hx
  have hxU : x.1 ∈ clusterVertices ω U := clusterVertices_subset hTU x.2
  have hU := (mem_clusterHarmonic.1 hu) ⟨x.1, hxU⟩ (TriadicCube.isInterior_mono hTU hx)
  rw [clusterLaplacianAt_apply] at hU ⊢
  have hU' : ∑ y ∈ clusterVertices ω U,
      (if (openGraph ω).Adj x.1 y then u y - u x.1 else 0) = 0 := by
    rw [← Finset.sum_coe_sort (clusterVertices ω U)
      (fun y => if (openGraph ω).Adj x.1 y then u y - u x.1 else 0)]
    exact hU
  suffices h : ∑ y ∈ clusterVertices ω T,
      (if (openGraph ω).Adj x.1 y then u y - u x.1 else 0) = 0 by
    rw [← Finset.sum_coe_sort (clusterVertices ω T)
      (fun y => if (openGraph ω).Adj x.1 y then u y - u x.1 else 0)] at h
    exact h
  refine (Finset.sum_subset (clusterVertices_subset hTU)
    (f := fun y => if (openGraph ω).Adj x.1 y then u y - u x.1 else 0)
    fun y hyU hyT => ?_).trans hU'
  rw [if_neg]
  intro hadj
  apply hyT
  have hxT := mem_clusterVertices.1 x.2
  have hyT' : y ∈ T.vertices := hx y fun i => by
    obtain ⟨l, hl | hl⟩ := Graph.Zd.adj_iff.mp (openGraph_le ω hadj) <;> subst hl <;>
      by_cases hil : i = l <;> simp [unit, hil]
  refine mem_clusterVertices.2 (mem_planarCubeCluster_of_reachIn hP hT hyT' hxT.1 ?_)
  refine ReachIn.trans ⟨SimpleGraph.Walk.cons hadj.symm SimpleGraph.Walk.nil, fun v hv => ?_⟩ hxT.2
  simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact hyT'
  · exact hxT.1

/-- `μ` is at most the value of its functional at a harmonic function. -/
theorem planarMu_le_of_mem (hP : PlanarPartitionEvent ω) {T : TriadicCube 2}
    (hT : PlanarResolved ω T) (q : Fin 2 → ℝ) {v : ClusterFun ω T}
    (hv : v ∈ clusterHarmonic ω T) :
    planarMu ω T q ≤ (clusterForm ω T v v / 2 - coarsePairing ω T q v) / T.volume := by
  obtain ⟨u₀, hu₀, hmin⟩ := exists_clusterHarmonic_minimizer T (coarsePairing ω T q)
    (fun w hw => coarsePairing_eq_zero_of_clusterForm hP hT q hw)
  have hvol := T.volume_pos
  set f : clusterHarmonic ω T → ℝ := fun w =>
    (clusterForm ω T w w / 2 - coarsePairing ω T q w) / T.volume with hf
  have hbdd : BddBelow (Set.range f) := ⟨f ⟨u₀, hu₀⟩, by
    rintro _ ⟨w, rfl⟩
    exact div_le_div_of_nonneg_right (hmin w.1 w.2).2 hvol.le⟩
  exact ciInf_le hbdd ⟨v, hv⟩

/-- **The coarse pairing of a harmonic function** is the pairing of `q` with the increments of the
coarsened function over the edges inside `T`. -/
theorem coarsePairing_restrict (hP : PlanarPartitionEvent ω) {T : TriadicCube 2}
    (hT : PlanarResolved ω T) (q : Fin 2 → ℝ) (u : Vertex 2 → ℝ) :
    coarsePairing ω T q (fun x : ↥(clusterVertices ω T) => u x) =
      ∑ i : Fin 2, q i * ∑ x ∈ T.toIntegerCube.vertices,
        (if x + unit i ∈ T.toIntegerCube.vertices then
          u (planarCoarseAnchor ω (x + unit i)) - u (planarCoarseAnchor ω x) else 0) := by
  rw [coarsePairing_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [unitVertex_eq_unit]
  split_ifs with h
  · have hA : ∀ z ∈ T.toIntegerCube.vertices,
        clusterExtend ω T (fun x : ↥(clusterVertices ω T) => u x) (planarCoarseAnchor ω z) =
          u (planarCoarseAnchor ω z) := by
      intro z hz
      have hzT := (T.mem_toIntegerCube_vertices z).1 hz
      exact clusterExtend_apply_of_mem _
        (mem_clusterVertices.2 (planarAnchor_mem_planarCubeCluster hP hT hzT))
    rw [hA _ h, hA _ hx]
  · rw [mul_zero]

/-- **The `μ` test on a subcube** (Armstrong and Dario, display (6.20)). -/
theorem planarMu_le_test (hP : PlanarPartitionEvent ω) {T U : TriadicCube 2}
    (hTU : T.vertices ⊆ U.vertices) (hT : PlanarResolved ω T) {u : Vertex 2 → ℝ}
    (hu : (fun x : ↥(clusterVertices ω U) => u x) ∈ clusterHarmonic ω U) (q : Fin 2 → ℝ) :
    planarMu ω T q ≤
      (∑ y ∈ T.toIntegerCube.vertices, clusterEnergy ω U u y) / T.volume / 2 -
        ∑ i : Fin 2, q i * ((∑ x ∈ T.toIntegerCube.vertices,
          (if x + unit i ∈ T.toIntegerCube.vertices then
            u (planarCoarseAnchor ω (x + unit i)) - u (planarCoarseAnchor ω x) else 0)) /
              T.volume) := by
  have hvol := T.volume_pos
  have h1 := planarMu_le_of_mem hP hT q (restrict_mem_clusterHarmonic hP hTU hT hu)
  have h2 := clusterForm_le_sum_clusterEnergy (ω := ω) hTU u
  rw [coarsePairing_restrict hP hT q u] at h1
  refine h1.trans ?_
  have e : ∑ i : Fin 2, q i * ((∑ x ∈ T.toIntegerCube.vertices,
      (if x + unit i ∈ T.toIntegerCube.vertices then
        u (planarCoarseAnchor ω (x + unit i)) - u (planarCoarseAnchor ω x) else 0)) / T.volume) =
      (∑ i : Fin 2, q i * ∑ x ∈ T.toIntegerCube.vertices,
        (if x + unit i ∈ T.toIntegerCube.vertices then
          u (planarCoarseAnchor ω (x + unit i)) - u (planarCoarseAnchor ω x) else 0)) /
            T.volume := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  set X := ∑ i : Fin 2, q i * ∑ x ∈ T.toIntegerCube.vertices,
    (if x + unit i ∈ T.toIntegerCube.vertices then
      u (planarCoarseAnchor ω (x + unit i)) - u (planarCoarseAnchor ω x) else 0)
  set E := ∑ y ∈ T.toIntegerCube.vertices, clusterEnergy ω U u y
  rw [show E / T.volume / 2 - X / T.volume = (E / 2 - X) / T.volume by ring]
  exact div_le_div_of_nonneg_right (by linarith) hvol.le

end Rigidity.Dirichlet
