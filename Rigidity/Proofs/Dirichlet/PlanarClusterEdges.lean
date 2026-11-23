import Rigidity.Proofs.Dirichlet.PlanarStatements

/-!
# The cluster of a planar cube as a conductance on the lattice edges

For a triadic cube `U` of the plane, the cluster conductance `c_U(x, k)` is `1` on the open edges
`(x, x + e_k)` with both endpoints in `C_*(U)` and `0` elsewhere. The lattice objects of the
Dirichlet problem for `c_U` are the cluster objects of `U`:

* the open neighbours of `x` in a finite set `S` are among `x ± e_k`, so
  `Σ_{y ∈ S, y ∼ x} g(y)` is the sum of the terms at the four lattice neighbours in `S`
  (`sum_openAdj_eq`);
* the Laplacian of `c_U` is minus the Laplacian of the cluster (`condLaplacian_clusterCond`), so
  functions harmonic on `C_*(U)` off the boundary are `c_U`-harmonic on the interior of `U`;
* the Dirichlet form of the cluster of a cube `T` is the sum of the squared increments over the
  open edges of `C_*(T)` (`clusterForm_eq_sum_edges`); for `T ⊆ U` it is at most the energy
  density of `c_U` summed over `T` (`clusterForm_le_sum_clusterEnergy`), and the energy density of
  `c_U` summed over `U` is the energy of `c_U` on the edges inside `U`
  (`sum_clusterEnergy_eq_innerEdgeEnergy`).
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

namespace Rigidity.Dirichlet

variable {ω : Configuration 2}

theorem unitVertex_eq_unit (i : Fin 2) : unitVertex i = unit i := rfl

theorem unit_apply_two (k i : Fin 2) : (unit k : Vertex 2) i = if i = k then 1 else 0 := by
  simp only [unit, Pi.single_apply]

/-- A lattice neighbour is one of the four vertices `x ± e_k`, and only one. -/
theorem ite_adj_eq_sum (x y : Vertex 2) (b : ℝ) (hb : ¬(nearestNeighborGraph 2).Adj x y → b = 0) :
    b = ∑ k : Fin 2, ((if y = x + unit k then b else 0) + (if y = x - unit k then b else 0)) := by
  by_cases hadj : (nearestNeighborGraph 2).Adj x y
  · obtain ⟨l, hl | hl⟩ := Graph.Zd.adj_iff.mp hadj
    · subst hl
      rw [Fin.sum_univ_two]
      fin_cases l
      · have h1 : ¬ x + unit 0 = x + unit 1 := fun h => by
          have := congrFun h 0; simp [unit_apply_two] at this
        have h2 : ¬ x + unit 0 = x - unit 0 := fun h => by
          have := congrFun h 0; simp [unit_apply_two] at this; omega
        have h3 : ¬ x + unit 0 = x - unit 1 := fun h => by
          have := congrFun h 0; simp [unit_apply_two] at this
        simp only [Fin.zero_eta, if_true, if_neg h1, if_neg h2, if_neg h3]
        ring
      · have h1 : ¬ x + unit 1 = x + unit 0 := fun h => by
          have := congrFun h 1; simp [unit_apply_two] at this
        have h2 : ¬ x + unit 1 = x - unit 1 := fun h => by
          have := congrFun h 1; simp [unit_apply_two] at this; omega
        have h3 : ¬ x + unit 1 = x - unit 0 := fun h => by
          have := congrFun h 1; simp [unit_apply_two] at this
        simp only [Fin.mk_one, if_true, if_neg h1, if_neg h2, if_neg h3]
        ring
    · subst hl
      rw [Fin.sum_univ_two]
      fin_cases l
      · have h1 : ¬ x - unit 0 = x + unit 0 := fun h => by
          have := congrFun h 0; simp [unit_apply_two] at this; omega
        have h2 : ¬ x - unit 0 = x + unit 1 := fun h => by
          have := congrFun h 0; simp [unit_apply_two] at this
        have h3 : ¬ x - unit 0 = x - unit 1 := fun h => by
          have := congrFun h 0; simp [unit_apply_two] at this
        simp only [Fin.zero_eta, if_true, if_neg h1, if_neg h2, if_neg h3]
        ring
      · have h1 : ¬ x - unit 1 = x + unit 1 := fun h => by
          have := congrFun h 1; simp [unit_apply_two] at this; omega
        have h2 : ¬ x - unit 1 = x + unit 0 := fun h => by
          have := congrFun h 1; simp [unit_apply_two] at this
        have h3 : ¬ x - unit 1 = x - unit 0 := fun h => by
          have := congrFun h 1; simp [unit_apply_two] at this
        simp only [Fin.mk_one, if_true, if_neg h1, if_neg h2, if_neg h3]
        ring
  · rw [hb hadj]
    simp

/-- **Open neighbours in a finite set are among the four lattice neighbours.** -/
theorem sum_openAdj_eq (S : Finset (Vertex 2)) (x : Vertex 2) (g : Vertex 2 → ℝ) :
    ∑ y ∈ S, (if (openGraph ω).Adj x y then g y else 0) =
      ∑ k : Fin 2, ((if x + unit k ∈ S ∧ (openGraph ω).Adj x (x + unit k) then g (x + unit k)
          else 0) +
        (if x - unit k ∈ S ∧ (openGraph ω).Adj x (x - unit k) then g (x - unit k) else 0)) := by
  have hpt : ∀ y, (if (openGraph ω).Adj x y then g y else 0) = ∑ k : Fin 2,
      ((if y = x + unit k then (if (openGraph ω).Adj x y then g y else 0) else 0) +
        (if y = x - unit k then (if (openGraph ω).Adj x y then g y else 0) else 0)) :=
    fun y => ite_adj_eq_sum x y _ fun h => if_neg fun h' => h (openGraph_le ω h')
  rw [Finset.sum_congr rfl fun y _ => hpt y, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', ite_and, ite_and]

/-- **Reindexing by a unit step.** -/
theorem sum_sub_unit_eq (S : Finset (Vertex 2)) (k : Fin 2) (h : Vertex 2 → ℝ) :
    ∑ x ∈ S, (if x - unit k ∈ S then h (x - unit k) else 0) =
      ∑ z ∈ S, (if z + unit k ∈ S then h z else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun x => x - unit k) (fun z => z + unit k) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.2, by rw [sub_add_cancel]; exact hx.1⟩
  · intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.2, by rw [add_sub_cancel_right]; exact hz.1⟩
  · intro x _
    exact sub_add_cancel x (unit k)
  · intro z _
    exact add_sub_cancel_right z (unit k)
  · intro x _
    rfl

/-- **Edges counted from both endpoints.** For a symmetric function of the open edges of a finite
set `S`, the sum over ordered pairs of open neighbours is twice the sum over the edges
`(x, x + e_k)`. -/
theorem sum_sum_openAdj_eq_two_mul (S : Finset (Vertex 2)) (f : Vertex 2 → Vertex 2 → ℝ)
    (hf : ∀ x y, f x y = f y x) :
    ∑ x ∈ S, ∑ y ∈ S, (if (openGraph ω).Adj x y then f x y else 0) =
      2 * ∑ x ∈ S, ∑ k : Fin 2,
        (if x + unit k ∈ S ∧ (openGraph ω).Adj x (x + unit k) then f x (x + unit k) else 0) := by
  set A : Vertex 2 → Fin 2 → ℝ := fun x k =>
    if x + unit k ∈ S ∧ (openGraph ω).Adj x (x + unit k) then f x (x + unit k) else 0 with hA
  set B : Vertex 2 → Fin 2 → ℝ := fun x k =>
    if x - unit k ∈ S ∧ (openGraph ω).Adj x (x - unit k) then f x (x - unit k) else 0 with hB
  have h1 : ∀ x, ∑ y ∈ S, (if (openGraph ω).Adj x y then f x y else 0) =
      ∑ k, A x k + ∑ k, B x k := by
    intro x
    rw [sum_openAdj_eq S x (f x), ← Finset.sum_add_distrib]
  have h2 : ∀ k, ∑ x ∈ S, B x k = ∑ x ∈ S, A x k := by
    intro k
    have e : ∀ x, B x k = if x - unit k ∈ S then
        (if (openGraph ω).Adj (x - unit k) (x - unit k + unit k) then
          f (x - unit k) (x - unit k + unit k) else 0) else 0 := by
      intro x
      simp only [hB, sub_add_cancel]
      by_cases h1 : x - unit k ∈ S
      · by_cases h2 : (openGraph ω).Adj x (x - unit k)
        · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2.symm, hf]
        · rw [if_neg (fun h => h2 h.2), if_pos h1, if_neg (fun h => h2 h.symm)]
      · rw [if_neg (fun h => h1 h.1), if_neg h1]
    simp only [e]
    rw [sum_sub_unit_eq S k (fun z => if (openGraph ω).Adj z (z + unit k) then
      f z (z + unit k) else 0)]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [hA, ite_and]
  calc ∑ x ∈ S, ∑ y ∈ S, (if (openGraph ω).Adj x y then f x y else 0)
      = ∑ x ∈ S, ∑ k, A x k + ∑ k, ∑ x ∈ S, B x k := by
        rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_add_distrib, Finset.sum_comm (s := S)
          (t := Finset.univ) (f := fun x k => B x k)]
    _ = ∑ x ∈ S, ∑ k, A x k + ∑ k, ∑ x ∈ S, A x k := by
        simp only [h2]
    _ = 2 * ∑ x ∈ S, ∑ k, A x k := by
        rw [Finset.sum_comm (s := Finset.univ) (t := S) (f := fun k x => A x k)]
        ring

/-- **The Dirichlet form of the cluster on the open edges.** -/
theorem clusterForm_eq_sum_edges (U : TriadicCube 2) (u : Vertex 2 → ℝ) :
    clusterForm ω U (fun x => u x) (fun x => u x) =
      ∑ x ∈ clusterVertices ω U, ∑ k : Fin 2,
        (if x + unit k ∈ clusterVertices ω U ∧ (openGraph ω).Adj x (x + unit k) then
          (u (x + unit k) - u x) ^ 2 else 0) := by
  set S := clusterVertices ω U
  rw [clusterForm_apply]
  have hinner : ∀ x : ↥S, ∑ y : ↥S, clusterFormTerm ω (fun x => u x) (fun x => u x) x y =
      ∑ y ∈ S, (if (openGraph ω).Adj x.1 y then (u x.1 - u y) ^ 2 else 0) := by
    intro x
    rw [← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [clusterFormTerm]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun x _ => hinner x]
  rw [Finset.sum_coe_sort S (fun x => ∑ y ∈ S, if (openGraph ω).Adj x y then (u x - u y) ^ 2
    else 0)]
  rw [sum_sum_openAdj_eq_two_mul S (fun x y => (u x - u y) ^ 2) (fun x y => by ring),
    ← mul_assoc, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

/-- The cluster conductance of a triadic cube: `1` on the open edges with both endpoints in
`C_*(U)`, `0` elsewhere. -/
noncomputable def clusterCond (ω : Configuration 2) (U : TriadicCube 2) (e : Edge 2) : ℝ :=
  if e.1 ∈ clusterVertices ω U ∧ e.1 + unit e.2 ∈ clusterVertices ω U ∧
      (openGraph ω).Adj e.1 (e.1 + unit e.2) then 1 else 0

theorem clusterCond_eq_zero_or (U : TriadicCube 2) (e : Edge 2) :
    clusterCond ω U e = 0 ∨ 1 ≤ clusterCond ω U e := by
  unfold clusterCond
  split_ifs
  · exact Or.inr le_rfl
  · exact Or.inl rfl

theorem clusterCond_nonneg (U : TriadicCube 2) (e : Edge 2) : 0 ≤ clusterCond ω U e := by
  unfold clusterCond
  split_ifs <;> norm_num

theorem clusterCond_le_one (U : TriadicCube 2) (e : Edge 2) : clusterCond ω U e ≤ 1 := by
  unfold clusterCond
  split_ifs <;> norm_num

/-- **The Laplacian of the cluster conductance** is minus the Laplacian of the cluster. -/
theorem condLaplacian_clusterCond (U : TriadicCube 2) (u : Vertex 2 → ℝ) (x : Vertex 2) :
    condLaplacian (clusterCond ω U) u x =
      if x ∈ clusterVertices ω U then
        -∑ y ∈ clusterVertices ω U, (if (openGraph ω).Adj x y then u y - u x else 0) else 0 := by
  set S := clusterVertices ω U
  unfold condLaplacian clusterCond
  by_cases hx : x ∈ S
  · rw [if_pos hx, sum_openAdj_eq S x (fun y => u y - u x), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [sub_add_cancel]
    by_cases h1 : x + unit k ∈ S ∧ (openGraph ω).Adj x (x + unit k)
    · rw [if_pos ⟨hx, h1⟩, if_pos h1]
      by_cases h2 : x - unit k ∈ S ∧ (openGraph ω).Adj x (x - unit k)
      · rw [if_pos ⟨h2.1, hx, h2.2.symm⟩, if_pos h2]
        ring
      · rw [if_neg (fun h => h2 ⟨h.1, h.2.2.symm⟩), if_neg h2]
        ring
    · rw [if_neg (fun h => h1 h.2), if_neg h1]
      by_cases h2 : x - unit k ∈ S ∧ (openGraph ω).Adj x (x - unit k)
      · rw [if_pos ⟨h2.1, hx, h2.2.symm⟩, if_pos h2]
        ring
      · rw [if_neg (fun h => h2 ⟨h.1, h.2.2.symm⟩), if_neg h2]
        ring
  · rw [if_neg hx]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [sub_add_cancel]
    rw [if_neg (fun h => hx h.1), if_neg (fun h => hx h.2.1)]
    ring

/-- **Harmonic functions on the cluster are harmonic for the cluster conductance.** If `u`
restricted to `C_*(U)` is in `A_*(U)`, then `u` is `c_U`-harmonic at every vertex of `U` whose
lattice neighbourhood lies in `U`. -/
theorem condLaplacian_clusterCond_eq_zero {U : TriadicCube 2} {u : Vertex 2 → ℝ}
    (hu : (fun x : ↥(clusterVertices ω U) => u x) ∈ clusterHarmonic ω U) {x : Vertex 2}
    (hx : U.IsInterior x) : condLaplacian (clusterCond ω U) u x = 0 := by
  rw [condLaplacian_clusterCond]
  split_ifs with hxS
  · have h := (mem_clusterHarmonic.1 hu) ⟨x, hxS⟩ hx
    rw [clusterLaplacianAt_apply] at h
    rw [← Finset.sum_coe_sort (clusterVertices ω U)
      (fun y => if (openGraph ω).Adj x y then u y - u x else 0)]
    rw [h, neg_zero]
  · rfl

/-- The energy density of the cluster conductance. -/
noncomputable def clusterEnergy (ω : Configuration 2) (U : TriadicCube 2) (u : Vertex 2 → ℝ)
    (y : Vertex 2) : ℝ :=
  ∑ k : Fin 2, clusterCond ω U (y, k) * (u (y + unit k) - u y) ^ 2

theorem clusterEnergy_nonneg (U : TriadicCube 2) (u : Vertex 2 → ℝ) (y : Vertex 2) :
    0 ≤ clusterEnergy ω U u y :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (clusterCond_nonneg U _) (sq_nonneg _)

/-- **The energy density summed over `U` is the energy of the edges inside `U`.** -/
theorem sum_clusterEnergy_eq_innerEdgeEnergy (U : TriadicCube 2) (u : Vertex 2 → ℝ) :
    ∑ y ∈ U.toIntegerCube.vertices, clusterEnergy ω U u y =
      innerEdgeEnergy (clusterCond ω U) U.toIntegerCube u := by
  unfold clusterEnergy innerEdgeEnergy
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs with h
  · rfl
  · have : clusterCond ω U (y, k) = 0 := by
      unfold clusterCond
      rw [if_neg]
      rintro ⟨-, h2, -⟩
      exact h (Finset.mem_filter.1 h2).1
    rw [this, zero_mul]

/-- A cube inside another has its cluster inside the cluster of the other. -/
theorem planarCubeCluster_subset {T U : TriadicCube 2} (hTU : T.vertices ⊆ U.vertices) :
    planarCubeCluster ω T ⊆ planarCubeCluster ω U := fun _ hx =>
  ⟨hTU hx.1, hx.2.mono hTU⟩

theorem clusterVertices_subset {T U : TriadicCube 2} (hTU : T.vertices ⊆ U.vertices) :
    clusterVertices ω T ⊆ clusterVertices ω U := fun _ hx =>
  mem_clusterVertices.2 (planarCubeCluster_subset hTU (mem_clusterVertices.1 hx))

/-- **The Dirichlet form of a subcube** is at most the energy density of the larger cube summed
over the subcube. -/
theorem clusterForm_le_sum_clusterEnergy {T U : TriadicCube 2} (hTU : T.vertices ⊆ U.vertices)
    (u : Vertex 2 → ℝ) :
    clusterForm ω T (fun x => u x) (fun x => u x) ≤
      ∑ y ∈ T.toIntegerCube.vertices, clusterEnergy ω U u y := by
  rw [clusterForm_eq_sum_edges]
  have hTsub : clusterVertices ω T ⊆ T.toIntegerCube.vertices := Finset.filter_subset _ _
  refine (Finset.sum_le_sum fun x hx => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hTsub fun y _ _ => clusterEnergy_nonneg U u y)
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases h1 : x + unit k ∈ clusterVertices ω T ∧ (openGraph ω).Adj x (x + unit k)
  · have hc : clusterCond ω U (x, k) = 1 := by
      unfold clusterCond
      exact if_pos ⟨clusterVertices_subset hTU hx, clusterVertices_subset hTU h1.1, h1.2⟩
    rw [if_pos h1, hc, one_mul]
  · rw [if_neg h1]
    exact mul_nonneg (clusterCond_nonneg U _) (sq_nonneg _)

end Rigidity.Dirichlet
