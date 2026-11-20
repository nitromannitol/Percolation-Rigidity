import Rigidity.Proofs.Percolation.PlanarStokes
import Rigidity.Proofs.Percolation.PlanarNuDirichlet

/-!
# The spatial average of the coarsened gradient of the `ν` maximizer

Let `v` solve the first-variation equation of `ν(U, p)` for a resolved cube `U` of side `L`. By
the discrete Stokes formula, the coarse pairing `ℓ_q v` is a sum of boundary terms. At a vertex `x`
on a face of `U`, the partition cube of `x` contains a boundary vertex `y` of the cluster on the
same face, where `v(y) = p · y + c`; the coarsened value at `x` is `v` at the anchor of the
partition cube, joined to `y` inside the window of the cube. Hence

`|ℓ_q v - (q · p) L (L - 1)| ≤ |q|₁ ∑_{x on ∂U} (Var(v; window of x) + |p|₁ s_x)`,

where `s_x` is the side of the partition cube of `x`. With the Cauchy–Schwarz inequality and the
energy bound for `v`, the variation term is at most `|q|₁ (9 ∑ W_∂²)^{1/2} (2 B v v)^{1/2}`, where
`W_∂(a)` counts the boundary vertices whose window contains `a` (Armstrong and Dario, Lemma 4.5).
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The coarsening of a function on the cluster: its value at the anchor of the partition cube. -/
noncomputable def coarsen (ω : Configuration 2) (U : TriadicCube 2) (u : ClusterFun ω U)
    (x : Vertex 2) : ℝ :=
  clusterExtend ω U u (planarCoarseAnchor ω x)

/-- The coarse pairing as a sum over the faces of `U`. -/
theorem coarsePairing_eq_faces {U : TriadicCube 2} (q : Fin 2 → ℝ) (u : ClusterFun ω U) :
    coarsePairing ω U q u = ∑ i, q i * (∑ x ∈ U.toIntegerCube.upperFace i, coarsen ω U u x -
      ∑ x ∈ U.toIntegerCube.lowerFace i, coarsen ω U u x) := by
  rw [coarsePairing_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← IntegerCube.sum_edgeStarts_sub, Finset.mul_sum, IntegerCube.edgeStarts,
    Finset.sum_filter]
  rfl

/-- **Boundary vertices of the cluster in boundary partition cubes.** The partition cube of a
vertex on a face of a resolved cube `U` contains a vertex of the cluster on the same face. -/
theorem exists_boundary_cluster_vertex (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {i : Fin 2} {x : Vertex 2}
    (hx : x ∈ U.toIntegerCube.lowerFace i ∨ x ∈ U.toIntegerCube.upperFace i) :
    ∃ y ∈ (planarPartCube ω x).vertices, y ∈ planarCubeCluster ω U ∧ ¬ U.IsInterior y := by
  have hxU : x ∈ U.vertices := by
    rcases hx with hx | hx <;>
      exact (U.mem_toIntegerCube_vertices x).1 (Finset.mem_filter.1 hx).1
  set Q := planarPartCube ω x with hQdef
  have hxQ : x ∈ Q.vertices := (planarPartCube_spec hP x).1
  have hQU := planarPartCube_subset_of_resolved hP hU hxU
  have hmesh : Q.planarMeshed ω := (planarPartCube_meshed hP x).1
  have hs : 1000 ≤ 3 ^ Q.scale := planarPartCube_large hP x
  obtain ⟨-, hA, -⟩ := Q.planarAnchor_spec hmesh hs
  set w := 3 ^ Q.scale / 100
  have hw100 : 100 * w ≤ 3 ^ Q.scale := Nat.mul_div_le _ _
  have hwQ : w + 1 ≤ Q.toIntegerCube.size := by
    change w + 1 ≤ 3 ^ Q.scale
    omega
  obtain ⟨_hub, -, -, hfaces⟩ := (hmesh _ Q.toIntegerCube_mem_planarSquares).exists_hub hwQ
  obtain ⟨⟨yl, hylQ, hylf, hhl⟩, ⟨yu, hyuQ, hyuf, hhu⟩⟩ := hfaces i
  have hyl0 := (IntegerCube.mem_lowerFace_coe.1 hylf).2
  have hyu0 := (IntegerCube.mem_upperFace_coe.1 hyuf).2
  have hQset := Q.coe_toIntegerCube_vertices
  have hcross : ReachIn ω Q.vertices yl yu := hQset ▸ (hhl.symm.trans hhu)
  have hsz := Q.cast_toIntegerCube_size
  have hw100' : 100 * (w : ℤ) ≤ 3 ^ Q.scale := by exact_mod_cast hw100
  have hpos : (1000 : ℤ) ≤ 3 ^ Q.scale := by exact_mod_cast hs
  have hdisp : yl i + (w : ℤ) ≤ yu i := by omega
  have hAyl : ReachIn ω Q.vertices (Q.planarAnchor ω) yl := hA yl yu i hcross hdisp
  have hylQ' : yl ∈ Q.vertices := hQset ▸ hylQ
  have hyuQ' : yu ∈ Q.vertices := hQset ▸ hyuQ
  have hylC : yl ∈ planarCubeCluster ω U :=
    mem_planarCubeCluster_of_reachIn hP hU (hQU hylQ') hxU (hAyl.symm.mono hQU)
  have hyuC : yu ∈ planarCubeCluster ω U :=
    mem_planarCubeCluster_of_reachIn hP hU (hQU hyuQ') hxU
      ((hAyl.trans hcross).symm.mono hQU)
  have hb := TriadicCube.corner_bounds_of_subset hQU i
  have hxi := TriadicCube.corner_le_of_mem hxQ i
  have hUs := U.cast_toIntegerCube_size
  rcases hx with hx | hx
  · have hxi' := (Finset.mem_filter.1 hx).2
    refine ⟨yl, hylQ', hylC, fun hint => ?_⟩
    have hz := hint (yl - unitVertex i) fun j => by
      by_cases hj : j = i
      · subst hj
        simp [unitVertex_apply_self]
      · simp [unitVertex_apply_ne hj]
    have := (TriadicCube.corner_le_of_mem hz i).1
    simp only [Pi.sub_apply, unitVertex_apply_self] at this
    omega
  · have hxi' := (Finset.mem_filter.1 hx).2
    rw [hUs] at hxi'
    refine ⟨yu, hyuQ', hyuC, fun hint => ?_⟩
    have hz := hint (yu + unitVertex i) fun j => by
      by_cases hj : j = i
      · subst hj
        simp [unitVertex_apply_self]
      · simp [unitVertex_apply_ne hj]
    have := (TriadicCube.corner_le_of_mem hz i).2
    simp only [Pi.add_apply, unitVertex_apply_self] at this
    rw [hsz] at hyu0
    omega

/-- **Boundary values of the coarsened maximizer.** -/
theorem abs_coarsen_sub_affine_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (p : Fin 2 → ℝ) {v : ClusterFun ω U} {c : ℝ}
    (hc : ∀ x : ↥(clusterVertices ω U), ¬ U.IsInterior x.1 →
      v x = ∑ i, p i * (x.1 i : ℝ) + c)
    {i : Fin 2} {x : Vertex 2}
    (hx : x ∈ U.toIntegerCube.lowerFace i ∨ x ∈ U.toIntegerCube.upperFace i) :
    |coarsen ω U v x - (∑ j, p j * (x j : ℝ) + c)| ≤
      edgeVariationIn ω (planarClusterWindow ω U x) (clusterExtend ω U v) +
        (|p 0| + |p 1|) * 3 ^ (planarPartCube ω x).scale := by
  obtain ⟨y, hyQ, hyC, hyb⟩ := exists_boundary_cluster_vertex hP hU hx
  have hxQ := (planarPartCube_spec hP x).1
  have hQy : planarPartCube ω y = planarPartCube ω x := planarPartCube_eq_of_mem hP hyQ
  have hyCV : y ∈ clusterVertices ω U := mem_clusterVertices.2 hyC
  have hvy : clusterExtend ω U v y = ∑ j, p j * (y j : ℝ) + c := by
    rw [clusterExtend_apply_of_mem v hyCV]
    exact hc ⟨y, hyCV⟩ hyb
  have h1 := abs_sub_coarseAnchor_le_clusterWindow hP hU hyC (clusterExtend ω U v)
  have hw : planarClusterWindow ω U y = planarClusterWindow ω U x := by
    unfold planarClusterWindow
    rw [hQy]
  have ha : planarCoarseAnchor ω y = planarCoarseAnchor ω x := by
    unfold planarCoarseAnchor
    rw [hQy]
  rw [hw, ha, hvy] at h1
  have hcoord : ∀ j, |(y j : ℝ) - x j| ≤ (3 : ℝ) ^ (planarPartCube ω x).scale := by
    intro j
    have h1 := TriadicCube.corner_le_of_mem hyQ j
    have h2 := TriadicCube.corner_le_of_mem hxQ j
    have : |y j - x j| ≤ 3 ^ (planarPartCube ω x).scale := by
      rw [abs_le]
      constructor <;> omega
    exact_mod_cast this
  have hpx : |(∑ j, p j * (y j : ℝ) + c) - (∑ j, p j * (x j : ℝ) + c)| ≤
      (|p 0| + |p 1|) * 3 ^ (planarPartCube ω x).scale := by
    simp only [Fin.sum_univ_two]
    rw [show p 0 * (y 0 : ℝ) + p 1 * (y 1 : ℝ) + c - (p 0 * (x 0 : ℝ) + p 1 * (x 1 : ℝ) + c) =
      p 0 * ((y 0 : ℝ) - x 0) + p 1 * ((y 1 : ℝ) - x 1) by ring]
    calc |p 0 * ((y 0 : ℝ) - x 0) + p 1 * ((y 1 : ℝ) - x 1)|
        ≤ |p 0| * |(y 0 : ℝ) - x 0| + |p 1| * |(y 1 : ℝ) - x 1| := by
          rw [← abs_mul, ← abs_mul]
          exact abs_add_le _ _
      _ ≤ |p 0| * 3 ^ (planarPartCube ω x).scale + |p 1| * 3 ^ (planarPartCube ω x).scale := by
          gcongr
          · exact hcoord 0
          · exact hcoord 1
      _ = (|p 0| + |p 1|) * 3 ^ (planarPartCube ω x).scale := by ring
  have htri := abs_sub_le (coarsen ω U v x) (∑ j, p j * (y j : ℝ) + c)
    (∑ j, p j * (x j : ℝ) + c)
  have h1' : |coarsen ω U v x - (∑ j, p j * (y j : ℝ) + c)| ≤
      edgeVariationIn ω (planarClusterWindow ω U x) (clusterExtend ω U v) := by
    rw [abs_sub_comm]
    exact h1
  linarith

/-- The boundary error: variation over the windows plus the sides of the partition cubes, summed
over the faces of `U`. -/
noncomputable def boundaryError (ω : Configuration 2) (U : TriadicCube 2) (p : Fin 2 → ℝ)
    (v : ClusterFun ω U) : ℝ :=
  ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i,
      (edgeVariationIn ω (planarClusterWindow ω U x) (clusterExtend ω U v) +
        (|p 0| + |p 1|) * 3 ^ (planarPartCube ω x).scale) +
    ∑ x ∈ U.toIntegerCube.lowerFace i,
      (edgeVariationIn ω (planarClusterWindow ω U x) (clusterExtend ω U v) +
        (|p 0| + |p 1|) * 3 ^ (planarPartCube ω x).scale))

/-- **Spatial average of the coarsened gradient** (planar form of Armstrong and Dario,
Lemma 4.5, first step). -/
theorem abs_coarsePairing_sub_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (p q : Fin 2 → ℝ) {v : ClusterFun ω U} {c : ℝ}
    (hc : ∀ x : ↥(clusterVertices ω U), ¬ U.IsInterior x.1 →
      v x = ∑ i, p i * (x.1 i : ℝ) + c) :
    |coarsePairing ω U q v - (∑ i, q i * p i) *
        ((U.toIntegerCube.size : ℝ) * ((U.toIntegerCube.size : ℝ) - 1))| ≤
      (|q 0| + |q 1|) * boundaryError ω U p v := by
  set g : Vertex 2 → ℝ := fun x => ∑ j, p j * (x j : ℝ) + c with hg
  have haff : ∀ i, ∑ x ∈ U.toIntegerCube.upperFace i, g x -
      ∑ x ∈ U.toIntegerCube.lowerFace i, g x =
      p i * ((U.toIntegerCube.size : ℝ) * ((U.toIntegerCube.size : ℝ) - 1)) :=
    fun i => U.toIntegerCube.sum_face_affine i p c
  have hdiff : coarsePairing ω U q v - (∑ i, q i * p i) *
      ((U.toIntegerCube.size : ℝ) * ((U.toIntegerCube.size : ℝ) - 1)) =
      ∑ i, q i * (∑ x ∈ U.toIntegerCube.upperFace i, (coarsen ω U v x - g x) -
        ∑ x ∈ U.toIntegerCube.lowerFace i, (coarsen ω U v x - g x)) := by
    rw [coarsePairing_eq_faces, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, mul_assoc, ← haff i]
    ring
  rw [hdiff, boundaryError, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have hqi : |q i| ≤ |q 0| + |q 1| := by
    fin_cases i
    · simp
    · simp
  have hface : ∀ (F : Finset (Vertex 2)), (∀ x ∈ F, x ∈ U.toIntegerCube.lowerFace i ∨
      x ∈ U.toIntegerCube.upperFace i) →
      |∑ x ∈ F, (coarsen ω U v x - g x)| ≤ ∑ x ∈ F,
        (edgeVariationIn ω (planarClusterWindow ω U x) (clusterExtend ω U v) +
          (|p 0| + |p 1|) * 3 ^ (planarPartCube ω x).scale) := by
    intro F hF
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx =>
      abs_coarsen_sub_affine_le hP hU p hc (hF x hx))
  have hup := hface (U.toIntegerCube.upperFace i) fun x hx => Or.inr hx
  have hlow := hface (U.toIntegerCube.lowerFace i) fun x hx => Or.inl hx
  have hnn : 0 ≤ ∑ x ∈ U.toIntegerCube.upperFace i,
      (edgeVariationIn ω (planarClusterWindow ω U x) (clusterExtend ω U v) +
        (|p 0| + |p 1|) * 3 ^ (planarPartCube ω x).scale) +
      ∑ x ∈ U.toIntegerCube.lowerFace i,
      (edgeVariationIn ω (planarClusterWindow ω U x) (clusterExtend ω U v) +
        (|p 0| + |p 1|) * 3 ^ (planarPartCube ω x).scale) :=
    add_nonneg (Finset.sum_nonneg fun _ _ => add_nonneg (edgeVariationIn_nonneg _ _ _)
      (by positivity)) (Finset.sum_nonneg fun _ _ => add_nonneg (edgeVariationIn_nonneg _ _ _)
      (by positivity))
  calc |q i| * |∑ x ∈ U.toIntegerCube.upperFace i, (coarsen ω U v x - g x) -
        ∑ x ∈ U.toIntegerCube.lowerFace i, (coarsen ω U v x - g x)|
      ≤ |q i| * (|∑ x ∈ U.toIntegerCube.upperFace i, (coarsen ω U v x - g x)| +
          |∑ x ∈ U.toIntegerCube.lowerFace i, (coarsen ω U v x - g x)|) := by
        gcongr
        exact abs_sub _ _
    _ ≤ (|q 0| + |q 1|) * (∑ x ∈ U.toIntegerCube.upperFace i,
          (edgeVariationIn ω (planarClusterWindow ω U x) (clusterExtend ω U v) +
            (|p 0| + |p 1|) * 3 ^ (planarPartCube ω x).scale) +
        ∑ x ∈ U.toIntegerCube.lowerFace i,
          (edgeVariationIn ω (planarClusterWindow ω U x) (clusterExtend ω U v) +
            (|p 0| + |p 1|) * 3 ^ (planarPartCube ω x).scale)) :=
        mul_le_mul hqi (add_le_add hup hlow) (by positivity) (by positivity)

end Rigidity.Percolation
