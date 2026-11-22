import Rigidity.Proofs.Percolation.GeneralDim.CubeStokes
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuDirichlet

/-!
# The spatial average of the coarsened gradient of the `ν` maximizer, in `ℤ^d`

Let `U` be a resolved triadic cube of `ℤ^d` of side `L`, on the partition event, and let `v`
solve the first variation equation of `ν(U, p)`, so that `v(y) = p · y + c` at the boundary
vertices `y` of the cluster (Lemma 4.3). By the discrete Stokes formula the coarse pairing `ℓ_q v`
is a sum over the faces of `U` of coarsened values. The partition cube `□` of a vertex `x` on a
face of `U` lies in `U`, so it has a face on the same face of `U`, and its crossing cluster, which
lies in `C_*(U)`, meets that face at a boundary vertex `y` of the cluster. The anchor of `□` and
`y` are joined inside the crossing cluster of `□`, so

`|[v]_𝒫(x) - (p · x + c)| ≤ Var(v; C_*(□)) + |p|₁ size(□)`,

and summing over the faces,

`|ℓ_q v - (q · p) L^{d-1} (L - 1)| ≤ |q|₁ ∑_{x ∈ ∂U} (Var(v; C_*(□_𝒫(x))) + |p|₁ size(□_𝒫(x)))`,

the faces being counted with multiplicity (Armstrong and Dario, Lemma 4.5, the inequality (4.27)
on which its proof rests, with the regions of the paths taken inside the boundary partition
cubes).
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

theorem TriadicCube.coord_bounds_of_mem {Q : TriadicCube d} {x : Vertex d}
    (hx : x ∈ Q.vertices) (i : Fin d) :
    Q.toIntegerCube.corner i ≤ x i ∧ x i < Q.toIntegerCube.corner i + 3 ^ Q.scale := by
  have h := ((IntegerCube.mem_vertices _ x).1 ((Q.mem_toIntegerCube_vertices x).2 hx)) i
  have hs : ((Q.toIntegerCube.size : ℕ) : ℤ) = 3 ^ Q.scale := by
    change ((3 ^ Q.scale : ℕ) : ℤ) = _
    push_cast
    rfl
  rw [hs] at h
  exact h

theorem TriadicCube.mem_of_coord_bounds {Q : TriadicCube d} {x : Vertex d}
    (h : ∀ i, Q.toIntegerCube.corner i ≤ x i ∧ x i < Q.toIntegerCube.corner i + 3 ^ Q.scale) :
    x ∈ Q.vertices := by
  have hs : ((Q.toIntegerCube.size : ℕ) : ℤ) = 3 ^ Q.scale := by
    change ((3 ^ Q.scale : ℕ) : ℤ) = _
    push_cast
    rfl
  rw [← Q.mem_toIntegerCube_vertices, IntegerCube.mem_vertices, hs]
  exact h

/-- A triadic cube inside another one has its corners inside the other one. -/
theorem TriadicCube.corner_bounds_of_vertices_subset {Q U : TriadicCube d}
    (h : Q.vertices ⊆ U.vertices) (i : Fin d) :
    U.toIntegerCube.corner i ≤ Q.toIntegerCube.corner i ∧
      Q.toIntegerCube.corner i + 3 ^ Q.scale ≤ U.toIntegerCube.corner i + 3 ^ U.scale := by
  have hpos : (1 : ℤ) ≤ 3 ^ Q.scale := one_le_pow₀ (by norm_num)
  have h0 : Q.toIntegerCube.corner ∈ U.vertices :=
    h (TriadicCube.mem_of_coord_bounds fun j => ⟨le_rfl, by omega⟩)
  have h1 : (fun j => Q.toIntegerCube.corner j + 3 ^ Q.scale - 1) ∈ U.vertices :=
    h (TriadicCube.mem_of_coord_bounds fun j => ⟨by omega, by omega⟩)
  have h0' := TriadicCube.coord_bounds_of_mem h0 i
  have h1' := TriadicCube.coord_bounds_of_mem h1 i
  constructor <;> omega

/-- Two vertices of the crossing cluster of a good cube are joined by an open path inside the
crossing cluster. -/
theorem joinedWithin_crossingClusterVertices_of_mem_goodCubes (hd : 0 < d) {Q : TriadicCube d}
    (hQ : Q ∈ TriadicCube.goodCubes ω) {x y : Vertex d} (hx : x ∈ Q.crossingCluster ω)
    (hy : y ∈ Q.crossingCluster ω) : JoinedWithin ω ↑(crossingClusterVertices ω Q) x y := by
  obtain ⟨root, hroot⟩ := (Q.wellConnectedIn_threeQuarter_iff ω).1 hQ.2.1.2
  have h := hroot.reachable_of_mem_crossingCluster hd hQ.2.1.1 hx hy
  have h2 : (openIn ω (Q.vertices ∩ Set.univ)).Reachable x y := by
    rwa [Set.inter_univ]
  have h' := TriadicCube.reachable_crossingCluster_inter hx h2
  refine (joinedWithin_of_reachable_openIn h' ⟨hx, Set.mem_univ _⟩).mono ?_
  rintro z ⟨hz, -⟩
  exact Finset.mem_coe.2 (mem_crossingClusterVertices.2 hz)

/-- **Boundary vertices of the cluster in boundary partition cubes.** On the partition event and
for a resolved cube `U`, the crossing cluster of the partition cube of a vertex on a face of `U`
contains a vertex of `C_*(U)` outside `int(U)`. -/
theorem exists_boundary_vertex_crossingCluster_partitionCube (hd : 0 < d)
    (hP : PartitionEvent ω) {U : TriadicCube d} (hU : PartitionResolved ω U) {i : Fin d}
    {x : Vertex d} (hx : x ∈ U.toIntegerCube.lowerFace i ∨ x ∈ U.toIntegerCube.upperFace i) :
    ∃ y ∈ (partitionCube ω x).crossingCluster ω, y ∈ U.crossingCluster ω ∧
      ¬ U.IsLatticeInterior y := by
  have hxU : x ∈ U.vertices := by
    rcases hx with hx | hx <;>
      exact (U.mem_toIntegerCube_vertices x).1 (Finset.mem_filter.1 hx).1
  set Q := partitionCube ω x with hQdef
  have hxQ : x ∈ Q.vertices := mem_partitionCube hP x
  have hQU : Q.vertices ⊆ U.vertices :=
    TriadicCube.vertices_subset_of_mem_of_scale_le hxQ hxU (hU x hxU)
  have hG := partitionCube_mem_goodCubes hP x
  obtain ⟨root, hroot⟩ := (Q.wellConnectedIn_threeQuarter_iff ω).1 hG.2.1.2
  have hcross := hroot.1
  have hb := TriadicCube.corner_bounds_of_vertices_subset hQU i
  have hxi := TriadicCube.coord_bounds_of_mem hxQ i
  have hUs : ((U.toIntegerCube.size : ℕ) : ℤ) = 3 ^ U.scale := by
    change ((3 ^ U.scale : ℕ) : ℤ) = _
    push_cast
    rfl
  have hQs : ((Q.toIntegerCube.size : ℕ) : ℤ) = 3 ^ Q.scale := by
    change ((3 ^ Q.scale : ℕ) : ℤ) = _
    push_cast
    rfl
  have hsubU : Q.crossingCluster ω ⊆ U.crossingCluster ω :=
    crossingCluster_partitionCube_subset hd hP hxU (hU x hxU)
  rcases hx with hx | hx
  · have hxi' := (Finset.mem_filter.1 hx).2
    obtain ⟨y, -, hyf, hry⟩ := (hcross.2 i).1
    have hyC : y ∈ Q.crossingCluster ω := ⟨root, hcross, hry⟩
    have hyi := ((IntegerCube.mem_lowerFace _ _ _).1 (Finset.mem_coe.1 hyf)).2
    refine ⟨y, hyC, hsubU hyC, fun hint => ?_⟩
    have hz := hint (y - LatticeProb.unit i) ⟨i, Or.inr (sub_add_cancel y _).symm⟩
    have := (TriadicCube.coord_bounds_of_mem hz i).1
    simp only [Pi.sub_apply, unit_apply_self] at this
    omega
  · have hxi' := (Finset.mem_filter.1 hx).2
    rw [hUs] at hxi'
    obtain ⟨y, -, hyf, hry⟩ := (hcross.2 i).2
    have hyC : y ∈ Q.crossingCluster ω := ⟨root, hcross, hry⟩
    have hyi := ((IntegerCube.mem_upperFace _ _ _).1 (Finset.mem_coe.1 hyf)).2
    rw [hQs] at hyi
    refine ⟨y, hyC, hsubU hyC, fun hint => ?_⟩
    have hz := hint (y + LatticeProb.unit i) ⟨i, Or.inl rfl⟩
    have := (TriadicCube.coord_bounds_of_mem hz i).2
    simp only [Pi.add_apply, unit_apply_self] at this
    omega

/-- The variation of a function over the open edges of the crossing cluster of the partition cube
of a vertex. -/
noncomputable def partitionCubeVariation (ω : Configuration d) (f : Vertex d → ℝ)
    (x : Vertex d) : ℝ :=
  ∑ z ∈ crossingClusterVertices ω (partitionCube ω x),
    vertexVariation ω (crossingClusterVertices ω (partitionCube ω x)) f z

theorem partitionCubeVariation_nonneg (ω : Configuration d) (f : Vertex d → ℝ) (x : Vertex d) :
    0 ≤ partitionCubeVariation ω f x :=
  Finset.sum_nonneg fun _ _ => vertexVariation_nonneg _ _ _ _

/-- An affine function varies by at most `|p|₁ s` across a triadic cube of side `s`. -/
theorem abs_affine_sub_le_of_mem {Q : TriadicCube d} {x y : Vertex d} (hx : x ∈ Q.vertices)
    (hy : y ∈ Q.vertices) (p : Fin d → ℝ) (c : ℝ) :
    |(∑ j, p j * (y j : ℝ) + c) - (∑ j, p j * (x j : ℝ) + c)| ≤
      (∑ j, |p j|) * 3 ^ Q.scale := by
  rw [show (∑ j, p j * (y j : ℝ) + c) - (∑ j, p j * (x j : ℝ) + c) =
      ∑ j, p j * ((y j : ℝ) - x j) by simp only [mul_sub, Finset.sum_sub_distrib]; ring]
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  have h1 := TriadicCube.coord_bounds_of_mem hy j
  have h2 := TriadicCube.coord_bounds_of_mem hx j
  have h : |y j - x j| ≤ 3 ^ Q.scale := by
    rw [abs_le]
    constructor <;> omega
  have h' : |(y j : ℝ) - x j| ≤ (3 : ℝ) ^ Q.scale := by exact_mod_cast h
  exact mul_le_mul_of_nonneg_left h' (abs_nonneg _)

/-- **Boundary values of the coarsened maximizer.** -/
theorem abs_cubeCoarsen_sub_affine_le (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (p : Fin d → ℝ) {v : CubeFun ω U} {c : ℝ}
    (hc : ∀ x : ↥(crossingClusterVertices ω U), ¬ U.IsLatticeInterior x.1 →
      v x = ∑ i, p i * (x.1 i : ℝ) + c)
    {i : Fin d} {x : Vertex d}
    (hx : x ∈ U.toIntegerCube.lowerFace i ∨ x ∈ U.toIntegerCube.upperFace i) :
    |cubeCoarsen ω U v x - (∑ j, p j * (x j : ℝ) + c)| ≤
      partitionCubeVariation ω (cubeExtend ω U v) x +
        (∑ j, |p j|) * 3 ^ (partitionCube ω x).scale := by
  obtain ⟨y, hyQ, hyC, hyb⟩ := exists_boundary_vertex_crossingCluster_partitionCube hd hP hU hx
  have hyCV : y ∈ crossingClusterVertices ω U := mem_crossingClusterVertices.2 hyC
  have hvy : cubeExtend ω U v y = ∑ j, p j * (y j : ℝ) + c := by
    rw [cubeExtend_apply_of_mem v hyCV]
    exact hc ⟨y, hyCV⟩ hyb
  have hjoin := joinedWithin_crossingClusterVertices_of_mem_goodCubes hd
    (partitionCube_mem_goodCubes hP x) (partitionAnchor_mem_crossingCluster hP x) hyQ
  have h1 := abs_sub_le_sum_vertexVariation _ (cubeExtend ω U v) hjoin
  rw [hvy] at h1
  have h2 := abs_affine_sub_le_of_mem (mem_partitionCube hP x)
    ((partitionCube ω x).crossingCluster_subset ω hyQ) p c
  have htri := abs_sub_le (cubeCoarsen ω U v x) (∑ j, p j * (y j : ℝ) + c)
    (∑ j, p j * (x j : ℝ) + c)
  have h1' : |cubeCoarsen ω U v x - (∑ j, p j * (y j : ℝ) + c)| ≤
      partitionCubeVariation ω (cubeExtend ω U v) x := h1
  linarith

/-- The boundary error: the variations over the crossing clusters of the boundary partition
cubes plus the sides of these cubes, summed over the faces of `U`. -/
noncomputable def cubeBoundaryError (ω : Configuration d) (U : TriadicCube d) (p : Fin d → ℝ)
    (v : CubeFun ω U) : ℝ :=
  ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i,
      (partitionCubeVariation ω (cubeExtend ω U v) x +
        (∑ j, |p j|) * 3 ^ (partitionCube ω x).scale) +
    ∑ x ∈ U.toIntegerCube.lowerFace i,
      (partitionCubeVariation ω (cubeExtend ω U v) x +
        (∑ j, |p j|) * 3 ^ (partitionCube ω x).scale))

theorem cubeBoundaryError_nonneg (ω : Configuration d) (U : TriadicCube d) (p : Fin d → ℝ)
    (v : CubeFun ω U) : 0 ≤ cubeBoundaryError ω U p v :=
  Finset.sum_nonneg fun _ _ => add_nonneg
    (Finset.sum_nonneg fun _ _ => add_nonneg (partitionCubeVariation_nonneg _ _ _)
      (by positivity))
    (Finset.sum_nonneg fun _ _ => add_nonneg (partitionCubeVariation_nonneg _ _ _)
      (by positivity))

/-- **Spatial average of the coarsened gradient** (Armstrong and Dario, Lemma 4.5, the
deterministic inequality (4.27)). -/
theorem abs_cubeCoarsePairing_sub_le (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (p q : Fin d → ℝ) {v : CubeFun ω U} {c : ℝ}
    (hc : ∀ x : ↥(crossingClusterVertices ω U), ¬ U.IsLatticeInterior x.1 →
      v x = ∑ i, p i * (x.1 i : ℝ) + c) :
    |cubeCoarsePairing ω U q v - (∑ i, q i * p i) *
        ((U.toIntegerCube.size : ℝ) ^ (d - 1) * ((U.toIntegerCube.size : ℝ) - 1))| ≤
      (∑ i, |q i|) * cubeBoundaryError ω U p v := by
  set g : Vertex d → ℝ := fun x => ∑ j, p j * (x j : ℝ) + c with hg
  have hsize : 0 < U.toIntegerCube.size := by
    change 0 < 3 ^ U.scale
    positivity
  have haff : ∀ i, ∑ x ∈ U.toIntegerCube.upperFace i, g x -
      ∑ x ∈ U.toIntegerCube.lowerFace i, g x =
      p i * ((U.toIntegerCube.size : ℝ) ^ (d - 1) * ((U.toIntegerCube.size : ℝ) - 1)) := by
    intro i
    rw [← U.toIntegerCube.cast_card_edgeStartsIn hsize i]
    exact U.toIntegerCube.sum_face_affine_eq_mul_card i p c
  have hdiff : cubeCoarsePairing ω U q v - (∑ i, q i * p i) *
      ((U.toIntegerCube.size : ℝ) ^ (d - 1) * ((U.toIntegerCube.size : ℝ) - 1)) =
      ∑ i, q i * (∑ x ∈ U.toIntegerCube.upperFace i, (cubeCoarsen ω U v x - g x) -
        ∑ x ∈ U.toIntegerCube.lowerFace i, (cubeCoarsen ω U v x - g x)) := by
    rw [cubeCoarsePairing_eq_faces, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, mul_assoc, ← haff i]
    ring
  rw [hdiff, cubeBoundaryError, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have hqi : |q i| ≤ ∑ j, |q j| :=
    Finset.single_le_sum (f := fun j => |q j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hface : ∀ (F : Finset (Vertex d)), (∀ x ∈ F, x ∈ U.toIntegerCube.lowerFace i ∨
      x ∈ U.toIntegerCube.upperFace i) →
      |∑ x ∈ F, (cubeCoarsen ω U v x - g x)| ≤ ∑ x ∈ F,
        (partitionCubeVariation ω (cubeExtend ω U v) x +
          (∑ j, |p j|) * 3 ^ (partitionCube ω x).scale) := by
    intro F hF
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx =>
      abs_cubeCoarsen_sub_affine_le hd hP hU p hc (hF x hx))
  have hup := hface (U.toIntegerCube.upperFace i) fun x hx => Or.inr hx
  have hlow := hface (U.toIntegerCube.lowerFace i) fun x hx => Or.inl hx
  have hnn : 0 ≤ ∑ x ∈ U.toIntegerCube.upperFace i,
      (partitionCubeVariation ω (cubeExtend ω U v) x +
        (∑ j, |p j|) * 3 ^ (partitionCube ω x).scale) +
      ∑ x ∈ U.toIntegerCube.lowerFace i,
      (partitionCubeVariation ω (cubeExtend ω U v) x +
        (∑ j, |p j|) * 3 ^ (partitionCube ω x).scale) :=
    add_nonneg (Finset.sum_nonneg fun _ _ => add_nonneg (partitionCubeVariation_nonneg _ _ _)
      (by positivity)) (Finset.sum_nonneg fun _ _ => add_nonneg
        (partitionCubeVariation_nonneg _ _ _) (by positivity))
  calc |q i| * |∑ x ∈ U.toIntegerCube.upperFace i, (cubeCoarsen ω U v x - g x) -
        ∑ x ∈ U.toIntegerCube.lowerFace i, (cubeCoarsen ω U v x - g x)|
      ≤ |q i| * (|∑ x ∈ U.toIntegerCube.upperFace i, (cubeCoarsen ω U v x - g x)| +
          |∑ x ∈ U.toIntegerCube.lowerFace i, (cubeCoarsen ω U v x - g x)|) := by
        gcongr
        exact abs_sub _ _
    _ ≤ (∑ j, |q j|) * (∑ x ∈ U.toIntegerCube.upperFace i,
          (partitionCubeVariation ω (cubeExtend ω U v) x +
            (∑ j, |p j|) * 3 ^ (partitionCube ω x).scale) +
        ∑ x ∈ U.toIntegerCube.lowerFace i,
          (partitionCubeVariation ω (cubeExtend ω U v) x +
            (∑ j, |p j|) * 3 ^ (partitionCube ω x).scale)) :=
        mul_le_mul hqi (add_le_add hup hlow) (by positivity) (by positivity)

end Rigidity.Percolation
