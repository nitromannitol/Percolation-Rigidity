import Rigidity.Proofs.Percolation.GeneralDim.CubeVariations

/-!
# Restriction to resolved subcubes in `ℤ^d`

For a vertex `x` and a scale `n`, `triadicCubeAt n x` is the triadic cube of scale `n` containing
`x`, and `U.subcubesAt n` is the set of subcubes of scale `n` of a triadic cube `U`. On the
partition event, if `V ⊆ U` are triadic cubes and `V` is resolved, then every ancestor of `V` is a
good cube, hence the crossing cluster `C_*(V)` lies in `C_*(U)` (the display after Definition 2.9
of Armstrong and Dario). The restriction of a function of `A_*(U)` to `C_*(V)` lies in `A_*(V)`,
its coarsening on `V` is the coarsening on `U`, and the energies of the restrictions to the
clusters of distinct subcubes of the same scale add up to at most the energy on `C_*(U)`. These
are the deterministic facts behind the subadditivity of `μ` and `ν` (Armstrong and Dario,
Lemma 4.8).
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The triadic cube of scale `n` containing a vertex. -/
def triadicCubeAt (n : ℕ) (x : Vertex d) : TriadicCube d := (⟨0, x⟩ : TriadicCube d).ancestor n

theorem mem_vertices_unitCube (x : Vertex d) : x ∈ (⟨0, x⟩ : TriadicCube d).vertices := by
  intro i
  change |2 * (x i - (3 : ℤ) ^ 0 * x i)| < (3 : ℤ) ^ 0
  simp

theorem mem_triadicCubeAt (n : ℕ) (x : Vertex d) : x ∈ (triadicCubeAt n x).vertices :=
  (⟨0, x⟩ : TriadicCube d).vertices_subset_ancestor n (mem_vertices_unitCube x)

theorem scale_triadicCubeAt (n : ℕ) (x : Vertex d) : (triadicCubeAt n x).scale = n := by
  unfold triadicCubeAt
  rw [TriadicCube.scale_ancestor]
  simp

/-- Vertices of the same scale-`n` cube have the same scale-`n` cube. -/
theorem triadicCubeAt_eq_of_mem {n : ℕ} {x y : Vertex d}
    (hy : y ∈ (triadicCubeAt n x).vertices) : triadicCubeAt n y = triadicCubeAt n x :=
  TriadicCube.eq_of_mem_of_scale_eq (by rw [scale_triadicCubeAt, scale_triadicCubeAt])
    (mem_triadicCubeAt n y) hy

/-- A scale-`n` cube containing a vertex of `U`, with `n` at most the scale of `U`, lies in `U`. -/
theorem triadicCubeAt_subset {U : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale) {x : Vertex d}
    (hx : x ∈ U.vertices) : (triadicCubeAt n x).vertices ⊆ U.vertices :=
  TriadicCube.vertices_subset_of_mem_of_scale_le (mem_triadicCubeAt n x) hx
    (by rw [scale_triadicCubeAt]; exact hn)

/-- The subcubes of scale `n` of a triadic cube. -/
noncomputable def TriadicCube.subcubesAt (U : TriadicCube d) (n : ℕ) : Finset (TriadicCube d) :=
  U.toIntegerCube.vertices.image (triadicCubeAt n)

theorem TriadicCube.subset_of_mem_subcubesAt {U V : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale)
    (hV : V ∈ U.subcubesAt n) : V.vertices ⊆ U.vertices := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hV
  exact triadicCubeAt_subset hn ((U.mem_toIntegerCube_vertices x).1 hx)

theorem TriadicCube.scale_of_mem_subcubesAt {U V : TriadicCube d} {n : ℕ}
    (hV : V ∈ U.subcubesAt n) : V.scale = n := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hV
  exact scale_triadicCubeAt n x

theorem TriadicCube.triadicCubeAt_mem_subcubesAt {U : TriadicCube d} (n : ℕ) {x : Vertex d}
    (hx : x ∈ U.vertices) : triadicCubeAt n x ∈ U.subcubesAt n :=
  Finset.mem_image_of_mem _ ((U.mem_toIntegerCube_vertices x).2 hx)

/-- **Fibres of the subcube map.** -/
theorem sum_triadicCubeAt_eq {U : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale)
    (g : TriadicCube d → Vertex d → ℝ) :
    ∑ x ∈ U.toIntegerCube.vertices, g (triadicCubeAt n x) x =
      ∑ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices, g V x := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := triadicCubeAt n) (t := U.subcubesAt n)
    (fun x hx => Finset.mem_image_of_mem _ hx)]
  refine Finset.sum_congr rfl fun V hV => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hV
  have hfib : U.toIntegerCube.vertices.filter (fun x => triadicCubeAt n x = triadicCubeAt n x₀) =
      (triadicCubeAt n x₀).toIntegerCube.vertices := by
    ext x
    rw [Finset.mem_filter, (triadicCubeAt n x₀).mem_toIntegerCube_vertices,
      U.mem_toIntegerCube_vertices]
    constructor
    · rintro ⟨_, hx⟩
      rw [← hx]
      exact mem_triadicCubeAt n x
    · intro hx
      exact ⟨triadicCubeAt_subset hn ((U.mem_toIntegerCube_vertices x₀).1 hx₀) hx,
        triadicCubeAt_eq_of_mem hx⟩
  rw [hfib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [triadicCubeAt_eq_of_mem (((triadicCubeAt n x₀).mem_toIntegerCube_vertices x).1 hx)]

/-- Sums over the vertices of `U` of a quantity of the resolved subcube containing the vertex. -/
theorem sum_vertices_ite_triadicCubeAt_eq {U : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale)
    (f : TriadicCube d → ℝ) :
    ∑ x ∈ U.toIntegerCube.vertices,
        (if PartitionResolved ω (triadicCubeAt n x) then f (triadicCubeAt n x) else 0) =
      ∑ V ∈ (U.subcubesAt n).filter (fun V => PartitionResolved ω V),
        V.latticeVolume * f V := by
  rw [sum_triadicCubeAt_eq hn (fun V _ => if PartitionResolved ω V then f V else 0),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul, V.card_toIntegerCube_vertices]
  split_ifs <;> simp

/-- **Nested crossing clusters.** On the partition event, the crossing cluster of a resolved cube
lies in the crossing cluster of each of its ancestors. -/
theorem crossingCluster_subset_ancestor_of_resolved (hd : 0 < d) (hP : PartitionEvent ω)
    {V : TriadicCube d} (hV : PartitionResolved ω V) (k : ℕ) :
    V.crossingCluster ω ⊆ (V.ancestor k).crossingCluster ω := by
  induction k with
  | zero => simp only [TriadicCube.ancestor_zero, subset_refl]
  | succ k ih =>
    refine ih.trans ?_
    have hz := V.center_mem
    have hA : V.ancestor (k + 1) ∈ TriadicCube.goodCubes ω :=
      mem_goodCubes_of_partitionCube_le hP (V.vertices_subset_ancestor (k + 1) hz)
        (by rw [TriadicCube.scale_ancestor]; have := hV _ hz; omega)
    rw [TriadicCube.ancestor_succ] at hA ⊢
    obtain ⟨root, hroot⟩ := ((V.ancestor k).parent.wellConnectedIn_threeQuarter_iff ω).1 hA.2.1.2
    have h := hroot.crossingCluster_child_subset_crossingCluster hd hA.2.1.1 (V.ancestor k).digit
    rwa [TriadicCube.parent_child] at h

/-- On the partition event, the crossing cluster of a resolved cube `V ⊆ U` lies in the crossing
cluster of `U`. -/
theorem crossingClusterVertices_subset_of_resolved (hd : 0 < d) (hP : PartitionEvent ω)
    {U V : TriadicCube d} (hV : PartitionResolved ω V) (hVU : V.vertices ⊆ U.vertices)
    (hscale : V.scale ≤ U.scale) :
    crossingClusterVertices ω V ⊆ crossingClusterVertices ω U := by
  intro x hx
  have hz := V.center_mem
  rw [TriadicCube.eq_ancestor_of_mem hz (hVU hz) hscale]
  rw [mem_crossingClusterVertices] at hx ⊢
  exact crossingCluster_subset_ancestor_of_resolved hd hP hV _ hx

/-- Distinct subcubes of the same scale have disjoint clusters. -/
theorem pairwiseDisjoint_crossingClusterVertices (U : TriadicCube d) (n : ℕ)
    (T : Finset (TriadicCube d)) (hT : T ⊆ U.subcubesAt n) :
    (↑T : Set (TriadicCube d)).PairwiseDisjoint (fun V => crossingClusterVertices ω V) := by
  intro V hV V' hV' hne
  refine Finset.disjoint_left.2 fun x hx hx' => hne ?_
  exact TriadicCube.eq_of_mem_of_scale_eq
    (by rw [TriadicCube.scale_of_mem_subcubesAt (hT hV),
      TriadicCube.scale_of_mem_subcubesAt (hT hV')])
    (V.crossingCluster_subset ω (mem_crossingClusterVertices.1 hx))
    (V'.crossingCluster_subset ω (mem_crossingClusterVertices.1 hx'))

/-- The coarsening `[u]_𝒫(x)` of a function on the cluster: its value at the anchor of the
partition cube of `x`. -/
noncomputable def cubeCoarsen (ω : Configuration d) (U : TriadicCube d) (u : CubeFun ω U)
    (x : Vertex d) : ℝ :=
  cubeExtend ω U u (partitionAnchor ω x)

/-- The restriction of a function on the cluster of `U` to the cluster of any cube, through the
extension by zero. -/
noncomputable def cubeRestrictExt (V : TriadicCube d) {U : TriadicCube d} (u : CubeFun ω U) :
    CubeFun ω V :=
  fun y => cubeExtend ω U u y.1

theorem cubeExtend_cubeRestrictExt (V : TriadicCube d) {U : TriadicCube d} (u : CubeFun ω U)
    {y : Vertex d} (hy : y ∈ crossingClusterVertices ω V) :
    cubeExtend ω V (cubeRestrictExt V u) y = cubeExtend ω U u y := by
  rw [cubeExtend_apply_of_mem _ hy]
  rfl

/-- Sums over the cluster as a type and as a finite set. -/
theorem sum_cubeFun_eq {U : TriadicCube d} (u : CubeFun ω U) (F : Vertex d → ℝ → ℝ) :
    ∑ z : ↥(crossingClusterVertices ω U), F z.1 (u z) =
      ∑ z ∈ crossingClusterVertices ω U, F z (cubeExtend ω U u z) := by
  rw [← Finset.sum_coe_sort (crossingClusterVertices ω U)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [cubeExtend_apply_of_mem u z.2]

/-- **Restriction preserves harmonicity.** -/
theorem cubeRestrictExt_mem_cubeHarmonic {U V : TriadicCube d} (hVU : V.vertices ⊆ U.vertices)
    (hsub : crossingClusterVertices ω V ⊆ crossingClusterVertices ω U) {u : CubeFun ω U}
    (hu : u ∈ cubeHarmonic ω U) : cubeRestrictExt V u ∈ cubeHarmonic ω V := by
  rw [mem_cubeHarmonic]
  intro y hint
  have hyU : y.1 ∈ crossingClusterVertices ω U := hsub y.2
  have hintU : U.IsLatticeInterior y.1 := fun z hz => hVU (hint z hz)
  have h0 := mem_cubeHarmonic.1 hu ⟨y.1, hyU⟩ hintU
  rw [cubeLaplacianAt_apply] at h0 ⊢
  set c := cubeExtend ω U u y.1 with hc
  have hcV : cubeRestrictExt V u y = c := rfl
  have hcU : u ⟨y.1, hyU⟩ = c := by
    rw [hc, cubeExtend_apply_of_mem u hyU]
  set F : Vertex d → ℝ → ℝ := fun z t => if (openGraph ω).Adj y.1 z then t - c else 0 with hF
  have eV : ∑ z : ↥(crossingClusterVertices ω V),
      (if (openGraph ω).Adj y.1 z.1 then cubeRestrictExt V u z - cubeRestrictExt V u y
        else 0) = ∑ z ∈ crossingClusterVertices ω V, F z (cubeExtend ω U u z) := by
    rw [hcV, ← Finset.sum_coe_sort (crossingClusterVertices ω V)]
    rfl
  have eU : ∑ z : ↥(crossingClusterVertices ω U),
      (if (openGraph ω).Adj y.1 z.1 then u z - u ⟨y.1, hyU⟩ else 0) =
      ∑ z ∈ crossingClusterVertices ω U, F z (cubeExtend ω U u z) := by
    rw [hcU, ← sum_cubeFun_eq u F]
  have esub : ∑ z ∈ crossingClusterVertices ω V, F z (cubeExtend ω U u z) =
      ∑ z ∈ crossingClusterVertices ω U, F z (cubeExtend ω U u z) := by
    refine Finset.sum_subset hsub fun z _ hzV => ?_
    simp only [hF]
    rw [if_neg]
    intro hyz
    exact hzV (mem_crossingClusterVertices.2 (mem_crossingCluster_of_adj
      (mem_crossingClusterVertices.1 y.2) (hint z (openGraph_le ω hyz)) hyz))
  rw [eV, esub, ← eU]
  exact h0

/-- **Restriction commutes with coarsening** at the vertices of a resolved cube. -/
theorem cubeCoarsen_cubeRestrictExt (hd : 0 < d) (hP : PartitionEvent ω) {U V : TriadicCube d}
    (hV : PartitionResolved ω V) (u : CubeFun ω U) {x : Vertex d} (hx : x ∈ V.vertices) :
    cubeCoarsen ω V (cubeRestrictExt V u) x = cubeCoarsen ω U u x :=
  cubeExtend_cubeRestrictExt V u
    (mem_crossingClusterVertices.2 (partitionAnchor_mem_crossingCluster_of_resolved hd hP hV hx))

/-- The energy of a function on the cluster, as a sum over the cluster as a finite set. -/
theorem cubeForm_self_eq_sum {U : TriadicCube d} (u : CubeFun ω U) :
    cubeForm ω U u u = (1 / 2 : ℝ) * ∑ x ∈ crossingClusterVertices ω U,
      ∑ y ∈ crossingClusterVertices ω U,
      (if (openGraph ω).Adj x y then (cubeExtend ω U u x - cubeExtend ω U u y) *
        (cubeExtend ω U u x - cubeExtend ω U u y) else 0) := by
  rw [cubeForm_apply]
  congr 1
  rw [← Finset.sum_coe_sort (crossingClusterVertices ω U)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_coe_sort (crossingClusterVertices ω U)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [cubeFormTerm]
  rw [cubeExtend_apply_of_mem u x.2, cubeExtend_apply_of_mem u y.2]

/-- **Energies of restrictions add up to at most the energy.** -/
theorem sum_cubeForm_restrictExt_le {U : TriadicCube d} {n : ℕ} (T : Finset (TriadicCube d))
    (hT : T ⊆ U.subcubesAt n)
    (hsubU : ∀ V ∈ T, crossingClusterVertices ω V ⊆ crossingClusterVertices ω U)
    (u : CubeFun ω U) :
    ∑ V ∈ T, cubeForm ω V (cubeRestrictExt V u) (cubeRestrictExt V u) ≤ cubeForm ω U u u := by
  set G : Vertex d → Vertex d → ℝ := fun x y => if (openGraph ω).Adj x y then
    (cubeExtend ω U u x - cubeExtend ω U u y) *
      (cubeExtend ω U u x - cubeExtend ω U u y) else 0 with hG
  have hG0 : ∀ x y, 0 ≤ G x y := fun x y => by
    simp only [hG]
    split_ifs
    · exact mul_self_nonneg _
    · exact le_rfl
  have hV : ∀ V ∈ T, cubeForm ω V (cubeRestrictExt V u) (cubeRestrictExt V u) =
      (1 / 2 : ℝ) * ∑ x ∈ crossingClusterVertices ω V, ∑ y ∈ crossingClusterVertices ω V,
        G x y := by
    intro V _
    rw [cubeForm_apply]
    congr 1
    rw [← Finset.sum_coe_sort (crossingClusterVertices ω V)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_coe_sort (crossingClusterVertices ω V)]
    rfl
  rw [Finset.sum_congr rfl hV, ← Finset.mul_sum, cubeForm_self_eq_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc ∑ V ∈ T, ∑ x ∈ crossingClusterVertices ω V, ∑ y ∈ crossingClusterVertices ω V, G x y
      ≤ ∑ V ∈ T, ∑ x ∈ crossingClusterVertices ω V, ∑ y ∈ crossingClusterVertices ω U, G x y :=
        Finset.sum_le_sum fun V hV => Finset.sum_le_sum fun x _ =>
          Finset.sum_le_sum_of_subset_of_nonneg (hsubU V hV) fun y _ _ => hG0 x y
    _ = ∑ x ∈ T.biUnion (fun V => crossingClusterVertices ω V),
          ∑ y ∈ crossingClusterVertices ω U, G x y :=
        (Finset.sum_biUnion (pairwiseDisjoint_crossingClusterVertices U n T hT)).symm
    _ ≤ ∑ x ∈ crossingClusterVertices ω U, ∑ y ∈ crossingClusterVertices ω U, G x y := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ =>
          Finset.sum_nonneg fun y _ => hG0 x y
        intro x hx
        obtain ⟨V, hV, hxV⟩ := Finset.mem_biUnion.1 hx
        exact hsubU V hV hxV

/-- The resolved subcubes of scale `n` of a triadic cube. -/
noncomputable def TriadicCube.resolvedSubcubesAt (ω : Configuration d) (U : TriadicCube d)
    (n : ℕ) : Finset (TriadicCube d) :=
  (U.subcubesAt n).filter (fun V => PartitionResolved ω V)

/-- On the partition event, the clusters of the resolved subcubes lie in the cluster of `U`. -/
theorem crossingClusterVertices_subset_of_mem_resolvedSubcubesAt (hd : 0 < d)
    (hP : PartitionEvent ω) {U V : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale)
    (hV : V ∈ U.resolvedSubcubesAt ω n) :
    crossingClusterVertices ω V ⊆ crossingClusterVertices ω U := by
  obtain ⟨hVS, hVres⟩ := Finset.mem_filter.1 hV
  exact crossingClusterVertices_subset_of_resolved hd hP hVres
    (TriadicCube.subset_of_mem_subcubesAt hn hVS)
    (by rw [TriadicCube.scale_of_mem_subcubesAt hVS]; exact hn)

end Rigidity.Percolation
