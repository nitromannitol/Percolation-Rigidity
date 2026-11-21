import Rigidity.Proofs.Cluster.CoarseReach
import Rigidity.Proofs.Partition.Resolved

/-!
# Coarse-graining data of a cube resolved by the partition into good cubes

For a configuration of the partition event in dimension `d ≥ 1` and a triadic cube `U` containing
the partition cubes of its vertices, the domain `U`, the crossing cluster `C_*(U)`, the partition
cubes with their anchors, the regions `□.parent ∪ (x + Q_{s-1})` of the local paths from the
vertices of `C_*(U)` to their anchors, and the unions of the partition cubes of lattice neighbours
form coarse-graining data.

Lemma 3.3 of Armstrong and Dario then holds in its stated form, with the weights
`size(□_𝒫(z))^{sd-1}`, since the pair regions lie in the two partition cubes (Armstrong and Dario,
Lemma 2.8) and neighbouring partition cubes differ by at most one scale (Proposition 2.1 (ii)). The
regions of Lemma 3.2 lie in the cube of side `3s` around the vertex, hence in the `3s`-neighbourhood
of its partition cube, but they may meet much smaller partition cubes: Lemma 3.2 holds with the
reach scale.
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- Every vertex of an open walk inside `B` starting in `B` lies in `B`. -/
theorem mem_of_mem_support_openIn_walk {B : Set (Vertex d)} :
    ∀ {x y : Vertex d} (W : (openIn ω B).Walk x y), x ∈ B → ∀ v ∈ W.support, v ∈ B
  | _, _, .nil, hx, v, hv => by
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
      exact hv ▸ hx
  | _, _, .cons h p, hx, v, hv => by
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hx
      · exact mem_of_mem_support_openIn_walk p h.2.2 v hv

/-- Reachability in the open graph inside `B` from a vertex of `B` is an open path inside `B`. -/
theorem joinedWithin_of_reachable_openIn {B : Set (Vertex d)} {x y : Vertex d}
    (h : (openIn ω B).Reachable x y) (hx : x ∈ B) : JoinedWithin ω B x y := by
  obtain ⟨W⟩ := h
  refine ⟨W.mapLe (show openIn ω B ≤ openGraph ω from fun _ _ h => h.1), fun v hv => ?_⟩
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
  exact mem_of_mem_support_openIn_walk W hx v hv

/-- A triadic cube is resolved by the partition when it contains the partition cubes of its
vertices. -/
def PartitionResolved (ω : Configuration d) (U : TriadicCube d) : Prop :=
  ∀ z ∈ U.vertices, (partitionCube ω z).scale ≤ U.scale

/-- The vertices of the crossing cluster `C_*(U)` of a triadic cube, as a finite set. -/
noncomputable def crossingClusterVertices (ω : Configuration d) (U : TriadicCube d) :
    Finset (Vertex d) :=
  U.toIntegerCube.vertices.filter (· ∈ U.crossingCluster ω)

theorem mem_crossingClusterVertices {U : TriadicCube d} {x : Vertex d} :
    x ∈ crossingClusterVertices ω U ↔ x ∈ U.crossingCluster ω := by
  unfold crossingClusterVertices
  rw [Finset.mem_filter, U.mem_toIntegerCube_vertices]
  exact ⟨fun h => h.2, fun h => ⟨U.crossingCluster_subset ω h, h⟩⟩

/-- The region of the local path from a vertex of `C_*(U)` to the anchor of its partition cube:
the parent of the partition cube and the cube of side `2s - 1` around the vertex, inside `U`. -/
noncomputable def partitionRegion (ω : Configuration d) (U : TriadicCube d) (x : Vertex d) :
    Finset (Vertex d) :=
  U.toIntegerCube.vertices.filter fun y =>
    y ∈ (partitionCube ω x).parent.vertices ∪ cubeAt x (3 ^ (partitionCube ω x).scale - 1)

/-- The region of the local path between the anchors of two lattice neighbours: the union of
their partition cubes, inside `U`. -/
noncomputable def partitionPairRegion (ω : Configuration d) (U : TriadicCube d) (x y : Vertex d) :
    Finset (Vertex d) :=
  U.toIntegerCube.vertices.filter fun z =>
    z ∈ (partitionCube ω x).vertices ∪ (partitionCube ω y).vertices

/-- **Coarse-graining data of a cube resolved by the partition into good cubes**: domain `U`,
cluster `C_*(U)`, the partition cubes and their anchors, the regions `partitionRegion` and the pair
regions `partitionPairRegion`. -/
noncomputable def partitionCoarseData (hd : 0 < d) (hP : PartitionEvent ω) (U : TriadicCube d)
    (hU : PartitionResolved ω U) : CoarseData d ω where
  domain := U.toIntegerCube.vertices
  cluster := crossingClusterVertices ω U
  cluster_subset := Finset.filter_subset _ _
  part := partitionCube ω
  mem_part x _ := mem_partitionCube hP x
  part_subset x hx y hy := by
    rw [TriadicCube.mem_toIntegerCube_vertices] at hx
    rw [Finset.mem_coe, TriadicCube.mem_toIntegerCube_vertices]
    exact TriadicCube.vertices_subset_of_mem_of_scale_le (mem_partitionCube hP x) hx (hU x hx) hy
  part_eq_of_mem _ _ _ hy := partitionCube_eq_of_mem hP hy
  anchor := partitionAnchor ω
  anchor_congr x y h := by
    unfold partitionAnchor
    rw [h]
  anchor_mem x hx := by
    rw [TriadicCube.mem_toIntegerCube_vertices] at hx
    exact mem_crossingClusterVertices.2 (crossingCluster_partitionCube_subset hd hP hx (hU x hx)
      (partitionAnchor_mem_crossingCluster hP x))
  anchor_mem_part x _ := partitionAnchor_mem hP x
  region := partitionRegion ω U
  joinedWithin_region x hx := by
    have hxC := mem_crossingClusterVertices.1 hx
    have hxU := U.crossingCluster_subset ω hxC
    have h := reachable_partitionAnchor_of_mem_crossingCluster hd hP hxU (hU x hxU) hxC
    have hxB : x ∈ U.crossingCluster ω ∩ ((partitionCube ω x).parent.vertices ∪
        cubeAt x (3 ^ (partitionCube ω x).scale - 1)) :=
      ⟨hxC, Or.inr (by simp [cubeAt])⟩
    refine (joinedWithin_of_reachable_openIn h hxB).mono ?_
    rintro y ⟨hyC, hyR⟩
    have hyU := U.crossingCluster_subset ω hyC
    exact Finset.mem_coe.2 (Finset.mem_inter.2 ⟨Finset.mem_filter.2
      ⟨(U.mem_toIntegerCube_vertices y).2 hyU, hyR⟩, mem_crossingClusterVertices.2 hyC⟩)
  pairRegion := partitionPairRegion ω U
  joinedWithin_pairRegion x hx y hy hadj _ := by
    rw [TriadicCube.mem_toIntegerCube_vertices] at hx hy
    have h := reachable_partitionAnchor_of_adj_of_le hd hP hx hy (hU x hx) (hU y hy) hadj
    have hA : partitionAnchor ω x ∈ U.crossingCluster ω ∩
        ((partitionCube ω x).vertices ∪ (partitionCube ω y).vertices) :=
      ⟨crossingCluster_partitionCube_subset hd hP hx (hU x hx)
        (partitionAnchor_mem_crossingCluster hP x), Or.inl (partitionAnchor_mem hP x)⟩
    refine (joinedWithin_of_reachable_openIn h hA).mono ?_
    rintro z ⟨hzC, hzR⟩
    have hzU := U.crossingCluster_subset ω hzC
    exact Finset.mem_coe.2 (Finset.mem_inter.2 ⟨Finset.mem_filter.2
      ⟨(U.mem_toIntegerCube_vertices z).2 hzU, hzR⟩, mem_crossingClusterVertices.2 hzC⟩)

/-- A cube of radius `r ≤ k s` around a vertex of a triadic cube of side `s` lies in its
`k s`-neighbourhood. -/
theorem TriadicCube.cubeAt_subset_thicken {Q : TriadicCube d} {x : Vertex d}
    (hx : x ∈ Q.vertices) {k r : ℕ} (hr : r ≤ k * 3 ^ Q.scale) :
    cubeAt x r ⊆ ↑(Q.thicken k).vertices := by
  rw [← Q.mem_toIntegerCube_vertices, IntegerCube.mem_vertices] at hx
  intro y hy
  have hy' : ∀ i, |y i - x i| ≤ (r : ℤ) := hy
  rw [Finset.mem_coe, IntegerCube.mem_vertices]
  intro i
  obtain ⟨h1, h2⟩ := hx i
  have h3 := abs_le.1 (hy' i)
  have hs : (Q.toIntegerCube.size : ℤ) = ((3 ^ Q.scale : ℕ) : ℤ) := rfl
  have hr' : (r : ℤ) ≤ (k : ℤ) * (Q.toIntegerCube.size : ℤ) := by
    rw [hs]
    exact_mod_cast hr
  change Q.toIntegerCube.corner i - (k : ℤ) * (Q.toIntegerCube.size : ℤ) ≤ y i ∧
    y i < Q.toIntegerCube.corner i - (k : ℤ) * (Q.toIntegerCube.size : ℤ) +
      (((2 * k + 1) * Q.toIntegerCube.size : ℕ) : ℤ)
  push_cast
  constructor <;> linarith

/-- The region of a vertex lies in the `3s`-neighbourhood of its partition cube. -/
theorem partitionRegion_subset_thicken (hP : PartitionEvent ω) (U : TriadicCube d)
    (x : Vertex d) : partitionRegion ω U x ⊆ ((partitionCube ω x).thicken 3).vertices := by
  intro y hy
  have hy' := (Finset.mem_filter.1 hy).2
  have h1 : y ∈ cubeAt x (3 ^ ((partitionCube ω x).scale + 1)) := by
    rcases hy' with h | h
    · exact parent_union_cubeAt_subset hP x (Or.inl h)
    · have hle : 3 ^ (partitionCube ω x).scale - 1 ≤ 3 ^ ((partitionCube ω x).scale + 1) :=
        (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
      simp only [cubeAt, Set.mem_setOf_eq] at h ⊢
      exact fun i => (h i).trans (by exact_mod_cast hle)
  exact Finset.mem_coe.1 ((partitionCube ω x).cubeAt_subset_thicken (mem_partitionCube hP x)
    (by rw [pow_succ]; omega) h1)

/-- The pair regions of the partition have bounded overlap with constants `1 + 3^d`, `21^d` and
`1`. -/
theorem partitionCoarseData_pairOverlap (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) :
    (partitionCoarseData hd hP U hU).PairOverlap (1 + 3 ^ d) (21 ^ d) 1 :=
  (partitionCoarseData hd hP U hU).pairOverlap_of_mem
    (fun _ _ _ hz => (Finset.mem_filter.1 (Finset.mem_inter.1 hz).1).2)
    (fun _ _ _ _ hn => by
      obtain ⟨a, ha, b, hb, hab⟩ := hn
      have h := partitionCube_scales_close hP hab
      rw [partitionCube_eq_of_mem hP ha, partitionCube_eq_of_mem hP hb] at h
      exact h.1)

/-- **Armstrong and Dario, Lemma 3.2, for the partition into good cubes, with the reach scale.**
On a cube `U` resolved by the partition, for `1 ≤ s < ∞`,
`∑_{x ∈ C_*(U)} |w(x) - [w]_𝒫(x)|^s ≤ C^s ∑_{z ∈ C_*(U)} (3^{ρ(z)})^{sd} |∇w 1_{a≠0}|^s(z)`,
with `C = (3/2) 8^d 7^d 2√d` and `ρ(z) ≥ scale(□_𝒫(z))` the reach scale. -/
theorem partition_sum_abs_sub_coarseAnchor_rpow_le (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (w : Vertex d → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ x ∈ crossingClusterVertices ω U, |w x - w (partitionAnchor ω x)| ^ s ≤
      (3 / 2 * (2 * ((3 : ℕ) : ℝ) + 2) ^ d * (2 * ((3 : ℕ) : ℝ) + 1) ^ d * (2 * √(d : ℝ))) ^ s *
        ∑ z ∈ crossingClusterVertices ω U,
          ((3 : ℝ) ^ (partitionCoarseData hd hP U hU).reachScale z) ^ (s * d) *
            gradNormIn (openGraph ω) (crossingClusterVertices ω U) w z ^ s :=
  (partitionCoarseData hd hP U hU).sum_abs_sub_coarsen_rpow_le_reach (c := 3)
    (fun x _ => Finset.inter_subset_left.trans (partitionRegion_subset_thicken hP U x))
    (by omega) w hs

/-- **Armstrong and Dario, Lemma 3.3, for the partition into good cubes.** On a cube `U` resolved
by the partition, for `1 ≤ s < ∞`,
`∑_{x ∈ U} |∇[w]_𝒫|^s(x) ≤ C^s ∑_{z ∈ C_*(U)} size(□_𝒫(z))^{sd-1} |∇w 1_{a≠0}|^s(z)`,
with `C = 2d · 21^d (1 + 3^d) 3^d 2√d`. -/
theorem partition_sum_gradNormIn_coarseAnchor_rpow_le (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (w : Vertex d → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ∑ x ∈ U.toIntegerCube.vertices, gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices
        (fun x => w (partitionAnchor ω x)) x ^ s ≤
      (2 * (d : ℝ) * ((21 ^ d : ℕ) : ℝ) * ((1 + 3 ^ d : ℕ) : ℝ) * 3 ^ (1 * d) *
        (2 * √(d : ℝ))) ^ s *
        ∑ z ∈ crossingClusterVertices ω U, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (s * d - 1) *
          gradNormIn (openGraph ω) (crossingClusterVertices ω U) w z ^ s :=
  (partitionCoarseData hd hP U hU).sum_gradNormIn_coarsen_rpow_le
    (partitionCoarseData_pairOverlap hd hP hU) (Nat.le_add_right 1 _) (Nat.one_le_pow _ _ (by norm_num))
    (by omega) w hs

end Rigidity.Percolation
