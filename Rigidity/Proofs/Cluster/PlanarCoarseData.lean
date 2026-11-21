import Rigidity.Proofs.Cluster.CoarseData
import Rigidity.Proofs.Percolation.PlanarCubeEnergy

/-!
# Coarse-graining data of a resolved planar cube

For a configuration of the planar partition event and a triadic cube `U` resolved by the planar
partition, the domain `U`, its cluster `C_*(U)`, the planar partition cubes with their anchors, and
the windows of the partition cubes restricted to `C_*(U)` form coarse-graining data. The region of
a vertex is the window of its partition cube; the region of two lattice neighbours is the pair
window of their partition cubes, taken from the one of smaller scale. Both lie in `U` and in the
square of side `9s` around the smaller partition cube.

The windows replace the local paths of Armstrong and Dario (Lemmas 3.2 and 3.3). They may meet
partition cubes much smaller than the cube they come from, so only the inequalities with exact
weights apply to these data.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

theorem joinedWithin_iff_reachIn {S : Set (Vertex 2)} {x y : Vertex 2} :
    JoinedWithin ω S x y ↔ ReachIn ω S x y :=
  Iff.rfl

theorem edgeVariationIn_eq_sum_vertexVariation {d : ℕ} (ω : Configuration d)
    (S : Finset (Vertex d)) (w : Vertex d → ℝ) :
    edgeVariationIn ω S w = ∑ x ∈ S, vertexVariation ω S w x :=
  rfl

private theorem planar_abs_sub_le_one_of_adj {d : ℕ} {u v : Vertex d}
    (h : (nearestNeighborGraph d).Adj u v) (k : Fin d) : |u k - v k| ≤ 1 := by
  obtain ⟨l, hl | hl⟩ := h <;> subst hl <;> by_cases hkl : k = l <;> simp [LatticeProb.unit, hkl]

/-- The pair region of two lattice neighbours: the pair window of their partition cubes, taken
from the one of smaller scale, restricted to the cluster of `U`. -/
noncomputable def planarClusterPairRegion (ω : Configuration 2) (U : TriadicCube 2)
    (x y : Vertex 2) : Finset (Vertex 2) :=
  if (planarPartCube ω x).scale ≤ (planarPartCube ω y).scale then planarClusterPairWindow ω U x y
  else planarClusterPairWindow ω U y x

theorem planarClusterWindow_subset (U : TriadicCube 2) (x : Vertex 2) :
    planarClusterWindow ω U x ⊆ clusterVertices ω U := fun _ hy =>
  mem_clusterVertices.2 (Finset.mem_filter.1 hy).2

theorem planarClusterPairRegion_subset (U : TriadicCube 2) (x y : Vertex 2) :
    planarClusterPairRegion ω U x y ⊆ clusterVertices ω U := by
  intro z hz
  unfold planarClusterPairRegion at hz
  split_ifs at hz <;> exact mem_clusterVertices.2 (Finset.mem_filter.1 hz).2

/-- A vertex of the cluster of a resolved cube is joined to the anchor of its partition cube by
an open path inside the window of the partition cube and the cluster. -/
theorem joinedWithin_planarClusterWindow (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {x : Vertex 2} (hx : x ∈ planarCubeCluster ω U) :
    JoinedWithin ω ↑(planarClusterWindow ω U x) x (planarCoarseAnchor ω x) := by
  set Q := planarPartCube ω x
  have hsub := planarPartCube_subset_of_resolved hP hU hx.1
  have h := Q.reachIn_window_of_reachIn (planarPartCube_meshed hP x).1
    (planarPartCube_large hP x) (hU x hx.1) hsub (planarPartCube_spec hP x).1 hx.2
  have hA : Q.planarAnchor ω ∈ planarCubeCluster ω U :=
    planarAnchor_mem_planarCubeCluster hP hU hx.1
  have h' := reachIn_planarCubeCluster hP hU (Q.window_subset hsub) hA h
  have hcoe : (↑(planarClusterWindow ω U x) : Set (Vertex 2)) =
      ↑(Q.window U).vertices ∩ planarCubeCluster ω U := by
    ext y
    simp only [planarClusterWindow, Finset.coe_filter, Set.mem_setOf_eq, Set.mem_inter_iff,
      Finset.mem_coe, Q]
  rw [hcoe]
  exact h'.symm

/-- The anchors of the partition cubes of two adjacent vertices of a resolved cube, the first of
the same or smaller scale, are joined by an open path inside their pair window and the cluster. -/
theorem joinedWithin_planarClusterPairWindow (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {x y : Vertex 2} (hx : x ∈ U.vertices) (hy : y ∈ U.vertices)
    (hnear : ∀ i, |x i - y i| ≤ 1)
    (hscale : (planarPartCube ω x).scale ≤ (planarPartCube ω y).scale) :
    JoinedWithin ω ↑(planarClusterPairWindow ω U x y) (planarCoarseAnchor ω x)
      (planarCoarseAnchor ω y) := by
  set Q := planarPartCube ω x
  set Q' := planarPartCube ω y
  have hsub := planarPartCube_subset_of_resolved hP hU hx
  have hsub' := planarPartCube_subset_of_resolved hP hU hy
  have hsc2 := (planarPartCube_scales_close hP hnear).2
  have h := TriadicCube.reachIn_planarAnchor_pairWindow (planarPartCube_meshed hP x).1
    (planarPartCube_meshed hP y).1 (planarPartCube_large hP x) (hU x hx) hsub hsub' hscale hsc2
    (planarPartCube_spec hP x).1 (planarPartCube_spec hP y).1 hnear
  have hspec := TriadicCube.pairWindow_spec (hU x hx) hsub hsub' hscale hsc2
    (planarPartCube_spec hP x).1 (planarPartCube_spec hP y).1 hnear
  have hA : Q.planarAnchor ω ∈ planarCubeCluster ω U :=
    planarAnchor_mem_planarCubeCluster hP hU hx
  have h' := reachIn_planarCubeCluster hP hU hspec.2.2.2 hA h
  have hcoe : (↑(planarClusterPairWindow ω U x y) : Set (Vertex 2)) =
      ↑(Q.pairWindow Q' U).vertices ∩ planarCubeCluster ω U := by
    ext z
    simp only [planarClusterPairWindow, Finset.coe_filter, Set.mem_setOf_eq, Set.mem_inter_iff,
      Finset.mem_coe, Q, Q']
  rw [hcoe]
  exact h'

/-- **Coarse-graining data of a resolved planar cube**: domain `U`, cluster `C_*(U)`, the planar
partition cubes and their anchors, the windows of the partition cubes and the pair windows of
adjacent partition cubes, restricted to `C_*(U)`. -/
noncomputable def planarCoarseData (hP : PlanarPartitionEvent ω) (U : TriadicCube 2)
    (hU : PlanarResolved ω U) : CoarseData 2 ω where
  domain := U.toIntegerCube.vertices
  cluster := clusterVertices ω U
  cluster_subset := Finset.filter_subset _ _
  part := planarPartCube ω
  mem_part x _ := (planarPartCube_spec hP x).1
  part_subset x hx y hy := by
    rw [TriadicCube.mem_toIntegerCube_vertices] at hx
    rw [Finset.mem_coe, TriadicCube.mem_toIntegerCube_vertices]
    exact planarPartCube_subset_of_resolved hP hU hx hy
  part_eq_of_mem _ _ _ hy := planarPartCube_eq_of_mem hP hy
  anchor := planarCoarseAnchor ω
  anchor_congr x y h := by
    change (planarPartCube ω x).planarAnchor ω = (planarPartCube ω y).planarAnchor ω
    rw [h]
  anchor_mem x hx := by
    rw [TriadicCube.mem_toIntegerCube_vertices] at hx
    exact mem_clusterVertices.2 (planarAnchor_mem_planarCubeCluster hP hU hx)
  anchor_mem_part x _ := ((planarPartCube ω x).planarAnchor_spec (planarPartCube_meshed hP x).1
    (planarPartCube_large hP x)).1
  region := planarClusterWindow ω U
  joinedWithin_region x hx :=
    (joinedWithin_planarClusterWindow hP hU (mem_clusterVertices.1 hx)).mono
      (Finset.coe_subset.2 (Finset.subset_inter (Finset.Subset.refl _) (planarClusterWindow_subset U x)))
  pairRegion := planarClusterPairRegion ω U
  joinedWithin_pairRegion x hx y hy hadj _ := by
    rw [TriadicCube.mem_toIntegerCube_vertices] at hx hy
    have hnear : ∀ i, |x i - y i| ≤ 1 := planar_abs_sub_le_one_of_adj hadj
    refine JoinedWithin.mono ?_
      (Finset.coe_subset.2 (Finset.subset_inter (Finset.Subset.refl _) (planarClusterPairRegion_subset U x y)))
    unfold planarClusterPairRegion
    split_ifs with h
    · exact joinedWithin_planarClusterPairWindow hP hU hx hy hnear h
    · exact (joinedWithin_planarClusterPairWindow hP hU hy hx
        (fun i => by rw [abs_sub_comm]; exact hnear i) (by omega)).symm

@[simp] theorem planarCoarseData_cluster (hP : PlanarPartitionEvent ω) (U : TriadicCube 2)
    (hU : PlanarResolved ω U) : (planarCoarseData hP U hU).cluster = clusterVertices ω U :=
  rfl

@[simp] theorem planarCoarseData_part (hP : PlanarPartitionEvent ω) (U : TriadicCube 2)
    (hU : PlanarResolved ω U) : (planarCoarseData hP U hU).part = planarPartCube ω :=
  rfl

@[simp] theorem planarCoarseData_anchor (hP : PlanarPartitionEvent ω) (U : TriadicCube 2)
    (hU : PlanarResolved ω U) : (planarCoarseData hP U hU).anchor = planarCoarseAnchor ω :=
  rfl

end Rigidity.Percolation
