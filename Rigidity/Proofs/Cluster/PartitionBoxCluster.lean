import Rigidity.Proofs.Cluster.PartitionBoxPaths
import Rigidity.Proofs.Cluster.PartitionCoarseData

/-!
# The cluster of an integer cube resolved by the partition into good cubes

An integer cube `B` (not necessarily triadic) is resolved by the partition into good cubes when it
contains the parents of the partition cubes of its vertices. Lattice walks inside `B` join any
two of its vertices, so the anchors of the partition cubes of its vertices are joined by open
paths inside `B` (Armstrong and Dario, Corollary 2.10). The cluster `C(B)` is the set of vertices of
`B` joined inside `B` to the anchor of their partition cube. With the regions
`B ∩ (Q.parent ∪ (x + Q_{s - 1}))` of the local paths (`reachable_partitionAnchor_of_reachable_box`)
and the unions of the partition cubes of lattice neighbours, the domain `B`, the cluster `C(B)`,
the partition cubes and their anchors form coarse-graining data, in every dimension.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External
open scoped Classical

variable {d : ℕ} {ω : Configuration d}

/-- **Lattice walks inside an integer cube.** Any two vertices of an integer cube are joined by a
lattice walk inside the cube. -/
theorem IntegerCube.exists_walk (B : IntegerCube d) :
    ∀ (n : ℕ) {x y : Vertex d}, x ∈ B.vertices → y ∈ B.vertices →
      ∑ i, (x i - y i).natAbs ≤ n →
        ∃ p : (nearestNeighborGraph d).Walk x y, ∀ z ∈ p.support, z ∈ B.vertices := by
  intro n
  induction n with
  | zero =>
    intro x y hx _ h0
    have hxy : x = y := funext fun i => by
      have := Finset.sum_eq_zero_iff.1 (Nat.le_zero.1 h0) i (Finset.mem_univ i)
      omega
    subst hxy
    exact ⟨SimpleGraph.Walk.nil, fun z hz => by
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      exact hz ▸ hx⟩
  | succ n ih =>
    intro x y hx hy hn
    by_cases hxy : x = y
    · subst hxy
      exact ⟨SimpleGraph.Walk.nil, fun z hz => by
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
        exact hz ▸ hx⟩
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    set s : ℤ := if x i < y i then 1 else -1 with hs
    set x' : Vertex d := Function.update x i (x i + s) with hx'
    have hx'i : x' i = x i + s := by rw [hx', Function.update_self]
    have hx'j : ∀ j, j ≠ i → x' j = x j := fun j hj => by rw [hx', Function.update_of_ne hj]
    have hadj : (nearestNeighborGraph d).Adj x x' := by
      refine ⟨i, ?_⟩
      by_cases hlt : x i < y i
      · left
        funext j
        simp only [Pi.add_apply, LatticeProb.unit, Pi.single_apply]
        by_cases hj : j = i
        · subst hj
          rw [hx'i, hs, if_pos hlt]
          simp
        · rw [hx'j j hj, if_neg hj, add_zero]
      · right
        funext j
        simp only [Pi.add_apply, LatticeProb.unit, Pi.single_apply]
        by_cases hj : j = i
        · subst hj
          rw [hx'i, hs, if_neg hlt]
          simp
        · rw [hx'j j hj, if_neg hj, add_zero]
    have hxB := (IntegerCube.mem_vertices B x).1 hx
    have hyB := (IntegerCube.mem_vertices B y).1 hy
    have hx'B : x' ∈ B.vertices := by
      rw [IntegerCube.mem_vertices]
      intro j
      by_cases hj : j = i
      · subst hj
        rw [hx'i, hs]
        have := hxB j
        have := hyB j
        split_ifs with hlt <;> omega
      · rw [hx'j j hj]
        exact hxB j
    have hdist : ∑ j, (x' j - y j).natAbs ≤ n := by
      have hsplit : ∀ z : Vertex d, ∑ j, (z j - y j).natAbs =
          (z i - y i).natAbs + ∑ j ∈ Finset.univ.erase i, (z j - y j).natAbs := fun z =>
        (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
      have heq : ∑ j ∈ Finset.univ.erase i, (x' j - y j).natAbs =
          ∑ j ∈ Finset.univ.erase i, (x j - y j).natAbs :=
        Finset.sum_congr rfl fun j hj => by rw [hx'j j (Finset.ne_of_mem_erase hj)]
      rw [hsplit x'] at ⊢
      rw [hsplit x] at hn
      rw [heq]
      have : (x' i - y i).natAbs + 1 = (x i - y i).natAbs := by
        rw [hx'i, hs]
        split_ifs with hlt <;> omega
      omega
    obtain ⟨p, hp⟩ := ih hx'B hy hdist
    refine ⟨SimpleGraph.Walk.cons hadj p, fun z hz => ?_⟩
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · exact hp z hz

/-- An integer cube is resolved by the partition into good cubes when it contains the parents of
the partition cubes of its vertices. -/
def PartitionBoxResolved (ω : Configuration d) (B : IntegerCube d) : Prop :=
  ∀ z ∈ B.vertices, (partitionCube ω z).parent.vertices ⊆ ↑B.vertices

theorem PartitionBoxResolved.partitionCube_subset {B : IntegerCube d}
    (hB : PartitionBoxResolved ω B) {z : Vertex d} (hz : z ∈ B.vertices) :
    (partitionCube ω z).vertices ⊆ ↑B.vertices :=
  fun _ hy => hB z hz ((partitionCube ω z).vertices_subset_parent hy)

/-- **Anchors inside a resolved integer cube.** The anchors of the partition cubes of two vertices
of a resolved integer cube are joined by an open path inside the cube. -/
theorem reachable_partitionAnchor_of_boxResolved (hd : 0 < d) (hP : PartitionEvent ω)
    {B : IntegerCube d} (hB : PartitionBoxResolved ω B) {z z' : Vertex d}
    (hz : z ∈ B.vertices) (hz' : z' ∈ B.vertices) :
    (openIn ω ↑B.vertices).Reachable (partitionAnchor ω z) (partitionAnchor ω z') := by
  obtain ⟨p, hp⟩ := B.exists_walk _ hz hz' le_rfl
  refine reachable_openIn_mono ?_ (reachable_partitionAnchor_of_walk hd hP p)
  intro w hw
  simp only [Set.mem_iUnion] at hw
  obtain ⟨v, hv, hw⟩ := hw
  exact hB.partitionCube_subset (hp v hv) hw

/-- The cluster `C(B)` of an integer cube: the vertices of `B` joined inside `B` to the anchor of
their partition cube. -/
noncomputable def partitionBoxCluster (ω : Configuration d) (B : IntegerCube d) :
    Finset (Vertex d) :=
  B.vertices.filter fun x => (openIn ω ↑B.vertices).Reachable x (partitionAnchor ω x)

theorem mem_partitionBoxCluster {B : IntegerCube d} {x : Vertex d} :
    x ∈ partitionBoxCluster ω B ↔
      x ∈ B.vertices ∧ (openIn ω ↑B.vertices).Reachable x (partitionAnchor ω x) := by
  unfold partitionBoxCluster
  rw [Finset.mem_filter]

/-- A vertex of a resolved integer cube joined inside it to some anchor belongs to its cluster. -/
theorem mem_partitionBoxCluster_of_reachable (hd : 0 < d) (hP : PartitionEvent ω)
    {B : IntegerCube d} (hB : PartitionBoxResolved ω B) {y z : Vertex d}
    (hy : y ∈ B.vertices) (hz : z ∈ B.vertices)
    (h : (openIn ω ↑B.vertices).Reachable y (partitionAnchor ω z)) :
    y ∈ partitionBoxCluster ω B :=
  mem_partitionBoxCluster.2 ⟨hy, h.trans (reachable_partitionAnchor_of_boxResolved hd hP hB hz hy)⟩

/-- Open paths inside `B` from a vertex of the cluster stay in the cluster. -/
theorem reachable_partitionBoxCluster (hd : 0 < d) (hP : PartitionEvent ω)
    {B : IntegerCube d} (hB : PartitionBoxResolved ω B) {S : Set (Vertex d)}
    (hSB : S ⊆ ↑B.vertices) {a b : Vertex d} (ha : a ∈ partitionBoxCluster ω B)
    (h : (openIn ω S).Reachable a b) :
    (openIn ω (S ∩ ↑(partitionBoxCluster ω B))).Reachable a b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y c hxy w ih =>
    have hx' := mem_partitionBoxCluster.1 ha
    have hyx : (openIn ω ↑B.vertices).Reachable y x :=
      SimpleGraph.Adj.reachable ⟨hxy.1.symm, hSB hxy.2.2, hSB hxy.2.1⟩
    have hy : y ∈ partitionBoxCluster ω B :=
      mem_partitionBoxCluster_of_reachable hd hP hB (hSB hxy.2.2) hx'.1 (hyx.trans hx'.2)
    exact (SimpleGraph.Adj.reachable (G := openIn ω (S ∩ ↑(partitionBoxCluster ω B)))
      ⟨hxy.1, ⟨hxy.2.1, ha⟩, ⟨hxy.2.2, hy⟩⟩).trans (ih hy)

/-- The anchors of the partition cubes of the vertices of a resolved integer cube belong to its
cluster. -/
theorem partitionAnchor_mem_partitionBoxCluster (hd : 0 < d) (hP : PartitionEvent ω)
    {B : IntegerCube d} (hB : PartitionBoxResolved ω B) {x : Vertex d} (hx : x ∈ B.vertices) :
    partitionAnchor ω x ∈ partitionBoxCluster ω B :=
  mem_partitionBoxCluster_of_reachable hd hP hB
    (hB.partitionCube_subset hx (partitionAnchor_mem hP x)) hx (SimpleGraph.Reachable.refl _)

/-- The cluster of a resolved integer cube contains every vertex of the cube joined to it by an
open edge. -/
theorem mem_partitionBoxCluster_of_adj (hd : 0 < d) (hP : PartitionEvent ω)
    {B : IntegerCube d} (hB : PartitionBoxResolved ω B) {z w : Vertex d}
    (hz : z ∈ partitionBoxCluster ω B) (hadj : (openGraph ω).Adj z w) (hw : w ∈ B.vertices) :
    w ∈ partitionBoxCluster ω B := by
  have hz' := mem_partitionBoxCluster.1 hz
  have hwz : (openIn ω ↑B.vertices).Reachable w z :=
    SimpleGraph.Adj.reachable ⟨hadj.symm, hw, hz'.1⟩
  exact mem_partitionBoxCluster_of_reachable hd hP hB hw hz'.1 (hwz.trans hz'.2)

/-- The region of the local path from a vertex to the anchor of its partition cube, inside `B`. -/
noncomputable def partitionBoxRegion (ω : Configuration d) (B : IntegerCube d) (x : Vertex d) :
    Finset (Vertex d) :=
  B.vertices.filter fun y =>
    y ∈ (partitionCube ω x).parent.vertices ∪ cubeAt x (3 ^ (partitionCube ω x).scale - 1)

/-- The region of the local path between the anchors of two lattice neighbours, inside `B`. -/
noncomputable def partitionBoxPairRegion (ω : Configuration d) (B : IntegerCube d)
    (x y : Vertex d) : Finset (Vertex d) :=
  B.vertices.filter fun z => z ∈ (partitionCube ω x).vertices ∪ (partitionCube ω y).vertices

/-- **Coarse-graining data of a resolved integer cube** for the partition into good cubes, in every
dimension: domain `B`, cluster `C(B)`, the partition cubes and their anchors, and the regions
`partitionBoxRegion` and `partitionBoxPairRegion`. -/
noncomputable def partitionBoxCoarseData (hd : 0 < d) (hP : PartitionEvent ω) (B : IntegerCube d)
    (hB : PartitionBoxResolved ω B) : CoarseData d ω where
  domain := B.vertices
  cluster := partitionBoxCluster ω B
  cluster_subset := Finset.filter_subset _ _
  part := partitionCube ω
  mem_part x _ := mem_partitionCube hP x
  part_subset x hx := hB.partitionCube_subset hx
  part_eq_of_mem _ _ _ hy := partitionCube_eq_of_mem hP hy
  anchor := partitionAnchor ω
  anchor_congr x y h := by
    unfold partitionAnchor
    rw [h]
  anchor_mem x hx := partitionAnchor_mem_partitionBoxCluster hd hP hB hx
  anchor_mem_part x _ := partitionAnchor_mem hP x
  region := partitionBoxRegion ω B
  joinedWithin_region x hx := by
    have hx' := mem_partitionBoxCluster.1 hx
    have h := reachable_partitionAnchor_of_reachable_box hd hP (hB x hx'.1) hx'.2
    have h' := reachable_partitionBoxCluster hd hP hB Set.inter_subset_left hx h
    have hxS : x ∈ (↑B.vertices ∩ ((partitionCube ω x).parent.vertices ∪
        cubeAt x (3 ^ (partitionCube ω x).scale - 1))) ∩ ↑(partitionBoxCluster ω B) :=
      ⟨⟨hx'.1, Or.inr (by simp [cubeAt])⟩, hx⟩
    refine (joinedWithin_of_reachable_openIn h' hxS).mono ?_
    rintro y ⟨⟨hyB, hyR⟩, hyC⟩
    exact Finset.mem_coe.2 (Finset.mem_inter.2 ⟨Finset.mem_filter.2 ⟨hyB, hyR⟩, hyC⟩)
  pairRegion := partitionBoxPairRegion ω B
  joinedWithin_pairRegion x hx y hy hadj _ := by
    have h := reachable_partitionAnchor_of_adj hd hP hadj
    have hsub : (partitionCube ω x).vertices ∪ (partitionCube ω y).vertices ⊆
        ↑B.vertices ∩ ((partitionCube ω x).vertices ∪ (partitionCube ω y).vertices) := by
      rintro z (hz | hz)
      · exact ⟨hB.partitionCube_subset hx hz, Or.inl hz⟩
      · exact ⟨hB.partitionCube_subset hy hz, Or.inr hz⟩
    have hA := partitionAnchor_mem_partitionBoxCluster hd hP hB hx
    have h' := reachable_partitionBoxCluster hd hP hB Set.inter_subset_left hA
      (reachable_openIn_mono hsub h)
    have hAS : partitionAnchor ω x ∈ (↑B.vertices ∩ ((partitionCube ω x).vertices ∪
        (partitionCube ω y).vertices)) ∩ ↑(partitionBoxCluster ω B) :=
      ⟨⟨hB.partitionCube_subset hx (partitionAnchor_mem hP x),
        Or.inl (partitionAnchor_mem hP x)⟩, hA⟩
    refine (joinedWithin_of_reachable_openIn h' hAS).mono ?_
    rintro z ⟨⟨hzB, hzR⟩, hzC⟩
    exact Finset.mem_coe.2 (Finset.mem_inter.2 ⟨Finset.mem_filter.2 ⟨hzB, hzR⟩, hzC⟩)

end Rigidity.Percolation
