import Rigidity.Proofs.Partition.LambdaClosure
import Rigidity.Proofs.Partition.Resolved

/-!
# The cluster `C_*(U)` of a finite set

Armstrong and Dario (beginning of Section 3) define, for a finite set `U`, the cluster `C_*(U)` as
the maximal cluster contained in the closure `cl(U)` (the union of the partition cubes of the
points of `U`) which contains the crossing clusters of the partition cubes of all points of `U`.
Here `setCluster ω U` is the set of vertices joined inside `cl(U)` to the anchor of the partition
cube of some point of `U`. If `U` is lattice-connected, the anchors of the partition cubes of its
points are joined inside `cl(U)` (Corollary 2.10 along a lattice walk inside `U`), so
`setCluster ω U` is an open cluster of `cl(U)`; it contains the crossing clusters of the partition
cubes of the points of `U` and lies in the infinite open component of the anchors. For a triadic
cube containing the partition cubes of its vertices, `cl(U) = U` and `setCluster` is the crossing
cluster of `U`.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

/-- Any two points of the set are joined by a lattice walk inside the set. -/
def LatticeConnected (U : Set (Vertex d)) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∃ p : (nearestNeighborGraph d).Walk x y, ∀ w ∈ p.support, w ∈ U

/-- Triadic cubes are lattice-connected: a walk moving one coordinate at a time towards the
target stays in the cube. -/
theorem TriadicCube.latticeConnected (Q : TriadicCube d) : LatticeConnected Q.vertices := by
  suffices h : ∀ (n : ℕ) (x y : Vertex d), x ∈ Q.vertices → y ∈ Q.vertices →
      ∑ i, (x i - y i).natAbs = n →
      ∃ p : (nearestNeighborGraph d).Walk x y, ∀ w ∈ p.support, w ∈ Q.vertices from
    fun x hx y hy => h _ x y hx hy rfl
  intro n
  induction n with
  | zero =>
    intro x y hx _ h0
    have hxy : x = y := funext fun i => by
      have := (Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_univ _)
      omega
    subst hxy
    refine ⟨SimpleGraph.Walk.nil, fun w hw => ?_⟩
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
    exact hw ▸ hx
  | succ n ih =>
    intro x y hx hy hn
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra h
      simp only [not_exists, not_not] at h
      have : ∑ i, (x i - y i).natAbs = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [h i, sub_self, Int.natAbs_zero]
      omega
    have hxQ := (Q.mem_vertices_iff_coord x).1 hx
    have hyQ := (Q.mem_vertices_iff_coord y).1 hy
    -- one step towards `y` in coordinate `i`
    obtain ⟨x', hadj, hx'i, hbetween, hx'j⟩ : ∃ x' : Vertex d, (nearestNeighborGraph d).Adj x x' ∧
        (x' i - y i).natAbs + 1 = (x i - y i).natAbs ∧
        ((x i ≤ x' i ∧ x' i ≤ y i) ∨ (y i ≤ x' i ∧ x' i ≤ x i)) ∧
        ∀ j, j ≠ i → x' j = x j := by
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · refine ⟨x + LatticeProb.unit i, ⟨i, Or.inl rfl⟩, ?_, ?_, fun j hj => ?_⟩
        · simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same]
          omega
        · simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same]
          omega
        · simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_of_ne hj, add_zero]
      · refine ⟨x - LatticeProb.unit i, ⟨i, Or.inr (sub_add_cancel x _).symm⟩, ?_, ?_,
          fun j hj => ?_⟩
        · simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_same]
          omega
        · simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_same]
          omega
        · simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_of_ne hj, sub_zero]
    have hx'Q : x' ∈ Q.vertices := by
      rw [Q.mem_vertices_iff_coord]
      intro j
      by_cases hj : j = i
      · subst hj
        have := hxQ j
        have := hyQ j
        omega
      · rw [hx'j j hj]
        exact hxQ j
    have hsum : ∑ j, (x' j - y j).natAbs = n := by
      have hsplit : ∀ j, (x j - y j).natAbs =
          (x' j - y j).natAbs + (if j = i then 1 else 0) := by
        intro j
        by_cases hj : j = i
        · subst hj
          rw [if_pos rfl]
          omega
        · rw [if_neg hj, add_zero, hx'j j hj]
      have h := Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hsplit j
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _)]
        at h
      omega
    obtain ⟨p, hp⟩ := ih x' y hx'Q hy hsum
    refine ⟨SimpleGraph.Walk.cons hadj p, fun w hw => ?_⟩
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hx
    · exact hp w hw

/-- The cluster `C_*(U)` of a finite set: the vertices joined inside the closure `cl(U)` to the
anchor of the partition cube of a point of `U`. -/
def setCluster (ω : Configuration d) (U : Finset (Vertex d)) : Set (Vertex d) :=
  {y | ∃ z ∈ U, (openIn ω ↑(partitionClosure ω U)).Reachable (partitionAnchor ω z) y}

/-- The partition cube of a point of `U` lies in `cl(U)`. -/
theorem partitionCube_subset_partitionClosure {U : Finset (Vertex d)} {z : Vertex d}
    (hz : z ∈ U) : (partitionCube ω z).vertices ⊆ ↑(partitionClosure ω U) := fun _ hx =>
  Finset.mem_coe.2 (mem_partitionClosure.2 ⟨z, hz, hx⟩)

/-- **Anchors inside a lattice-connected set** are joined inside its closure. -/
theorem reachable_partitionAnchor_of_latticeConnected (hd : 0 < d) (hP : PartitionEvent ω)
    {U : Finset (Vertex d)} (hU : LatticeConnected (↑U : Set (Vertex d))) {z z' : Vertex d}
    (hz : z ∈ U) (hz' : z' ∈ U) :
    (openIn ω ↑(partitionClosure ω U)).Reachable (partitionAnchor ω z) (partitionAnchor ω z') := by
  obtain ⟨p, hp⟩ := hU z hz z' hz'
  refine reachable_openIn_mono ?_ (reachable_partitionAnchor_of_walk hd hP p)
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨w, hw, hxw⟩ := hx
  exact partitionCube_subset_partitionClosure (Finset.mem_coe.1 (hp w hw)) hxw

/-- `C_*(U)` lies in `cl(U)`. -/
theorem setCluster_subset (ω : Configuration d) (U : Finset (Vertex d)) :
    setCluster ω U ⊆ ↑(partitionClosure ω U) ∪ {y | ∃ z ∈ U, y = partitionAnchor ω z} := by
  rintro y ⟨z, hz, hy⟩
  by_cases h : y = partitionAnchor ω z
  · exact Or.inr ⟨z, hz, h⟩
  · obtain ⟨w⟩ := hy
    cases w with
    | nil => exact absurd rfl h
    | cons hadj w' =>
      exact Or.inl (mem_of_reachable_openIn_of_mem hadj.2.2 ⟨w'⟩)

/-- **`C_*(U)` contains the crossing clusters** of the partition cubes of the points of `U`. -/
theorem crossingCluster_partitionCube_subset_setCluster (hd : 0 < d) (hP : PartitionEvent ω)
    {U : Finset (Vertex d)} {z : Vertex d} (hz : z ∈ U) :
    (partitionCube ω z).crossingCluster ω ⊆ setCluster ω U := by
  intro v hv
  have hQ := (partitionCube_mem_goodCubes hP z).2.1
  obtain ⟨root, hroot⟩ := ((partitionCube ω z).wellConnectedIn_threeQuarter_iff ω).1 hQ.2
  exact ⟨z, hz, reachable_openIn_mono (partitionCube_subset_partitionClosure hz)
    (hroot.reachable_of_mem_crossingCluster hd hQ.1 (partitionAnchor_mem_crossingCluster hP z) hv)⟩

/-- **`C_*(U)` is a cluster** of `cl(U)` when `U` is lattice-connected: any two of its points are
joined inside `cl(U)`. -/
theorem reachable_of_mem_setCluster (hd : 0 < d) (hP : PartitionEvent ω)
    {U : Finset (Vertex d)} (hU : LatticeConnected (↑U : Set (Vertex d))) {y y' : Vertex d}
    (hy : y ∈ setCluster ω U) (hy' : y' ∈ setCluster ω U) :
    (openIn ω ↑(partitionClosure ω U)).Reachable y y' := by
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨z', hz', hzy'⟩ := hy'
  exact (hzy.symm.trans (reachable_partitionAnchor_of_latticeConnected hd hP hU hz hz')).trans
    hzy'

/-- `C_*(U)` is closed under open edges of `cl(U)`: it is the maximal cluster of `cl(U)`
containing the crossing clusters of the partition cubes of the points of `U`. -/
theorem mem_setCluster_of_adj {U : Finset (Vertex d)} {y w : Vertex d}
    (hy : y ∈ setCluster ω U) (hyw : (openIn ω ↑(partitionClosure ω U)).Adj y w) :
    w ∈ setCluster ω U := by
  obtain ⟨z, hz, hzy⟩ := hy
  exact ⟨z, hz, hzy.trans hyw.reachable⟩

/-- `C_*(U)` lies in the infinite open component of the anchors. -/
theorem infinite_supp_of_mem_setCluster (hd : 0 < d) (hP : PartitionEvent ω)
    {U : Finset (Vertex d)} {y : Vertex d} (hy : y ∈ setCluster ω U) :
    ((openGraph ω).connectedComponentMk y).supp.Infinite := by
  obtain ⟨z, -, hzy⟩ := hy
  have hr : (openGraph ω).Reachable (partitionAnchor ω z) y := by
    refine hzy.mono ?_
    intro u v h
    exact h.1
  rw [show (openGraph ω).connectedComponentMk y =
      (openGraph ω).connectedComponentMk (partitionAnchor ω z) from
    (SimpleGraph.ConnectedComponent.eq.2 hr).symm]
  exact infinite_supp_partitionAnchor hd hP z

/-- For a triadic cube containing the partition cubes of its vertices, `cl(U) = U`. -/
theorem partitionClosure_eq_of_resolved (hP : PartitionEvent ω) {U : TriadicCube d}
    (hres : ∀ z ∈ U.vertices, (partitionCube ω z).scale ≤ U.scale) :
    (↑(partitionClosure ω U.toIntegerCube.vertices) : Set (Vertex d)) = U.vertices := by
  ext x
  rw [Finset.mem_coe, mem_partitionClosure]
  constructor
  · rintro ⟨z, hz, hxz⟩
    have hzU := (U.mem_toIntegerCube_vertices z).1 hz
    exact TriadicCube.vertices_subset_of_mem_of_scale_le (mem_partitionCube hP z) hzU
      (hres z hzU) hxz
  · intro hx
    exact ⟨x, (U.mem_toIntegerCube_vertices x).2 hx, mem_partitionCube hP x⟩

/-- **For a resolved triadic cube, `C_*(U)` is the crossing cluster of `U`**: the two definitions
of Armstrong and Dario agree. -/
theorem setCluster_eq_crossingCluster (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hres : ∀ z ∈ U.vertices, (partitionCube ω z).scale ≤ U.scale) :
    setCluster ω U.toIntegerCube.vertices = U.crossingCluster ω := by
  have hcl := partitionClosure_eq_of_resolved hP hres
  ext y
  constructor
  · rintro ⟨z, hz, hzy⟩
    rw [hcl] at hzy
    have hzU := (U.mem_toIntegerCube_vertices z).1 hz
    have ha := crossingCluster_partitionCube_subset hd hP hzU (hres z hzU)
      (partitionAnchor_mem_crossingCluster hP z)
    obtain ⟨r, hr, hra⟩ := ha
    exact ⟨r, hr, hra.trans hzy⟩
  · intro hy
    obtain ⟨z, hz⟩ : ∃ z, z ∈ U.vertices := ⟨U.center, U.center_mem⟩
    have hU := mem_goodCubes_of_partitionCube_le hP hz (hres z hz)
    obtain ⟨rU, hrU⟩ := (U.wellConnectedIn_threeQuarter_iff ω).1 hU.2.1.2
    have ha := crossingCluster_partitionCube_subset hd hP hz (hres z hz)
      (partitionAnchor_mem_crossingCluster hP z)
    refine ⟨z, (U.mem_toIntegerCube_vertices z).2 hz, ?_⟩
    rw [hcl]
    exact hrU.reachable_of_mem_crossingCluster hd hU.2.1.1 ha hy

end Rigidity.Percolation
