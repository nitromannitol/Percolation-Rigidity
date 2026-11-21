import Rigidity.Proofs.Partition.Adjacent
import Rigidity.Percolation.TriadicStoppingNeighbors

/-!
# The partition into good cubes in every dimension

On the event that every vertex lies in a unique maximal stopping cube of the good cubes, the
partition `𝒫` of Armstrong and Dario (Proposition 2.1 and Definition 2.9) is given by
`partitionCube ω x`, the cube of the partition containing `x`. Partition cubes are good, and so
is every triadic cube containing a partition cube (property (i) of Proposition 2.1); partition
cubes containing neighbouring vertices differ by at most one scale (property (ii)).

The anchor `z̄(Q)` of a cube is a point of its crossing cluster, chosen when the crossing cluster
is nonempty. Armstrong and Dario fix the point closest to the centre; any point of the crossing
cluster serves in what follows.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External
open scoped Classical

variable {d : ℕ}

/-- Every vertex lies in a unique maximal stopping cube of the good cubes. -/
def PartitionEvent (ω : Configuration d) : Prop :=
  ∀ x : Vertex d, ∃! Q : TriadicCube d,
    x ∈ Q.vertices ∧ Q.IsMaximalStopping (TriadicCube.goodCubes ω)

/-- The cube of the partition containing a vertex. -/
noncomputable def partitionCube (ω : Configuration d) (x : Vertex d) : TriadicCube d :=
  if h : ∃ Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (TriadicCube.goodCubes ω) then
    Classical.choose h
  else ⟨0, x⟩

variable {ω : Configuration d}

theorem partitionCube_spec (hP : PartitionEvent ω) (x : Vertex d) :
    x ∈ (partitionCube ω x).vertices ∧
      (partitionCube ω x).IsMaximalStopping (TriadicCube.goodCubes ω) := by
  have h : ∃ Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (TriadicCube.goodCubes ω) :=
    (hP x).exists
  unfold partitionCube
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- A vertex lies in its partition cube. -/
theorem mem_partitionCube (hP : PartitionEvent ω) (x : Vertex d) :
    x ∈ (partitionCube ω x).vertices :=
  (partitionCube_spec hP x).1

/-- The partition cube is the unique maximal stopping cube containing the vertex. -/
theorem partitionCube_eq (hP : PartitionEvent ω) {x : Vertex d} {Q : TriadicCube d}
    (hx : x ∈ Q.vertices) (hQ : Q.IsMaximalStopping (TriadicCube.goodCubes ω)) :
    partitionCube ω x = Q :=
  (hP x).unique (partitionCube_spec hP x) ⟨hx, hQ⟩

/-- The partition cube map is constant on partition cubes. -/
theorem partitionCube_eq_of_mem (hP : PartitionEvent ω) {x y : Vertex d}
    (hy : y ∈ (partitionCube ω x).vertices) : partitionCube ω y = partitionCube ω x :=
  partitionCube_eq hP hy (partitionCube_spec hP x).2

/-- Two vertices have the same partition cube or disjoint partition cubes. -/
theorem partitionCube_eq_or_disjoint (hP : PartitionEvent ω) (x y : Vertex d) :
    partitionCube ω x = partitionCube ω y ∨
      Disjoint (partitionCube ω x).vertices (partitionCube ω y).vertices := by
  by_cases h : ∃ z, z ∈ (partitionCube ω x).vertices ∧ z ∈ (partitionCube ω y).vertices
  · obtain ⟨z, hzx, hzy⟩ := h
    exact Or.inl ((partitionCube_eq_of_mem hP hzx).symm.trans (partitionCube_eq_of_mem hP hzy))
  · simp only [not_exists, not_and] at h
    exact Or.inr (Set.disjoint_left.2 h)

/-- Partition cubes are stable good cubes. -/
theorem partitionCube_mem_stableGood (hP : PartitionEvent ω) (x : Vertex d) :
    partitionCube ω x ∈ TriadicCube.stableGood (TriadicCube.goodCubes ω) :=
  (partitionCube_spec hP x).2.1.1

/-- **Armstrong and Dario, Proposition 2.1 (i).** Every ancestor of a partition cube is good. -/
theorem ancestor_partitionCube_mem_goodCubes (hP : PartitionEvent ω) (x : Vertex d) (n : ℕ) :
    (partitionCube ω x).ancestor n ∈ TriadicCube.goodCubes ω :=
  TriadicCube.stableGood_subset _
    (TriadicCube.ancestor_mem_stableGood (partitionCube_mem_stableGood hP x) n)

/-- Every triadic cube containing a partition cube is good. -/
theorem mem_goodCubes_of_partitionCube_le (hP : PartitionEvent ω) {x : Vertex d}
    {U : TriadicCube d} (hxU : x ∈ U.vertices) (hscale : (partitionCube ω x).scale ≤ U.scale) :
    U ∈ TriadicCube.goodCubes ω := by
  rw [TriadicCube.eq_ancestor_of_mem (mem_partitionCube hP x) hxU hscale]
  exact ancestor_partitionCube_mem_goodCubes hP x _

/-- Partition cubes are good. -/
theorem partitionCube_mem_goodCubes (hP : PartitionEvent ω) (x : Vertex d) :
    partitionCube ω x ∈ TriadicCube.goodCubes ω :=
  TriadicCube.stableGood_subset _ (partitionCube_mem_stableGood hP x)

/-- The parent of a partition cube is good. -/
theorem parent_partitionCube_mem_goodCubes (hP : PartitionEvent ω) (x : Vertex d) :
    (partitionCube ω x).parent ∈ TriadicCube.goodCubes ω :=
  ancestor_partitionCube_mem_goodCubes hP x 1

/-- Partition cubes have scale at least three. -/
theorem three_le_scale_partitionCube (hP : PartitionEvent ω) (x : Vertex d) :
    3 ≤ (partitionCube ω x).scale :=
  TriadicCube.three_le_scale_of_mem_goodCubes (partitionCube_mem_goodCubes hP x)

/-- **Armstrong and Dario, Proposition 2.1 (ii).** Partition cubes of vertices at `ℓ∞` distance at
most one differ by at most one scale. -/
theorem partitionCube_scales_close (hP : PartitionEvent ω) {x y : Vertex d}
    (hnear : ∀ i, |x i - y i| ≤ 1) :
    (partitionCube ω x).scale ≤ (partitionCube ω y).scale + 1 ∧
      (partitionCube ω y).scale ≤ (partitionCube ω x).scale + 1 :=
  (partitionCube_spec hP x).2.1.scales_close_of_near (partitionCube_spec hP y).2.1
    (partitionCube_spec hP x).1 (partitionCube_spec hP y).1 hnear

/-- Lattice neighbours are at `ℓ∞` distance at most one. -/
theorem abs_sub_le_one_of_nearestNeighbor_adj {x y : Vertex d}
    (h : (nearestNeighborGraph d).Adj x y) (i : Fin d) : |x i - y i| ≤ 1 := by
  obtain ⟨j, hj | hj⟩ := h <;> subst hj <;>
    by_cases hij : i = j <;> simp [LatticeProb.unit, hij]

/-- The anchor of a cube: a point of its crossing cluster, when the crossing cluster is
nonempty. -/
noncomputable def TriadicCube.anchor (ω : Configuration d) (Q : TriadicCube d) : Vertex d :=
  if h : (Q.crossingCluster ω).Nonempty then h.some else Q.center

/-- The anchor of a well-connected cube lies in its crossing cluster. -/
theorem TriadicCube.anchor_mem_crossingCluster {Q : TriadicCube d}
    (hQ : Q ∈ wellConnectedCubes ω) : Q.anchor ω ∈ Q.crossingCluster ω := by
  obtain ⟨root, hroot⟩ := (Q.wellConnectedIn_threeQuarter_iff ω).1 hQ.2
  have h : (Q.crossingCluster ω).Nonempty := ⟨root, hroot.mem_crossingCluster⟩
  unfold TriadicCube.anchor
  rw [dif_pos h]
  exact h.some_mem

/-- The anchor `z̄(𝒫(x))` of the partition cube of a vertex. -/
noncomputable def partitionAnchor (ω : Configuration d) (x : Vertex d) : Vertex d :=
  (partitionCube ω x).anchor ω

/-- The anchor of a partition cube lies in its crossing cluster. -/
theorem partitionAnchor_mem_crossingCluster (hP : PartitionEvent ω) (x : Vertex d) :
    partitionAnchor ω x ∈ (partitionCube ω x).crossingCluster ω :=
  TriadicCube.anchor_mem_crossingCluster (partitionCube_mem_goodCubes hP x).2.1

/-- The anchor of a partition cube lies in the cube. -/
theorem partitionAnchor_mem (hP : PartitionEvent ω) (x : Vertex d) :
    partitionAnchor ω x ∈ (partitionCube ω x).vertices :=
  TriadicCube.crossingCluster_subset _ _ (partitionAnchor_mem_crossingCluster hP x)

/-- The anchor map is constant on partition cubes. -/
theorem partitionAnchor_eq_of_mem (hP : PartitionEvent ω) {x y : Vertex d}
    (hy : y ∈ (partitionCube ω x).vertices) : partitionAnchor ω y = partitionAnchor ω x := by
  unfold partitionAnchor
  rw [partitionCube_eq_of_mem hP hy]

end Rigidity.Percolation
