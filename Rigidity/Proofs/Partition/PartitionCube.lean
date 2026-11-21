import Rigidity.Proofs.Partition.Adjacent
import Rigidity.Percolation.TriadicStoppingNeighbors

/-!
# The partition into good cubes in every dimension

On the event that every vertex lies in a unique maximal stopping cube of the good cubes, the
partition `𝒫` of Armstrong and Dario (Proposition 2.1 and Definition 2.9) is given by
`partitionCube ω x`, the cube of the partition containing `x`. Partition cubes are good, and so
is every triadic cube containing a partition cube (property (i) of Proposition 2.1); partition
cubes containing neighbouring vertices differ by at most one scale (property (ii)).

The anchor `z̄(Q)` of a cube is, as in Armstrong and Dario (Definition 3.1), the point of its
crossing cluster closest to the centre of the cube in the `ℓ∞` norm, ties broken by the
lexicographic order; it is the centre when the crossing cluster is empty.
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
theorem abs_sub_coord_le_one_of_adj {x y : Vertex d}
    (h : (nearestNeighborGraph d).Adj x y) (i : Fin d) : |x i - y i| ≤ 1 := by
  obtain ⟨j, hj | hj⟩ := h <;> subst hj <;>
    by_cases hij : i = j <;> simp [LatticeProb.unit, hij]

/-- The vertices of a triadic cube form a finite set. -/
theorem TriadicCube.finite_vertices (Q : TriadicCube d) : Q.vertices.Finite :=
  Q.toIntegerCube.vertices.finite_toSet.subset fun x hx =>
    Finset.mem_coe.2 ((Q.mem_toIntegerCube_vertices x).2 hx)

/-- The order of candidate anchors of a cube: `ℓ∞` distance to the centre, then lexicographic
order. -/
def TriadicCube.anchorKey (Q : TriadicCube d) (y : Vertex d) : ℕ ×ₗ Lex (Fin d → ℤ) :=
  toLex (Finset.univ.sup fun i => (y i - Q.center i).natAbs, toLex y)

theorem TriadicCube.anchorKey_injective (Q : TriadicCube d) : Function.Injective Q.anchorKey := by
  intro y z h
  have h2 := congrArg (fun p => (ofLex p).2) h
  simpa [TriadicCube.anchorKey] using h2

/-- A minimizer of the anchor order over the crossing cluster. -/
def TriadicCube.IsAnchor (ω : Configuration d) (Q : TriadicCube d) (y : Vertex d) : Prop :=
  y ∈ Q.crossingCluster ω ∧ ∀ z ∈ Q.crossingCluster ω, Q.anchorKey y ≤ Q.anchorKey z

/-- The anchor order has a unique minimizer over a nonempty crossing cluster. -/
theorem TriadicCube.existsUnique_isAnchor {Q : TriadicCube d}
    (h : (Q.crossingCluster ω).Nonempty) : ∃! y, Q.IsAnchor ω y := by
  obtain ⟨y, hy, hmin⟩ := Set.exists_min_image _ Q.anchorKey
    (Q.finite_vertices.subset (Q.crossingCluster_subset ω)) h
  refine ⟨y, ⟨hy, hmin⟩, fun z hz => Q.anchorKey_injective (le_antisymm (hz.2 y hy) (hmin z hz.1))⟩

/-- The anchor `z̄(Q)` of a cube (Armstrong and Dario, Definition 3.1): the point of its
crossing cluster closest to its centre in the `ℓ∞` norm, ties broken lexicographically, and the
centre when the crossing cluster is empty. -/
noncomputable def TriadicCube.anchor (ω : Configuration d) (Q : TriadicCube d) : Vertex d :=
  if h : ∃ y, Q.IsAnchor ω y then Classical.choose h else Q.center

/-- The anchor of a cube with a nonempty crossing cluster minimizes the anchor order. -/
theorem TriadicCube.isAnchor_anchor {Q : TriadicCube d} (h : (Q.crossingCluster ω).Nonempty) :
    Q.IsAnchor ω (Q.anchor ω) := by
  have he : ∃ y, Q.IsAnchor ω y := (TriadicCube.existsUnique_isAnchor h).exists
  unfold TriadicCube.anchor
  rw [dif_pos he]
  exact Classical.choose_spec he

/-- The anchor of a cube with a nonempty crossing cluster is its unique minimizer. -/
theorem TriadicCube.anchor_eq_iff {Q : TriadicCube d} (h : (Q.crossingCluster ω).Nonempty)
    (y : Vertex d) : Q.anchor ω = y ↔ Q.IsAnchor ω y :=
  ⟨fun hy => hy ▸ TriadicCube.isAnchor_anchor h,
    fun hy => (TriadicCube.existsUnique_isAnchor h).unique (TriadicCube.isAnchor_anchor h) hy⟩

/-- The anchor of a cube with an empty crossing cluster is its centre. -/
theorem TriadicCube.anchor_of_crossingCluster_eq_empty {Q : TriadicCube d}
    (h : Q.crossingCluster ω = ∅) : Q.anchor ω = Q.center := by
  have hne : ¬ ∃ y, Q.IsAnchor ω y := by
    rintro ⟨y, hy, -⟩
    rw [h] at hy
    exact hy
  unfold TriadicCube.anchor
  rw [dif_neg hne]

/-- The anchor of a well-connected cube lies in its crossing cluster. -/
theorem TriadicCube.anchor_mem_crossingCluster {Q : TriadicCube d}
    (hQ : Q ∈ wellConnectedCubes ω) : Q.anchor ω ∈ Q.crossingCluster ω := by
  obtain ⟨root, hroot⟩ := (Q.wellConnectedIn_threeQuarter_iff ω).1 hQ.2
  exact (TriadicCube.isAnchor_anchor ⟨root, hroot.mem_crossingCluster⟩).1

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
