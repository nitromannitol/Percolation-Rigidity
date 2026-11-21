import Rigidity.Proofs.Partition.PartitionCube
import Rigidity.Percolation.TriadicStoppingMeasurable

/-!
# Measurability of the partition into good cubes

Goodness of a fixed triadic cube, the partition event, the event that a vertex has a given
partition cube, membership of a vertex in the crossing cluster of a fixed cube, and the value of
the anchor of a fixed cube or of the partition cube of a vertex are measurable events: each is a
countable combination of measurable connection events inside finite regions.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

variable {d : ℕ}

/-- Membership in the well-connected cubes of scale at least two is measurable. -/
theorem TriadicCube.measurableSet_mem_wellConnectedCubes (Q : TriadicCube d) :
    MeasurableSet {ω : Configuration d | Q ∈ TriadicCube.wellConnectedCubes ω} := by
  by_cases h : 2 ≤ Q.scale
  · have heq : {ω : Configuration d | Q ∈ TriadicCube.wellConnectedCubes ω} =
        {ω | Q.wellConnectedIn Q.threeQuarterCube.vertices ω} := by
      ext ω
      simp only [TriadicCube.wellConnectedCubes, Set.mem_setOf_eq, h, true_and]
    rw [heq]
    exact Q.measurableSet_wellConnectedIn _
  · have heq : {ω : Configuration d | Q ∈ TriadicCube.wellConnectedCubes ω} = ∅ := by
      ext ω
      simp only [TriadicCube.wellConnectedCubes, Set.mem_setOf_eq, h, false_and,
        Set.mem_empty_iff_false]
    rw [heq]
    exact MeasurableSet.empty

/-- Goodness of a triadic cube is measurable. -/
theorem TriadicCube.measurableSet_mem_goodCubes (Q : TriadicCube d) :
    MeasurableSet {ω : Configuration d | Q ∈ TriadicCube.goodCubes ω} :=
  TriadicCube.measurableSet_mem_goodOfWellConnected TriadicCube.wellConnectedCubes
    TriadicCube.measurableSet_mem_wellConnectedCubes Q

/-- Being a cube of the partition is measurable. -/
theorem TriadicCube.measurableSet_isMaximalStopping_goodCubes (Q : TriadicCube d) :
    MeasurableSet {ω : Configuration d | Q.IsMaximalStopping (TriadicCube.goodCubes ω)} :=
  TriadicCube.measurableSet_isMaximalStopping TriadicCube.goodCubes
    TriadicCube.measurableSet_mem_goodCubes Q

/-- The partition event is measurable. -/
theorem measurableSet_partitionEvent :
    MeasurableSet {ω : Configuration d | PartitionEvent ω} := by
  have h : ∀ (x : Vertex d) (Q : TriadicCube d), Measurable fun ω : Configuration d =>
      x ∈ Q.vertices ∧ Q.IsMaximalStopping (TriadicCube.goodCubes ω) := fun x Q =>
    measurable_const.and (measurableSet_setOf.1 Q.measurableSet_isMaximalStopping_goodCubes)
  refine measurableSet_setOf.2 (Measurable.forall fun x => ?_)
  unfold ExistsUnique
  exact Measurable.exists fun Q =>
    (h x Q).and (Measurable.forall fun Q' => (h x Q').imp measurable_const)

/-- The event that a vertex has a given partition cube is measurable. -/
theorem measurableSet_partitionCube_eq (x : Vertex d) (Q : TriadicCube d) :
    MeasurableSet {ω : Configuration d | PartitionEvent ω ∧ partitionCube ω x = Q} := by
  have heq : {ω : Configuration d | PartitionEvent ω ∧ partitionCube ω x = Q} =
      {ω | PartitionEvent ω} ∩
        {ω | x ∈ Q.vertices ∧ Q.IsMaximalStopping (TriadicCube.goodCubes ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hP, rfl⟩
      exact ⟨hP, partitionCube_spec hP x⟩
    · rintro ⟨hP, hx, hQ⟩
      exact ⟨hP, partitionCube_eq hP hx hQ⟩
  rw [heq]
  exact measurableSet_partitionEvent.inter (measurableSet_setOf.2 (measurable_const.and
    (measurableSet_setOf.1 Q.measurableSet_isMaximalStopping_goodCubes)))

/-- Membership in the crossing cluster of a fixed cube is measurable. -/
theorem TriadicCube.measurableSet_mem_crossingCluster (Q : TriadicCube d) (y : Vertex d) :
    MeasurableSet {ω : Configuration d | y ∈ Q.crossingCluster ω} :=
  measurableSet_setOf.2 (Measurable.exists fun r =>
    (measurableSet_setOf.1 (measurableSet_isCrossingRoot _ _ _ r)).and
      (measurableSet_setOf.1 (measurableSet_openIn_reachable _ r y)))

/-- Minimizing the anchor order over the crossing cluster is measurable. -/
theorem TriadicCube.measurableSet_isAnchor (Q : TriadicCube d) (y : Vertex d) :
    MeasurableSet {ω : Configuration d | Q.IsAnchor ω y} :=
  measurableSet_setOf.2 ((measurableSet_setOf.1 (Q.measurableSet_mem_crossingCluster y)).and
    (Measurable.forall fun z =>
      (measurableSet_setOf.1 (Q.measurableSet_mem_crossingCluster z)).imp measurable_const))

/-- The value of the anchor of a fixed cube is measurable. -/
theorem TriadicCube.measurableSet_anchor_eq (Q : TriadicCube d) (y : Vertex d) :
    MeasurableSet {ω : Configuration d | Q.anchor ω = y} := by
  have heq : {ω : Configuration d | Q.anchor ω = y} =
      {ω | Q.IsAnchor ω y} ∪ ({ω | ∀ z, z ∉ Q.crossingCluster ω} ∩ {_ω | Q.center = y}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff]
    by_cases h : (Q.crossingCluster ω).Nonempty
    · rw [TriadicCube.anchor_eq_iff h]
      obtain ⟨z, hz⟩ := h
      constructor
      · exact Or.inl
      · rintro (h1 | ⟨h2, -⟩)
        · exact h1
        · exact absurd hz (h2 z)
    · have h0 : Q.crossingCluster ω = ∅ := Set.not_nonempty_iff_eq_empty.1 h
      rw [TriadicCube.anchor_of_crossingCluster_eq_empty h0]
      constructor
      · intro hc
        exact Or.inr ⟨fun z hz => h ⟨z, hz⟩, hc⟩
      · rintro (h1 | ⟨-, h2⟩)
        · exact absurd ⟨y, h1.1⟩ h
        · exact h2
  rw [heq]
  refine (Q.measurableSet_isAnchor y).union (MeasurableSet.inter ?_ (MeasurableSet.const _))
  exact measurableSet_setOf.2 (Measurable.forall fun z =>
    (measurableSet_setOf.1 (Q.measurableSet_mem_crossingCluster z)).not)

/-- The value of the anchor of the partition cube of a vertex is measurable on the partition
event. -/
theorem measurableSet_partitionAnchor_eq (x y : Vertex d) :
    MeasurableSet {ω : Configuration d | PartitionEvent ω ∧ partitionAnchor ω x = y} := by
  have heq : {ω : Configuration d | PartitionEvent ω ∧ partitionAnchor ω x = y} =
      ⋃ Q : TriadicCube d, ({ω | PartitionEvent ω ∧ partitionCube ω x = Q} ∩
        {ω | Q.anchor ω = y}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, partitionAnchor]
    constructor
    · rintro ⟨hP, h⟩
      exact ⟨_, ⟨hP, rfl⟩, h⟩
    · rintro ⟨Q, ⟨hP, rfl⟩, h⟩
      exact ⟨hP, h⟩
  rw [heq]
  exact MeasurableSet.iUnion fun Q =>
    (measurableSet_partitionCube_eq x Q).inter (Q.measurableSet_anchor_eq y)

end Rigidity.Percolation
