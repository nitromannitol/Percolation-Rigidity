import PercolationClusterHomogenization.Proofs.Partition.Paths
import PercolationClusterHomogenization.Proofs.Partition.Measurability
import PercolationClusterHomogenization.Proofs.Partition.AlmostSure
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw
import LatticeProb.Prob.Percolation.OpenComponentTranslation

/-!
# Anchors of the translated partitions into good cubes of `ℤᵈ`

Dario's §5 uses, besides the partition `𝒫` of good cubes, its translates `𝒫_y = y + 𝒫(τ_{-y})`:
the partition computed from the configuration seen from `y`, moved back by `y`. For the partition
into good cubes of Armstrong and Dario in every dimension (`Rigidity.Percolation.partitionCube`,
anchors `partitionAnchor`) this file proves:

* on the partition event, the open component of the anchors is infinite
  (`infinite_partitionAnchor`), since all anchors lie in one open component
  (`Rigidity.Percolation.reachable_partitionAnchor`);
* the anchor, set to the vertex itself off the partition event (`guardAnchor`), is a measurable
  function of the configuration (`measurable_guardAnchor`);
* the anchor `shiftedAnchor y ω z = y + guardAnchor (τ_{-y} ω) (z - y)` of `𝒫_y` is measurable,
  moves with translations of the configuration (`shiftedAnchor_translation`) and lies in the
  infinite cluster when the partition event holds for `τ_{-y} ω` (`infinite_shiftedAnchor`).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

variable {d : ℕ} {ω : Configuration d}

/-- The open component of the anchors is infinite. -/
theorem infinite_partitionAnchor (hd : 0 < d) (hP : PartitionEvent ω) (x : Vertex d) :
    ω ∈ infiniteComponentEvent (partitionAnchor ω x) := by
  change ((openGraph ω).connectedComponentMk (partitionAnchor ω x)).supp.Infinite
  intro hfin
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  haveI : Infinite (Vertex d) := Pi.infinite_of_right
  apply Set.infinite_univ (α := Vertex d)
  have hcover : (Set.univ : Set (Vertex d)) ⊆
      ⋃ a ∈ ((openGraph ω).connectedComponentMk (partitionAnchor ω x)).supp,
        (partitionCube ω a).vertices := by
    intro y _
    simp only [Set.mem_iUnion]
    refine ⟨partitionAnchor ω y, ?_, ?_⟩
    · rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
      exact (reachable_partitionAnchor hd hP x y).symm
    · rw [partitionCube_eq_of_mem hP (partitionAnchor_mem hP y)]
      exact mem_partitionCube hP y
  exact (hfin.biUnion fun a _ => (partitionCube ω a).toIntegerCube.vertices.finite_toSet.subset
    fun x hx => Finset.mem_coe.2 (((partitionCube ω a).mem_toIntegerCube_vertices x).2 hx)).subset
    hcover

/-- Translating a configuration moves infinite components. -/
theorem mem_infiniteComponentEvent_translation (z : Vertex d) {ω : Configuration d} {a : Vertex d}
    (ha : ω ∈ infiniteComponentEvent a) :
    configurationTranslation z ω ∈ infiniteComponentEvent (a + z) := by
  have h := (openComponentTranslation_infinite_iff z ((openGraph ω).connectedComponentMk a)).2 ha
  rw [openComponentTranslation_mk] at h
  exact h

/-- The anchor of the partition cube, set to the vertex itself off the partition event. -/
noncomputable def guardAnchor (ω : Configuration d) (z : Vertex d) : Vertex d :=
  if PartitionEvent ω then partitionAnchor ω z else z

theorem guardAnchor_of_event (hP : PartitionEvent ω) (z : Vertex d) :
    guardAnchor ω z = partitionAnchor ω z := if_pos hP

/-- **The anchor is measurable.** -/
theorem measurable_guardAnchor (z : Vertex d) : Measurable fun ω => guardAnchor ω z := by
  refine measurable_to_countable' fun y => ?_
  have e : (fun ω => guardAnchor ω z) ⁻¹' {y} =
      {ω : Configuration d | PartitionEvent ω ∧ partitionAnchor ω z = y} ∪
        ({ω : Configuration d | PartitionEvent ω}ᶜ ∩ {_ω | z = y}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_compl_iff, guardAnchor]
    by_cases hP : PartitionEvent ω <;> simp [hP]
  rw [e]
  exact (measurableSet_partitionAnchor_eq z y).union
    (measurableSet_partitionEvent.compl.inter (MeasurableSet.const _))

/-- The anchor of the translated partition `𝒫_y`. -/
noncomputable def shiftedAnchor (y : Vertex d) (ω : Configuration d) (z : Vertex d) : Vertex d :=
  y + guardAnchor (configurationTranslation (-y) ω) (z - y)

theorem measurable_shiftedAnchor (y z : Vertex d) : Measurable fun ω => shiftedAnchor y ω z :=
  (measurable_of_countable fun v : Vertex d => y + v).comp
    ((measurable_guardAnchor (z - y)).comp
      (configurationTranslationMeasurableEquiv (-y)).measurable)

theorem shiftedAnchor_zero (ω : Configuration d) (z : Vertex d) :
    shiftedAnchor 0 ω z = guardAnchor ω z := by
  simp [shiftedAnchor, configurationTranslation_zero]

/-- **The translated partitions move with the configuration**: `𝒫_{y + y'}(τ_{y'} ω) = y' + 𝒫_y(ω)`
at the level of anchors. -/
theorem shiftedAnchor_translation (y y' : Vertex d) (ω : Configuration d) (v : Vertex d) :
    shiftedAnchor (y + y') (configurationTranslation y' ω) (v + y') = shiftedAnchor y ω v + y' := by
  unfold shiftedAnchor
  rw [configurationTranslation_add, show -(y + y') + y' = -y by abel,
    show v + y' - (y + y') = v - y by abel]
  abel

/-- On the partition event of `τ_{-y} ω`, the anchors of `𝒫_y` lie in an infinite component. -/
theorem infinite_shiftedAnchor (hd : 0 < d) {y : Vertex d}
    (hP : PartitionEvent (configurationTranslation (-y) ω)) (z : Vertex d) :
    ω ∈ infiniteComponentEvent (shiftedAnchor y ω z) := by
  have h := mem_infiniteComponentEvent_translation y (infinite_partitionAnchor hd hP (z - y))
  rw [configurationTranslation_add, add_neg_cancel, configurationTranslation_zero] at h
  unfold shiftedAnchor
  rw [guardAnchor_of_event hP, add_comm]
  exact h

/-- The partition event holds almost surely for every translate of the configuration. -/
theorem ae_partitionEvent_translation [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (y : Vertex d) :
    ∀ᵐ ω ∂latticeBondLaw d p, PartitionEvent (configurationTranslation y ω) :=
  (measurePreserving_configurationTranslation p y).quasiMeasurePreserving.ae
    (ae_partitionEvent hd hpc)

end Rigidity.Corrector.GeneralDim
