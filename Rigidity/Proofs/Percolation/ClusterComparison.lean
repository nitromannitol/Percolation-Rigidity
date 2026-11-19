import Rigidity.Proofs.Percolation.BondLawComparison
import LatticeProb.Prob.Percolation.LatticeBondCritical

/-!
# Comparison of lattice clusters

The two bond models have identical open graphs, percolation probabilities, and critical values.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation _root_.Percolation.Literature

/-- Extending a Boolean configuration gives the same open graph. -/
theorem openGraph_eq (d : ℕ) (ω : Configuration d) :
    _root_.Percolation.Literature.openGraph
        (extendEdges (LatticeModels.zdGraph d) (toEdgeConfig d ω)) =
      LatticeProb.Percolation.openGraph ω := by
  ext x y
  rw [_root_.Percolation.Literature.openGraph_adj, LatticeProb.Percolation.openGraph_adj_iff]
  constructor
  · rintro ⟨⟨h, hω⟩, _⟩
    have hxy : (nearestNeighborGraph d).Adj x y := by
      rw [nearestNeighborGraph_eq_zdGraph, ← SimpleGraph.mem_edgeSet]
      exact h
    refine ⟨hxy, ?_⟩
    change ω ((bondEquiv d).symm ⟨s(x, y), h⟩) = true at hω
    have heq : (bondEquiv d).symm ⟨s(x, y), h⟩ = bondOfAdjacent hxy := Subtype.ext rfl
    rw [heq] at hω
    exact hω
  · rintro ⟨hxy, hω⟩
    have h : s(x, y) ∈ (LatticeModels.zdGraph d).edgeSet := by
      rw [SimpleGraph.mem_edgeSet, ← nearestNeighborGraph_eq_zdGraph]
      exact hxy
    refine ⟨⟨h, ?_⟩, hxy.ne⟩
    change ω ((bondEquiv d).symm ⟨s(x, y), h⟩) = true
    have heq : (bondEquiv d).symm ⟨s(x, y), h⟩ = bondOfAdjacent hxy := Subtype.ext rfl
    rw [heq]
    exact hω

/-- A component support is the corresponding reachability cluster. -/
theorem component_supp_eq_cluster {W : Type*} (G : SimpleGraph W) (x : W) :
    (G.connectedComponentMk x).supp = {y | G.Reachable x y} := by
  ext y
  simp only [SimpleGraph.ConnectedComponent.mem_supp_iff,
    SimpleGraph.ConnectedComponent.eq, Set.mem_setOf_eq]
  exact ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩

/-- Infinite-component events agree under the configuration map. -/
theorem infinite_event_iff (d : ℕ) (ω : Configuration d) (x : Vertex d) :
    ω ∈ infiniteComponentEvent x ↔
      extendEdges (LatticeModels.zdGraph d) (toEdgeConfig d ω) ∈ percolatesAt x := by
  change ((LatticeProb.Percolation.openGraph ω).connectedComponentMk x).supp.Infinite ↔
    (_root_.Percolation.Literature.openCluster
      (extendEdges (LatticeModels.zdGraph d) (toEdgeConfig d ω)) x).Infinite
  rw [component_supp_eq_cluster, ← openGraph_eq]
  rfl

/-- The two definitions of percolation probability agree in every dimension. -/
theorem theta_eq (d : ℕ) (p : unitInterval) :
    LatticeProb.Percolation.theta d p =
      _root_.Percolation.Literature.theta (LatticeModels.zdGraph d) 0 p := by
  unfold LatticeProb.Percolation.theta _root_.Percolation.Literature.theta
  have he : infiniteComponentEvent (0 : Vertex d) =
      (extendEdges (LatticeModels.zdGraph d) ∘ toEdgeConfig d) ⁻¹' percolatesAt 0 := by
    ext ω
    exact infinite_event_iff d ω 0
  rw [he, ← map_measureReal_apply
    ((measurable_extendEdges _).comp (by unfold toEdgeConfig; fun_prop))
    (measurableSet_percolatesAt_holds 0), map_latticeBondLaw]

/-- The critical probabilities of the two lattice models coincide. -/
theorem criticalProbability_eq (d : ℕ) [NeZero d] :
    criticalProbability d = criticalProb (LatticeModels.zdGraph d) 0 := by
  have hs : {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧
      0 < LatticeProb.Percolation.theta d p} =
      {q : ℝ | ∃ h : q ∈ unitInterval,
        0 < _root_.Percolation.Literature.theta (LatticeModels.zdGraph d) 0 ⟨q, h⟩} := by
    ext q
    constructor
    · rintro ⟨p, rfl, hp⟩
      exact ⟨p.property, by simpa only [← theta_eq] using hp⟩
    · rintro ⟨h, hp⟩
      exact ⟨⟨q, h⟩, rfl, by simpa only [theta_eq] using hp⟩
  have h1 : (1 : ℝ) ∈ {q : ℝ | ∃ h : q ∈ unitInterval,
      0 < _root_.Percolation.Literature.theta (LatticeModels.zdGraph d) 0 ⟨q, h⟩} := by
    refine ⟨(1 : unitInterval).property, ?_⟩
    rw [← theta_eq]
    change 0 < LatticeProb.Percolation.theta d (1 : unitInterval)
    rw [LatticeProb.Percolation.theta_one]
    exact zero_lt_one
  unfold criticalProbability criticalProb
  rw [hs, Set.union_eq_left.mpr]
  rintro q rfl
  exact h1

end Rigidity.Percolation
