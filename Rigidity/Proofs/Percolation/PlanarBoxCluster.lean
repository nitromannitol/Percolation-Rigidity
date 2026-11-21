import Rigidity.Proofs.Percolation.PlanarBoxCrossing
import Rigidity.Proofs.Percolation.PlanarBoxGeometry

/-!
# Unique crossing clusters in planar cubes

Supercritical rectangle crossings give a unique crossing cluster in a planar cube with
stretched-exponentially high probability.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal

namespace Rigidity.Percolation

/-- Two coordinate crossings give a unique cluster crossing the cube. -/
theorem existsUnique_crossing_cluster_of_rectangles {ω : Configuration 2}
    (x : Vertex 2) (N : ℕ)
    (hH : HasOpenCrossing ω (cubeLowerCorner x N) (2 * N) (2 * N) 0)
    (hV : HasOpenCrossing ω (cubeLowerCorner x N) (2 * N) (2 * N) 1) :
    ∃! V, IsCrossingCluster ω x N V := by
  unfold HasOpenCrossing at hH hV
  rw [crossingRectangle_cubeLowerCorner] at hH hV
  simp only [cubeLowerCorner, Nat.cast_mul, Nat.cast_ofNat] at hH hV
  have heq0 : x 0 - (N : ℤ) + 2 * N = x 0 + N := by ring
  have heq1 : x 1 - (N : ℤ) + 2 * N = x 1 + N := by ring
  rw [heq0] at hH
  rw [heq1] at hV
  obtain ⟨a, b, ha, hb, ha0, hb0, hH⟩ := hH
  obtain ⟨c, d, hc, hd, hc1, hd1, hV⟩ := hV
  exact existsUnique_crossing_cluster_of_paths ha0 hb0 hc1 hd1
    (reachIn_of_reachable_induce hH) (reachIn_of_reachable_induce hV)

/-- Supercritical planar cubes have a unique crossing cluster with high probability. -/
theorem unique_crossing_cluster_failure_bound (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (x : Vertex 2) (N : ℕ),
      latticeBondLaw 2 p {ω | ¬ ∃! V, IsCrossingCluster ω x N V} ≤
        ENNReal.ofReal (C * ((2 * N : ℕ) + 1) * Real.exp (-(c * (2 * N : ℕ)))) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := kesten_rectangle_crossing p hp
  refine ⟨2 * C, c, by positivity, hc, fun x N => ?_⟩
  have hsub : {ω | ¬ ∃! V, IsCrossingCluster ω x N V} ⊆
      {ω | ¬ HasOpenCrossing ω (cubeLowerCorner x N) (2 * N) (2 * N) 0} ∪
      {ω | ¬ HasOpenCrossing ω (cubeLowerCorner x N) (2 * N) (2 * N) 1} := by
    intro ω hω
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_contra h
    push Not at h
    exact hω (existsUnique_crossing_cluster_of_rectangles x N h.1 h.2)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hb := add_le_add (hbound (cubeLowerCorner x N) (2 * N) (2 * N) 0)
    (hbound (cubeLowerCorner x N) (2 * N) (2 * N) 1)
  refine hb.trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  ring_nf
  exact le_rfl

end Rigidity.Percolation
