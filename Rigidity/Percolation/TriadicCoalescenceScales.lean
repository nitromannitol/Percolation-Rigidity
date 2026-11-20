import Rigidity.Percolation.IntegerCubeCoalescenceScales

/-!
# Coalescence scales for triadic test cubes

The path diameter used for a triadic cube dominates the local threshold in
each of its test cubes.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External MeasureTheory
open scoped ENNReal

/-- Every path selected by the ambient cube has at least one-tenth the
side length of any of its test cubes as coordinate diameter. -/
theorem TriadicCube.largePath_testCube_diameter {d n : ℕ} (Q : TriadicCube d)
    {interior : Set (Vertex d)} {T : IntegerCube d} (hT : T ∈ Q.testCubes interior)
    {γ : Fin (n + 1) → Vertex d} (hγ : Q.largePath n γ) :
    pathDiameterAtLeast (T.size / 10 : ℕ) n γ := by
  obtain ⟨i, j, k, hk⟩ := hγ
  have hTsize := hT.2.1
  have hsizenonneg : (0 : ℤ) ≤ T.size := by exact Nat.cast_nonneg _
  have hdiv : 10 * (T.size / 10) ≤ T.size := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self T.size 10
  have hdiv' : 10 * (((T.size / 10 : ℕ) : ℤ)) ≤ T.size := by exact_mod_cast hdiv
  refine ⟨i, j, k, ?_⟩
  omega

/-- Compatible subcube estimates control large-path coalescence in each
sufficiently large triadic test cube. -/
theorem TriadicCube.measure_testCube_not_coalesces_le {d : ℕ}
    (hd : 0 < d) (Q : TriadicCube d) {interior : Set (Vertex d)}
    (T : IntegerCube d) (hT : T ∈ Q.testCubes interior) (hsize : 61 ≤ T.size)
    (μ : Measure (Configuration d)) (a b : ℕ → ℝ≥0∞)
    (ha : ∀ t : ℕ, 3 ≤ t → ∀ U : IntegerCube d, U.size = 20 * t + 1 →
      (↑U.vertices : Set (Vertex d)) ⊆ T.vertices →
      μ {ω | ¬ HasCrossingComponentConnectingPaths ω (↑U.vertices)
        (fun i => ↑(U.lowerFace i)) (fun i => ↑(U.upperFace i))
        (pathDiameterAtLeast (2 * (t : ℤ)))} ≤ a t)
    (hb : ∀ t : ℕ, 3 ≤ t → ∀ U : IntegerCube d, U.size = 10 * t + 1 →
      (↑U.vertices : Set (Vertex d)) ⊆ T.vertices →
      μ {ω | ¬ HasCrossingComponentConnectingPaths ω (↑U.vertices)
        (fun i => ↑(U.lowerFace i)) (fun i => ↑(U.upperFace i))
        (pathDiameterAtLeast (2 * (t : ℤ)))} ≤ b t) :
    ∃ t : ℕ, 3 ≤ t ∧ T.size ≤ 20 * t + 20 ∧
      μ {ω | ¬ LargePathsCoalesce ω (↑T.vertices) Q.largePath} ≤
        (T.size ^ d : ℕ) * (a t + b t) := by
  exact T.measure_not_coalesces_le_at_compatible_scales hd hsize Q.largePath
    (fun _ _ hγ => Q.largePath_testCube_diameter hT hγ) μ a b ha hb

end Rigidity.Percolation
