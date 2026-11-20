import Rigidity.Percolation.IntegerCubeUniformCoalescence
import Rigidity.Percolation.CrossingRadiusAdapter

/-!
# Uniform coalescence from radius estimates

Crossing-component estimates with ℓ¹-radius thresholds control path
coalescence uniformly at a prescribed ambient overlap scale.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External MeasureTheory
open scoped ENNReal

/-- Radius-based crossing estimates at two common scales control coalescence
at the ambient overlap threshold in every sufficiently large cube. -/
theorem IntegerCube.measure_not_coalesces_le_at_uniform_overlap_scale_of_radius {d : ℕ}
    (hd : 0 < d) (S : ℕ) (hS : 620 ≤ S) (Q : IntegerCube d)
    (hQ : S ≤ 10 * Q.size) (μ : Measure (Configuration d)) (a b : ℕ → ℝ≥0∞)
    (ha : ∀ t : ℕ, 3 ≤ t → ∀ T : IntegerCube d, T.size = 20 * t + 1 →
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices →
      μ {ω | ¬ HasCrossingComponentConnectingPaths ω (↑T.vertices)
        (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i))
        (fun n γ => ∀ z : Vertex d, ∃ i : Fin (n + 1),
          8 * (t : ℤ) < 10 * ∑ k, |γ i k - z k|)} ≤ a t)
    (hb : ∀ t : ℕ, 3 ≤ t → ∀ T : IntegerCube d, T.size = 10 * t + 1 →
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices →
      μ {ω | ¬ HasCrossingComponentConnectingPaths ω (↑T.vertices)
        (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i))
        (fun n γ => ∀ z : Vertex d, ∃ i : Fin (n + 1),
          4 * (t : ℤ) < 10 * ∑ k, |γ i k - z k|)} ≤ b t) :
    ∃ t : ℕ, 3 ≤ t ∧ S ≤ 200 * t + 219 ∧
      μ {ω | ¬ LargePathsCoalesce ω (↑Q.vertices)
        (pathDiameterAtLeast (((S / 20 : ℕ) : ℤ) - 1))} ≤
        (Q.size ^ d : ℕ) * (a t + b t) := by
  apply Q.measure_not_coalesces_le_at_uniform_overlap_scale hd S hS hQ μ a b
  · intro t ht T hsize hsub
    calc
      _ ≤ μ {ω | ¬ HasCrossingComponentConnectingPaths ω (↑T.vertices)
          (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i))
          (fun n γ => ∀ z : Vertex d, ∃ i : Fin (n + 1),
            8 * (t : ℤ) < 10 * ∑ k, |γ i k - z k|)} := by
        apply measure_mono
        intro ω hbad hgood
        exact hbad (hgood.of_l1_radius t (by omega))
      _ ≤ a t := ha t ht T hsize hsub
  · intro t ht T hsize hsub
    calc
      _ ≤ μ {ω | ¬ HasCrossingComponentConnectingPaths ω (↑T.vertices)
          (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i))
          (fun n γ => ∀ z : Vertex d, ∃ i : Fin (n + 1),
            4 * (t : ℤ) < 10 * ∑ k, |γ i k - z k|)} := by
        apply measure_mono
        intro ω hbad hgood
        apply hbad
        apply HasCrossingComponentConnectingPaths.of_l1_radius_le t (4 * t) (by omega)
          (by omega)
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hgood
      _ ≤ b t := hb t ht T hsize hsub

end Rigidity.Percolation
