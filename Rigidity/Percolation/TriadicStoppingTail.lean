import Rigidity.Percolation.TriadicGeometricCoverage

/-!
# Tail estimates for stopping cubes

A stopping cube much larger than a prescribed scale forces the cube at that
scale containing the same point to be unstable. This transfers bad-cube
probability estimates to the size of the stopping cubes.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- A stopping cube containing a point has scale at most one above any stable
cube containing that point. -/
theorem TriadicCube.measure_exists_large_stopping_le {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (G : Ω → Set (TriadicCube d))
    (p : ℕ → ℝ≥0∞) (hprob : ∀ R : TriadicCube d, μ {ω | R ∉ G ω} ≤ p R.scale)
    (x : Vertex d) (n : ℕ) :
    μ {ω | ∃ R : TriadicCube d, x ∈ R.vertices ∧ R.IsStopping (G ω) ∧ n + 1 < R.scale} ≤
      ∑' m : ℕ, (19 ^ d : ℝ≥0∞) * p (n + m) := by
  classical
  obtain ⟨Q, ⟨hscale, hx⟩, _⟩ := existsUnique_mem d n x
  calc
    _ ≤ μ {ω | Q ∉ stableGood (G ω)} := by
      apply measure_mono
      intro ω hω hQ
      obtain ⟨R, hxR, hR, hlarge⟩ := hω
      have hle := hR.scale_le_of_mem hQ hx hxR
      omega
    _ ≤ _ := by
      simpa only [hscale] using measure_not_mem_stableGood_le μ G p hprob Q

/-- Geometric bounds on bad cubes give a geometric tail for the scale of any
stopping cube containing a fixed point. -/
theorem TriadicCube.measure_exists_large_stopping_le_geometric {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (G : Ω → Set (TriadicCube d))
    (C r : ℝ≥0∞)
    (hprob : ∀ R : TriadicCube d, μ {ω | R ∉ G ω} ≤ C * r ^ R.scale)
    (x : Vertex d) (n : ℕ) :
    μ {ω | ∃ R : TriadicCube d, x ∈ R.vertices ∧ R.IsStopping (G ω) ∧ n + 1 < R.scale} ≤
      (19 ^ d : ℝ≥0∞) * C * r ^ n * ∑' m : ℕ, r ^ m := by
  calc
    _ ≤ ∑' m : ℕ, (19 ^ d : ℝ≥0∞) * (C * r ^ (n + m)) :=
      measure_exists_large_stopping_le μ G (fun k => C * r ^ k) hprob x n
    _ = _ := by
      simp_rw [pow_add, ← mul_assoc, ENNReal.tsum_mul_left]

end Rigidity.Percolation
