import Rigidity.Percolation.TriadicStableCoverage
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Geometric bounds for stable cube coverage

A geometric bound on the probabilities of bad cubes implies the summable-tail
hypothesis used in the stable cube partition construction.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- A geometric scale bound has a finite double tail. -/
theorem TriadicCube.double_tail_ne_top_of_geometric {d : ℕ} (p : ℕ → ℝ≥0∞)
    (C r : ℝ≥0∞) (hC : C ≠ ∞) (hr : r < 1)
    (hp : ∀ n, p n ≤ C * r ^ n) :
    (∑' n : ℕ, ∑' m : ℕ, (19 ^ d : ℝ≥0∞) * p (n + m)) ≠ ∞ := by
  have hgeo : (∑' n : ℕ, r ^ n) ≠ ∞ := ne_of_lt (tsum_geometric_lt_top.mpr hr)
  have hbound : (∑' n : ℕ, ∑' m : ℕ, (19 ^ d : ℝ≥0∞) * p (n + m)) ≤
      (19 ^ d : ℝ≥0∞) * C * (∑' n : ℕ, r ^ n) * (∑' m : ℕ, r ^ m) := by
    calc
      _ ≤ ∑' n : ℕ, ∑' m : ℕ, (19 ^ d : ℝ≥0∞) * (C * r ^ (n + m)) := by
        apply ENNReal.tsum_le_tsum
        intro n
        apply ENNReal.tsum_le_tsum
        intro m
        gcongr
        exact hp (n + m)
      _ = _ := by
        simp_rw [pow_add, ← mul_assoc, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
        rw [ENNReal.tsum_mul_left]
  apply ne_top_of_le_ne_top _ hbound
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hC) hgeo) hgeo

/-- A geometric bad-cube bound yields an almost-sure maximal stopping partition. -/
theorem TriadicCube.ae_existsUnique_maximal_stopping_of_geometric {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (G : Ω → Set (TriadicCube d))
    (C r : ℝ≥0∞) (hC : C ≠ ∞) (hr : r < 1)
    (hprob : ∀ R : TriadicCube d, μ {ω | R ∉ G ω} ≤ C * r ^ R.scale) :
    ∀ᵐ ω ∂μ, ∀ x : Vertex d,
      ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω) := by
  apply ae_existsUnique_maximal_stopping μ G (fun n => C * r ^ n) hprob
  exact double_tail_ne_top_of_geometric _ C r hC hr (fun _ => le_rfl)

end Rigidity.Percolation
