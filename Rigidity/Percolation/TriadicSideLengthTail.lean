import Rigidity.Percolation.TriadicStretchedTail
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stopping bounds from stretched-exponential side-length estimates

The usual bad-cube bound is exponential in a positive power of its side length.
This form yields almost-sure coverage and quantitative stopping-cube bounds.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- A stretched-exponential bound in the triadic side length gives the same
form of bound for the scale of a stopping cube containing a fixed point. -/
theorem TriadicCube.measure_exists_large_stopping_le_side_stretched {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (G : Ω → Set (TriadicCube d))
    (C : ℝ≥0∞) (s c : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hprob : ∀ R : TriadicCube d,
      μ {ω | R ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ R.scale) ^ s)))
    (x : Vertex d) (n : ℕ) :
    μ {ω | ∃ R : TriadicCube d, x ∈ R.vertices ∧ R.IsStopping (G ω) ∧ n + 1 < R.scale} ≤
      (19 ^ d : ℝ≥0∞) * C * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ n) ^ s)) *
        ∑' m : ℕ, ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ s - 1))) ^ m := by
  have hb : 1 < (3 : ℝ) ^ s := Real.one_lt_rpow (by norm_num) hs
  have hprob' : ∀ R : TriadicCube d,
      μ {ω | R ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ s) ^ R.scale)) := by
    intro R
    simpa only [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3)] using hprob R
  simpa only [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3)] using
    measure_exists_large_stopping_le_stretched μ G C ((3 : ℝ) ^ s) c hb hc hprob' x n

/-- A stretched-exponential bad-cube bound in the side length yields an
almost-sure maximal stopping partition. -/
theorem TriadicCube.ae_existsUnique_maximal_stopping_of_side_stretched {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (G : Ω → Set (TriadicCube d))
    (C : ℝ≥0∞) (hC : C ≠ ∞) (s c : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hprob : ∀ R : TriadicCube d,
      μ {ω | R ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ R.scale) ^ s))) :
    ∀ᵐ ω ∂μ, ∀ x : Vertex d,
      ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω) := by
  apply ae_existsUnique_maximal_stopping_of_stretched μ G C hC ((3 : ℝ) ^ s) c
    (Real.one_lt_rpow (by norm_num) hs) hc
  intro R
  simpa only [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3)] using hprob R

end Rigidity.Percolation
