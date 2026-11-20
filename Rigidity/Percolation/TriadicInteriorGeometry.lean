import Rigidity.Percolation.TriadicLocalizationCenteredInterior

/-!
# Interior points of triadic cubes

Coordinate margins inside a cube imply a lower bound on the distance to
any lattice point outside the cube.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- Points at least `3 ^ n` from every coordinate face of the cube. -/
def TriadicCube.interiorVertices {d : ℕ} (A : TriadicCube d) (n : ℕ) : Set (Vertex d) :=
  {x ∈ A.vertices | ∀ i, 2 * |x i - A.center i| + 2 * (3 : ℤ) ^ n ≤ A.side}

/-- A point in the coordinate interior and a point outside the cube differ by
at least the interior margin in some coordinate. -/
theorem TriadicCube.exists_coord_distance_le_of_mem_interiorVertices {d : ℕ}
    (A : TriadicCube d) (n : ℕ) {x y : Vertex d}
    (hx : x ∈ A.interiorVertices n) (hy : y ∉ A.vertices) :
    ∃ i, (3 : ℤ) ^ n ≤ |x i - y i| := by
  classical
  have hy' : ¬ ∀ i, |2 * (y i - A.center i)| < A.side := hy
  push Not at hy'
  obtain ⟨i, hi⟩ := hy'
  refine ⟨i, ?_⟩
  rw [abs_mul, abs_of_pos (show (0 : ℤ) < 2 by norm_num)] at hi
  have hx' := hx.2 i
  have htri : |y i - A.center i| ≤ |y i - x i| + |x i - A.center i| := by
    have heq : y i - A.center i = (y i - x i) + (x i - A.center i) := by ring
    rw [heq]
    exact abs_add_le _ _
  rw [abs_sub_comm (y i) (x i)] at htri
  omega

/-- The centered-support discrepancy bound applies to the coordinate interior
of a triadic cube. -/
theorem TriadicCube.measure_localGoodCentered_interior_discrepancy_le {d : ℕ} (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → Set (TriadicCube d)) (A : TriadicCube d) (n : ℕ) (hn : 3 ≤ n)
    (C : ℝ≥0∞) (b c : ℝ) (hb : 1 < b) (hc : 0 < c)
    (hprob : ∀ T : TriadicCube d,
      μ {ω | T ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ T.scale))) :
    μ {ω | ∃ x ∈ A.interiorVertices n, ∃ Q R : TriadicCube d,
      x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
        R.IsMaximalStopping (localGoodCentered (G ω) A.vertices) ∧ Q ≠ R} ≤
      max 1 (C * ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k) *
        ((2 * 3 ^ (A.scale - (n - 3 + 1)) + 29 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp ((-c * b ^ (n - 3 + 1)) / d)) := by
  apply measure_localGoodCentered_stopping_discrepancy_le hd μ G A.vertices A
    (A.interiorVertices n) (fun _ hx => hx.1) n hn
  · intro x hx y hy
    exact A.exists_coord_distance_le_of_mem_interiorVertices n hx hy
  · exact hb
  · exact hc
  · exact hprob

end Rigidity.Percolation
