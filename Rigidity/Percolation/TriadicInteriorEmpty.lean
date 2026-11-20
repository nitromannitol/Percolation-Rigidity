import Rigidity.Percolation.TriadicBoundary

/-!
# Empty interiors of triadic cubes

A cube has no points at distance at least its own side length from its
inner vertex boundary in positive dimension.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory

/-- The interior at a scale at least that of the cube is empty. -/
theorem TriadicCube.boundaryInterior_eq_empty_of_scale_le {d : ℕ} (hd : 0 < d)
    (A : TriadicCube d) (n : ℕ) (hn : A.scale ≤ n) : A.boundaryInterior n = ∅ := by
  rw [A.boundaryInterior_eq_interiorVertices n]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hi := hx.2 ⟨0, hd⟩
  have hp : (3 : ℤ) ^ A.scale ≤ (3 : ℤ) ^ n :=
    pow_le_pow_right₀ (by norm_num) hn
  have hs : 0 < A.side := A.side_pos
  change 2 * |x ⟨0, hd⟩ - A.center ⟨0, hd⟩| + 2 * (3 : ℤ) ^ n ≤
    (3 : ℤ) ^ A.scale at hi
  have ha : 0 ≤ |x ⟨0, hd⟩ - A.center ⟨0, hd⟩| := abs_nonneg _
  change 0 < (3 : ℤ) ^ A.scale at hs
  omega

/-- There is no localization discrepancy in an empty interior. -/
theorem TriadicCube.measure_localGoodCentered_boundaryInterior_discrepancy_eq_zero
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G : Ω → Set (TriadicCube d)) (A : TriadicCube d) (n : ℕ) (hn : A.scale ≤ n) :
    μ {ω | ∃ x ∈ A.boundaryInterior n, ∃ Q R : TriadicCube d,
      x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
        R.IsMaximalStopping (localGoodCentered (G ω) A.vertices) ∧ Q ≠ R} = 0 := by
  have h := A.boundaryInterior_eq_empty_of_scale_le hd n hn
  simp only [h, Set.mem_empty_iff_false, false_and, exists_const, Set.setOf_false, measure_empty]

end Rigidity.Percolation
