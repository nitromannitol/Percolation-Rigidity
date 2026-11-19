import Rigidity.External.SmoothingParameter

/-!
# Zero-rank dual lattices

The dual lattice in the span of an empty family consists only of the origin. Consequently its
nonzero Gaussian mass is zero, independently of the scale.
-/

namespace Rigidity.External

/-- The dual lattice of an empty family consists of the origin. -/
theorem dualLattice_fin_zero (N : ℕ) (b : Fin 0 → EuclideanSpace ℝ (Fin N)) :
    dualLattice b = {0} := by
  ext y
  simp [dualLattice]

/-- The smoothing bound for a lattice of rank zero. -/
theorem smoothing_fin_zero (N : ℕ) (b : Fin 0 → EuclideanSpace ℝ (Fin N))
    (ε s : ℝ) (hε : 0 < ε) :
    Summable (fun y : {y // y ∈ dualLattice b ∧ y ≠ 0} =>
      Real.exp (-(Real.pi * s ^ 2 * ‖(y : EuclideanSpace ℝ (Fin N))‖ ^ 2))) ∧
    ∑' y : {y // y ∈ dualLattice b ∧ y ≠ 0},
      Real.exp (-(Real.pi * s ^ 2 * ‖(y : EuclideanSpace ℝ (Fin N))‖ ^ 2)) ≤ ε := by
  have : IsEmpty {y // y ∈ dualLattice b ∧ y ≠ 0} := ⟨fun y => by
    have hy : (y : EuclideanSpace ℝ (Fin N)) = 0 := by
      simpa only [dualLattice_fin_zero, Set.mem_singleton_iff] using y.property.1
    exact y.property.2 hy⟩
  have hfun : (fun y : {y // y ∈ dualLattice b ∧ y ≠ 0} =>
      Real.exp (-(Real.pi * s ^ 2 * ‖(y : EuclideanSpace ℝ (Fin N))‖ ^ 2))) =
      fun _ => 0 := funext fun y => isEmptyElim y
  rw [hfun]
  simp only [summable_zero, tsum_zero, true_and]
  exact le_of_lt hε

end Rigidity.External
