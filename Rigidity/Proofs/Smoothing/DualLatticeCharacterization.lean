import Rigidity.Proofs.Smoothing.DualCoordinateMass

/-!
# Dual lattice coordinates

The integer span of a dual basis consists exactly of vectors whose pairings with the primal basis
are integral. This is the dual lattice identification in Micciancio and Regev, *Worst-case to
average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 3.3.
-/

open Module

namespace Rigidity.Smoothing

/-- Integral pairings characterize the integer span of the dual basis. -/
theorem mem_span_frequencyBasis_iff {E d : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype d] (b : Basis d ℝ E) (y : E) :
    y ∈ Submodule.span ℤ (Set.range (frequencyBasis b)) ↔
      ∀ i, ∃ z : ℤ, inner ℝ y (b i) = z := by
  classical
  rw [Basis.mem_span_iff_repr_mem]
  simp only [frequencyBasis, LinearMap.BilinForm.dualBasis_repr_apply, innerₗ_apply_apply,
    Set.mem_range]
  exact forall_congr' fun _ => exists_congr fun _ => eq_comm

end Rigidity.Smoothing
