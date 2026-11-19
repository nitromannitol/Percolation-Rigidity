import Rigidity.External.SmoothingParameter
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# A basis for the dual lattice

The dual basis identifies integral inner-product coordinates with the integer span of the dual basis.
This is the lattice-coordinate construction used in Micciancio and Regev, *Worst-case to
average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 3.3.
-/

open Module

namespace Rigidity.Smoothing

private theorem inner_nondegenerate (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    (innerₗ E).Nondegenerate := by
  constructor
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)

/-- The inner-product dual of the basis formed by an independent family in its real span. -/
noncomputable def dualBasis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (b : Fin k → E) (hb : LinearIndependent ℝ b) :
    Basis (Fin k) ℝ (Submodule.span ℝ (Set.range b)) :=
  LinearMap.BilinForm.dualBasis (innerₗ _) (inner_nondegenerate _) (Basis.span hb)

/-- Integral inner products with the generators characterize the span of the dual basis. -/
theorem mem_span_dualBasis_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (b : Fin k → E) (hb : LinearIndependent ℝ b)
    (y : Submodule.span ℝ (Set.range b)) :
    y ∈ Submodule.span ℤ (Set.range (dualBasis b hb)) ↔
      ∀ i, ∃ z : ℤ, inner ℝ (y : E) (b i) = z := by
  rw [Basis.mem_span_iff_repr_mem]
  simp only [dualBasis, LinearMap.BilinForm.dualBasis_repr_apply, innerₗ_apply_apply, Submodule.coe_inner,
    Basis.coe_span_apply, Set.mem_range]
  exact forall_congr' fun _ => exists_congr fun _ => eq_comm

end Rigidity.Smoothing
