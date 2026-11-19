import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Dual frequencies of a lattice basis

Integer frequencies in basis coordinates correspond to vectors in the integer span of the
inner-product dual basis. This is the coordinate pairing used in the Gaussian lattice argument of
Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian measures*, SIAM J.
Comput. 37 (2007), Lemma 2.9.
-/

open Module

namespace Rigidity.Smoothing

private theorem inner_nondegenerate' (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    (innerₗ E).Nondegenerate := by
  constructor
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)

/-- The inner-product dual of a finite real basis. -/
noncomputable def frequencyBasis {E d : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype d] (b : Basis d ℝ E) : Basis d ℝ E := by
  classical
  exact LinearMap.BilinForm.dualBasis (innerₗ E) (inner_nondegenerate' E) b

/-- The vector corresponding to an integer frequency in basis coordinates. -/
noncomputable def dualFrequency {E d : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype d] (b : Basis d ℝ E) (n : d → ℤ) : E :=
  (frequencyBasis b).equivFun.symm (fun i => (n i : ℝ))

/-- A dual frequency pairs with each basis vector as the corresponding integer. -/
theorem inner_dualFrequency_basis {E d : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype d] (b : Basis d ℝ E) (n : d → ℤ) (i : d) :
    inner ℝ (dualFrequency b n) (b i) = (n i : ℝ) := by
  classical
  rw [← innerₗ_apply_apply, ← LinearMap.BilinForm.dualBasis_repr_apply (inner_nondegenerate' E) b]
  change (frequencyBasis b).repr (dualFrequency b n) i = _
  rw [← Basis.equivFun_apply]
  simp only [dualFrequency, LinearEquiv.apply_symm_apply]

/-- A dual frequency pairs with a vector as the dot product of their coordinates. -/
theorem inner_dualFrequency_equivFun_symm {E d : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype d] (b : Basis d ℝ E) (n : d → ℤ) (x : d → ℝ) :
    inner ℝ (dualFrequency b n) (b.equivFun.symm x) = ∑ i, x i * (n i : ℝ) := by
  rw [Basis.equivFun_symm_apply, inner_sum]
  simp only [real_inner_smul_right, inner_dualFrequency_basis]

/-- A dual frequency belongs to the integer span of the dual basis. -/
theorem dualFrequency_mem_span {E d : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype d] (b : Basis d ℝ E) (n : d → ℤ) :
    dualFrequency b n ∈ Submodule.span ℤ (Set.range (frequencyBasis b)) := by
  rw [Basis.mem_span_iff_repr_mem]
  intro i
  use n i
  simp only [← Basis.equivFun_apply, dualFrequency, LinearEquiv.apply_symm_apply, algebraMap_int_eq]
  rfl

/-- Distinct integer coordinate frequencies give distinct dual vectors. -/
theorem dualFrequency_injective {E d : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype d] (b : Basis d ℝ E) : Function.Injective (dualFrequency b) := by
  intro n m h
  funext i
  exact_mod_cast (inner_dualFrequency_basis b n i).symm.trans
    ((congrArg (fun w => inner ℝ w (b i)) h).trans (inner_dualFrequency_basis b m i))

end Rigidity.Smoothing
