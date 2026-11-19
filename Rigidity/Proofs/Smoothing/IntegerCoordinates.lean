import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Integer coordinates in a lattice basis

The integer span of a real basis is parametrized bijectively by integer coordinate vectors. This
reindexing is used in the lattice Gaussian argument of Micciancio and Regev, *Worst-case to
average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 2.9.
-/

open Module

namespace Rigidity.Smoothing

/-- Integer coordinate vectors parametrize the integer span of a real basis. -/
noncomputable def integerCoordinates {E d : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype d] (b : Basis d ℝ E) : (d → ℤ) ≃ Submodule.span ℤ (Set.range b) :=
  (b.restrictScalars ℤ).equivFun.symm.toEquiv

/-- The coordinate parametrization agrees with real linear combination of the basis. -/
theorem coe_integerCoordinates {E d : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype d] (b : Basis d ℝ E) (n : d → ℤ) :
    (integerCoordinates b n : E) = b.equivFun.symm (fun i => (n i : ℝ)) := by
  classical
  change ((b.restrictScalars ℤ).equivFun.symm n : E) = _
  simp only [Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul,
    Basis.restrictScalars_apply, Int.cast_smul_eq_zsmul]

/-- A sum over a lattice can be reindexed by integer coordinates. -/
theorem tsum_integerCoordinates {E d A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype d] [AddCommMonoid A] [TopologicalSpace A] (b : Basis d ℝ E) (f : E → A) :
    (∑' z : Submodule.span ℤ (Set.range b), f (z : E)) =
      ∑' n : d → ℤ, f (b.equivFun.symm (fun i => (n i : ℝ))) := by
  simpa only [coe_integerCoordinates] using ((integerCoordinates b).tsum_eq (fun z => f (z : E))).symm

end Rigidity.Smoothing
