import Rigidity.Proofs.Smoothing.GaussianPeriod
import Rigidity.Proofs.Smoothing.TorusLift

/-!
# A lattice Gaussian on the coordinate torus

A Gaussian periodized over the integer span of a real basis defines a continuous function on the
coordinate torus. This is the periodization used in Micciancio and Regev, *Worst-case to
average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 2.9.
-/

open Module

namespace Rigidity.Smoothing

/-- The lattice Gaussian periodization descends continuously to the coordinate torus. -/
theorem exists_gaussian_torus {E d : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype d] (b : Basis d ℝ E) {a : ℝ} (ha : 0 < a) :
    ∃ g : C(UnitAddTorus d, ℂ), ∀ x : d → ℝ,
      g (fun i => (x i : UnitAddCircle)) =
        ((∑' z : Submodule.span ℤ (Set.range b),
          Real.exp (-a * ‖(z : E) + b.equivFun.symm x‖ ^ 2) : ℝ) : ℂ) := by
  classical
  let L : Submodule ℤ E := Submodule.span ℤ (Set.range b)
  let B : (d → ℝ) →ₗ[ℝ] E := b.equivFun.symm.toLinearMap
  let f : (d → ℝ) → ℂ := fun x =>
    ((∑' z : L, Real.exp (-a * ‖(z : E) + B x‖ ^ 2) : ℝ) : ℂ)
  have hB : Continuous B := B.continuous_of_finiteDimensional
  have hf : Continuous f := Complex.continuous_ofReal.comp ((continuous_tsum_gaussian L ha).comp hB)
  apply exists_continuous_torus_lift f hf
  intro x n
  have hn : B (fun i => (n i : ℝ)) ∈ L := by
    rw [Basis.mem_span_iff_repr_mem]
    intro i
    use n i
    simp only [← Basis.equivFun_apply, B, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, algebraMap_int_eq]
    rfl
  change ((∑' z : L, Real.exp (-a * ‖(z : E) + B (x + fun i => (n i : ℝ))‖ ^ 2) : ℝ) : ℂ) = _
  rw [map_add]
  exact congrArg Complex.ofReal (tsum_gaussian_add_lattice L a (B x) ⟨_, hn⟩)

end Rigidity.Smoothing
