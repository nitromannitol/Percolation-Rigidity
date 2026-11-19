import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integrating a lattice periodization

A summably integrable lattice periodization over a fundamental domain integrates to the integral
of the original function. This is the integral rearrangement in the Gaussian lattice argument of
Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian measures*, SIAM J.
Comput. 37 (2007), Lemma 2.9.
-/

open MeasureTheory Module

namespace Rigidity.Smoothing

/-- Integration of a summably integrable lattice periodization unfolds the fundamental domain. -/
theorem integral_tsum_lattice_add {E d : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype d]
    (b : Basis d ℝ E) (μ : Measure E) [Measure.IsAddHaarMeasure μ] (f : E → ℂ)
    (hf : Integrable f μ)
    (hshift : ∀ z : Submodule.span ℤ (Set.range b),
      IntegrableOn (fun x : E => f ((z : E) + x)) (ZSpan.fundamentalDomain b) μ)
    (hsum : Summable (fun z : Submodule.span ℤ (Set.range b) =>
      ∫ x in ZSpan.fundamentalDomain b, ‖f ((z : E) + x)‖ ∂μ)) :
    (∫ x in ZSpan.fundamentalDomain b,
      ∑' z : Submodule.span ℤ (Set.range b), f ((z : E) + x) ∂μ) = ∫ x, f x ∂μ := by
  letI : VAddInvariantMeasure (Submodule.span ℤ (Set.range b)) E μ :=
    ⟨fun z {s} _ => by
      simpa only [Submodule.vadd_def, vadd_eq_add] using measure_preimage_add μ (z : E) s⟩
  have hfund : (∫ x, f x ∂μ) = ∑' z : Submodule.span ℤ (Set.range b),
      ∫ x in ZSpan.fundamentalDomain b, f ((z : E) + x) ∂μ := by
    simpa only [Submodule.vadd_def, vadd_eq_add] using
      (ZSpan.isAddFundamentalDomain b μ).integral_eq_tsum'' f hf
  exact (integral_tsum_of_summable_integral_norm hshift hsum).symm.trans hfund.symm

end Rigidity.Smoothing
