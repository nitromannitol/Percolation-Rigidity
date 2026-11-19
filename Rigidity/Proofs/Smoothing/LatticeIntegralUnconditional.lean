import Rigidity.Proofs.Smoothing.LatticeIntegral
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Unfolding integrable lattice periodizations

An integrable function has summably integrable translates over a lattice fundamental domain.
Consequently its periodization may be integrated term by term, as in the Gaussian lattice
argument of Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian
measures*, SIAM J. Comput. 37 (2007), Lemma 2.9.
-/

open MeasureTheory Module
open scoped Pointwise

namespace Rigidity.Smoothing

/-- Integrability implies summable integrals of lattice translates over a fundamental domain. -/
theorem summable_integral_norm_lattice_add {E d : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype d]
    (b : Basis d ℝ E) (μ : Measure E) [Measure.IsAddHaarMeasure μ] (f : E → ℂ)
    (hf : Integrable f μ) :
    Summable (fun z : Submodule.span ℤ (Set.range b) =>
      ∫ x in ZSpan.fundamentalDomain b, ‖f ((z : E) + x)‖ ∂μ) := by
  let L : Submodule ℤ E := Submodule.span ℤ (Set.range b)
  let D := ZSpan.fundamentalDomain b
  letI : VAddInvariantMeasure L E μ :=
    ⟨fun z {s} _ => by
      simpa only [Submodule.vadd_def, vadd_eq_add] using measure_preimage_add μ (z : E) s⟩
  have hpart : Integrable f (Measure.sum fun z : L => μ.restrict (z +ᵥ D)) := by
    rw [(ZSpan.isAddFundamentalDomain b μ).sum_restrict]
    exact hf
  apply hpart.summable_integral.congr
  intro z
  change (∫ x in (z : E) +ᵥ D, ‖f x‖ ∂μ) = _
  rw [← Set.image_vadd]
  exact (measurePreserving_add_left μ (z : E)).setIntegral_image_emb
    (MeasurableEquiv.addLeft (z : E)).measurableEmbedding (fun x => ‖f x‖) D

/-- The integral of a lattice periodization unfolds to the integral of the original function. -/
theorem integral_tsum_lattice_add_of_integrable {E d : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype d]
    (b : Basis d ℝ E) (μ : Measure E) [Measure.IsAddHaarMeasure μ] (f : E → ℂ)
    (hf : Integrable f μ) :
    (∫ x in ZSpan.fundamentalDomain b,
      ∑' z : Submodule.span ℤ (Set.range b), f ((z : E) + x) ∂μ) = ∫ x, f x ∂μ := by
  apply integral_tsum_lattice_add b μ f hf
  · intro z
    exact ((measurePreserving_add_left μ (z : E)).integrable_comp_of_integrable hf).integrableOn
  · exact summable_integral_norm_lattice_add b μ f hf

end Rigidity.Smoothing
