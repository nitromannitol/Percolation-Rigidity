import Rigidity.Proofs.Smoothing.HaarChangeOfVariables

/-!
# Integrability under linear changes of variables

An integrable function remains integrable after a finite-dimensional linear change of variables.
This is used in the Gaussian Fourier integral of Micciancio and Regev, *Worst-case to average-case
reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 2.9.
-/

open MeasureTheory MeasureTheory.Measure

namespace Rigidity.Smoothing

/-- Integrability is preserved by a finite-dimensional linear equivalence. -/
theorem integrable_comp_linearEquiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μE : Measure E) (μF : Measure F)
    [IsAddHaarMeasure μE] [IsAddHaarMeasure μF] (e : E ≃ₗ[ℝ] F) {f : F → ℂ}
    (hf : Integrable f μF) : Integrable (fun x => f (e x)) μE := by
  let μ : Measure F := Measure.map e μE
  letI : IsAddHaarMeasure μ := Measure.MapLinearEquiv.isAddHaarMeasure μE e
  have hmap : Integrable f μ := by
    rw [Measure.isAddLeftInvariant_eq_smul μ μF]
    exact hf.smul_measure_nnreal
  exact hmap.comp_measurable e.toLinearMap.continuous_of_finiteDimensional.measurable

end Rigidity.Smoothing
