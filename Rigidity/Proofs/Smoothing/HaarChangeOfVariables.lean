import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Linear changes of variables and Haar measure

A linear equivalence between finite-dimensional real normed spaces changes Gaussian Fourier
integrals by a positive constant. The measure comparison is the change-of-basis step used in the
lattice Gaussian argument of Micciancio and Regev, *Worst-case to average-case reductions based on
Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 2.9.
-/

open MeasureTheory MeasureTheory.Measure

namespace Rigidity.Smoothing

/-- A linear change of variables multiplies integrals by a positive constant. -/
theorem exists_integral_comp_linearEquiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μE : Measure E) (μF : Measure F)
    [IsAddHaarMeasure μE] [IsAddHaarMeasure μF] (e : E ≃ₗ[ℝ] F) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : F → ℂ, Continuous f →
      (∫ x : E, f (e x) ∂μE) = c • ∫ y : F, f y ∂μF := by
  let μ : Measure F := Measure.map e μE
  letI : IsAddHaarMeasure μ := Measure.MapLinearEquiv.isAddHaarMeasure μE e
  let c : NNReal := μ.addHaarScalarFactor μF
  refine ⟨c, ?_, ?_⟩
  · exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ μF
  · intro f hf
    have he : Measurable e := e.toLinearMap.continuous_of_finiteDimensional.measurable
    calc
      (∫ x : E, f (e x) ∂μE) = ∫ y : F, f y ∂μ :=
        (integral_map_of_stronglyMeasurable he hf.stronglyMeasurable).symm
      _ = (c : ℝ) • ∫ y : F, f y ∂μF := by
        rw [Measure.isAddLeftInvariant_eq_smul μ μF,
          integral_smul_nnreal_measure]
        rfl

end Rigidity.Smoothing
