import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integrating nonnegative series

A finite integral of a nonnegative series yields summability of the individual integrals and
permits exchanging the integral and the sum.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory
open scoped ENNReal

/-- A nonnegative measurable series with finite extended integral may be integrated termwise. -/
theorem integral_tsum_nonnegative {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) (f : ι → α → ℝ) (hf : ∀ i, Measurable (f i))
    (hpos : ∀ i x, 0 ≤ f i x)
    (hfinite : (∫⁻ x, ∑' i, ENNReal.ofReal (f i x) ∂μ) < ∞) :
    (∀ i, Integrable (f i) μ) ∧ Summable (fun i => ∫ x, f i x ∂μ) ∧
      (∫ x, ∑' i, f i x ∂μ) = ∑' i, ∫ x, f i x ∂μ := by
  have hsum : (∑' i, ∫⁻ x, ENNReal.ofReal (f i x) ∂μ) ≠ ∞ := by
    rw [← lintegral_tsum (fun i => (hf i).ennreal_ofReal.aemeasurable)]
    exact hfinite.ne
  have hfi (i : ι) : (∫⁻ x, ENNReal.ofReal (f i x) ∂μ) < ∞ :=
    lt_of_le_of_lt (ENNReal.le_tsum i) (lt_top_iff_ne_top.mpr hsum)
  have hint (i : ι) : Integrable (f i) μ := by
    refine ⟨(hf i).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simpa only [Real.enorm_of_nonneg (hpos i _)] using hfi i
  have hInt (i : ι) : (∫ x, f i x ∂μ) = (∫⁻ x, ENNReal.ofReal (f i x) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (hpos i))
      (hf i).aestronglyMeasurable
  refine ⟨hint, ?_, ?_⟩
  · simpa only [hInt] using ENNReal.summable_toReal hsum
  · apply integral_tsum (fun i => (hf i).aestronglyMeasurable)
    simpa only [Real.enorm_of_nonneg (hpos _ _)] using hsum

end Rigidity.Proofs.S2
