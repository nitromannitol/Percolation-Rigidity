import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Conditioning a product integral on its first coordinate

On a product of probability spaces, integrating the second coordinate gives a version of the
conditional expectation given the first coordinate.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory

/-- Conditional expectation onto the first-coordinate σ-algebra is integration over the second
factor. -/
theorem condExp_first_eq_integral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → ℝ) (hf : Integrable f (μ.prod ν)) (hfm : StronglyMeasurable f) :
    (fun z => ∫ y, f (z.1, y) ∂ν) =ᵐ[μ.prod ν]
      MeasureTheory.condExp (MeasurableSpace.comap Prod.fst ‹MeasurableSpace α›) (μ.prod ν) f := by
  let 𝓜 : MeasurableSpace (α × β) := MeasurableSpace.comap Prod.fst ‹MeasurableSpace α›
  have hle : 𝓜 ≤ (Prod.instMeasurableSpace : MeasurableSpace (α × β)) := measurable_fst.comap_le
  let g : α → ℝ := fun x => ∫ y, f (x, y) ∂ν
  have hg : Integrable g μ := hf.integral_prod_left
  have hgprod : Integrable (g ∘ Prod.fst) (μ.prod ν) :=
    ((memLp_one_iff_integrable.mpr hg).comp_fst ν).integrable le_rfl
  have hgm : StronglyMeasurable[𝓜] (g ∘ Prod.fst) := by
    apply hfm.integral_prod_right'.comp_measurable
    exact comap_measurable Prod.fst
  apply ae_eq_condExp_of_forall_setIntegral_eq hle hf
  · exact fun s _ _ => hgprod.integrableOn
  · intro s hs _
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    change (∫ z in Prod.fst ⁻¹' t, g z.1 ∂μ.prod ν) = _
    rw [show Prod.fst ⁻¹' t = t ×ˢ Set.univ by ext z; simp]
    rw [← Measure.prod_restrict, Measure.restrict_univ]
    have hgrest : Integrable (fun z : α × β => g z.1) ((μ.restrict t).prod ν) := by
      rw [Measure.restrict_prod_eq_prod_univ]
      exact hgprod.restrict
    have hfrest : Integrable f ((μ.restrict t).prod ν) := by
      rw [Measure.restrict_prod_eq_prod_univ]
      exact hf.restrict
    rw [integral_prod _ hgrest, integral_prod _ hfrest]
    simp [g]
  · exact hgm.aestronglyMeasurable

end Rigidity.Proofs.S2
