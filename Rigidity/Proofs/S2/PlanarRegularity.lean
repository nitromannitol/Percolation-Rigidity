import Rigidity.External.PlanarInputs
import Rigidity.Proofs.S2.ArmstrongDarioTranslation

/-!
# Planar order-one regularity at every centre

Stationarity transports the origin estimate and the qualitative corrector classification gives
the regularity scale used for Green-function homogenization.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.Steps.S2
open Rigidity.External (IsOsBond ArmstrongDarioOrderOneOriginTwo SupercriticalBondCorrectorInputTwo)

/-- The regularity-scale step follows from the planar origin and corrector estimates. -/
theorem regularityScaleStep_two_of_origin (p : unitInterval)
    (hAD : ArmstrongDarioOrderOneOriginTwo) (hCorr : SupercriticalBondCorrectorInputTwo) :
    RegularityScaleStep 2 p := by
  intro hp hp1
  obtain ⟨s, C₀, hs, hC₀, X, hXm, hX0, hXO, C, hAE⟩ := hAD p hp hp1
  have hcl := hCorr p hp hp1
  refine ⟨s, max C₀ C, hs, lt_max_of_lt_left hC₀, fun x => ?_⟩
  have hmp := measurePreserving_configurationTranslation p (-x)
  have hYm : Measurable (fun ω => X (configurationTranslation (-x) ω)) :=
    hXm.comp (configurationTranslationMeasurableEquiv (-x)).measurable
  have hYO : IsOsBond 2 p (fun ω => X (configurationTranslation (-x) ω)) s C₀ := by
    refine ⟨hmp.integrable_comp_of_integrable hXO.1, ?_⟩
    have he := hmp.integral_comp (configurationTranslationMeasurableEquiv (-x)).measurableEmbedding
      (fun ω => Real.exp (Real.rpow (max (X ω / C₀) 0) s))
    exact he.trans_le hXO.2
  refine ⟨fun ω => X (configurationTranslation (-x) ω), hYm, fun ω => hX0 _,
    IsOsBond.mono_scale hs hC₀ (le_max_left _ _) hYm hYO, ?_⟩
  filter_upwards [hmp.quasiMeasurePreserving.ae hAE, hmp.quasiMeasurePreserving.ae hcl, hcl]
    with ω hω hcω hUω
  intro h ℓ hℓ R hR u hu
  have ht := (hasUniqueInfiniteOpenComponent_translation_iff (-x) ω).mpr h
  obtain ⟨φ, hφ, hest⟩ := orderOne_approximation_translation x h
    (X (configurationTranslation (-x) ω)) C
    (fun φ hφ => ((hcω ht).2 φ hφ).exists) (hω ht) R hR u hu
  obtain ⟨ξ, a, hξ⟩ := exists_eq_sum_correctedPlane (hUω h).1 (hUω h).2 hℓ hφ
  have huφ : u - φ = fun z => u z - ∑ i, ξ i * ℓ i z - a :=
    funext fun z => by rw [Pi.sub_apply, hξ z, sub_sub]
  refine ⟨ξ, a, fun r hr hrR => ?_⟩
  rw [← huφ]
  exact (hest r hr hrR).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
    (componentBallL2_nonneg _ _ _ _))

end Rigidity.Proofs.S2
