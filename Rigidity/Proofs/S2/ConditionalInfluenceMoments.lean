import Rigidity.Proofs.S2.PlanarDensityEncodingTransfer
import Rigidity.Proofs.S2.ConditionalEnergyMoments

/-!
# Moments of averaged planar influences

Conditional averaging preserves the quantitative moment bounds for the resampling energy.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- The averaged planar influence sum is measurable. -/
theorem measurable_planarConditionalInfluenceEnergy (p : unitInterval) (m : ℕ) (k : Vertex 2) :
    Measurable (planarConditionalInfluenceEnergy p m k) := by
  apply Measurable.tsum
  intro e
  have hF := measurable_infiniteClusterCount_triadicCube m k
  have hRes := (measurePreserving_resampleBond 2 p e).measurable
  have hm := (((hF.comp measurable_fst).div_const ((triadicCube 2 m k).ncard : ℝ)).sub
    ((hF.comp hRes).div_const ((triadicCube 2 m k).ncard : ℝ))).abs.pow_const 2
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- The averaged planar influence sum has quantitative inverse-volume moment bounds. -/
theorem planar_conditional_influence_energy_moments (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (m : ℕ) (k : Vertex 2),
      MemLp (planarConditionalInfluenceEnergy p m k) r (latticeBondLaw 2 p) ∧
      lpNorm (planarConditionalInfluenceEnergy p m k) r (latticeBondLaw 2 p) ≤
        C * (r : ℝ) ^ 12 / (((3 ^ m : ℕ) : ℝ) ^ 2) := by
  obtain ⟨C, hC, hmom⟩ := planar_conditional_density_energy_moments p hp
  obtain ⟨D, hD, henergy⟩ := planar_normalized_density_energy_moments p hp
  refine ⟨C, hC, fun r hr m k => ?_⟩
  let μ := latticeBondLaw 2 p
  let P := μ.prod μ
  let X := planarDensityResamplingEnergy m k
  let W := planarConditionalInfluenceEnergy p m k
  let A : MeasurableSpace (Configuration 2 × Configuration 2) :=
    MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (Configuration 2))
  letI : MeasurableSpace (Configuration 2 × Configuration 2) := Prod.instMeasurableSpace
  let Y := MeasureTheory.condExp A P X
  have hXm : Measurable X := by
    dsimp only [X, planarDensityResamplingEnergy]
    apply Measurable.tsum
    intro e
    have hF := measurable_infiniteClusterCount_triadicCube m k
    have hRes := (measurePreserving_resampleBond 2 p e).measurable
    exact (((hF.comp measurable_fst).div_const _).sub
      ((hF.comp hRes).div_const _)).abs.pow_const 2
  have hXi : Integrable X P := by
    have h := (henergy 1 (by norm_num) m k).2.1
    have h' : MemLp X ((1 : ℕ) : ℝ≥0∞) P := h
    exact memLp_one_iff_integrable.mp (by simpa using h')
  have hWm : Measurable W := measurable_planarConditionalInfluenceEnergy p m k
  have hYeq : (fun q : Configuration 2 × Configuration 2 => W q.1) =ᵐ[P] Y := by
    have heq := condExp_first_eq_integral μ μ X hXi hXm.stronglyMeasurable
    have hs := (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (planar_integrated_density_energy_series p hp m k)
    filter_upwards [heq, hs] with q hq hs'
    calc
      W q.1 = ∫ η, X (q.1, η) ∂μ := hs'.2.2.symm
      _ = Y q := hq
  obtain ⟨hYm, hYnorm⟩ := hmom r hr m k A
  have hWprod : MemLp (W ∘ Prod.fst) r P := by
    refine ⟨hYm.1.congr hYeq.symm, ?_⟩
    change eLpNorm (fun q : Configuration 2 × Configuration 2 => W q.1) r P < ⊤
    rw [eLpNorm_congr_ae hYeq]
    exact hYm.2
  have hWmem : MemLp W r μ := by
    have hmap : AEStronglyMeasurable W (Measure.map Prod.fst P) := by
      rw [(measurePreserving_fst (μ := μ) (ν := μ)).map_eq]
      exact hWm.aestronglyMeasurable
    have h := (memLp_map_measure_iff hmap measurable_fst.aemeasurable).2 hWprod
    rwa [(measurePreserving_fst (μ := μ) (ν := μ)).map_eq] at h
  have hNorm : lpNorm W r μ = lpNorm Y r P := by
    rw [← toReal_eLpNorm hWm.aestronglyMeasurable,
      ← toReal_eLpNorm hYm.aestronglyMeasurable]
    have hnormeq : eLpNorm (W ∘ Prod.fst) r P = eLpNorm Y r P :=
      eLpNorm_congr_ae hYeq
    rw [← eLpNorm_comp_measurePreserving hWm.aestronglyMeasurable
      (measurePreserving_fst (μ := μ) (ν := μ)), hnormeq]
  exact ⟨hWmem, hNorm.trans_le hYnorm⟩

end Rigidity.Proofs.S2
