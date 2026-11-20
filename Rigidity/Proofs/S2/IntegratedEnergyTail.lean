import Rigidity.Proofs.S2.ConditionalEnergyStochasticBound
import Rigidity.Proofs.S2.ConditionalProductIntegral

/-!
# Integrated planar resampling energy

Averaging the resampling energy over the independent configuration preserves its
inverse-volume stretched-exponential tail.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- The second-copy average of the planar resampling energy has an inverse-volume tail. -/
theorem planar_integrated_density_energy_osBound (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex 2),
      LatticeProb.OsBound (latticeBondLaw 2 p) (1 / 12 : ℝ)
        (C / (((3 ^ m : ℕ) : ℝ) ^ 2))
        (fun ω => ∫ η, planarDensityResamplingEnergy m k (ω, η) ∂(latticeBondLaw 2 p)) := by
  obtain ⟨C, hC, htail⟩ := planar_conditional_density_energy_osBound p hp
  obtain ⟨D, hD, hmoment⟩ := planar_normalized_density_energy_moments p hp
  refine ⟨C, hC, fun m k => ?_⟩
  let μ := latticeBondLaw 2 p
  let X := planarDensityResamplingEnergy m k
  let g (ω : Configuration 2) := ∫ η, X (ω, η) ∂μ
  let 𝓜 : MeasurableSpace (Configuration 2 × Configuration 2) := MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (Configuration 2))
  letI : MeasurableSpace (Configuration 2 × Configuration 2) := Prod.instMeasurableSpace
  have hXm : Measurable X := by
    dsimp only [X, planarDensityResamplingEnergy]
    apply Measurable.tsum
    intro e
    have hF := measurable_infiniteClusterCount_triadicCube m k
    have hRes := (measurePreserving_resampleBond 2 p e).measurable
    exact (((hF.comp measurable_fst).div_const _).sub
      ((hF.comp hRes).div_const _)).abs.pow_const 2
  have hXi : Integrable X (μ.prod μ) := by
    have h := (hmoment 1 (by norm_num) m k).2.1
    have h' : MemLp X ((1 : ℕ) : ℝ≥0∞) (μ.prod μ) := h
    exact memLp_one_iff_integrable.mp (by simpa using h')
  have hg : Measurable g := hXm.stronglyMeasurable.integral_prod_right'.measurable
  have heq : (fun q : Configuration 2 × Configuration 2 => g q.1) =ᵐ[μ.prod μ]
      MeasureTheory.condExp 𝓜 (μ.prod μ) X :=
    condExp_first_eq_integral μ μ X hXi hXm.stronglyMeasurable
  intro t ht
  have hmeasure : μ {ω | t * (C / (((3 ^ m : ℕ) : ℝ) ^ 2)) < max (g ω) 0} =
      (μ.prod μ) {q | t * (C / (((3 ^ m : ℕ) : ℝ) ^ 2)) < max (g q.1) 0} := by
    symm
    exact (measurePreserving_fst (μ := μ) (ν := μ)).measure_preimage
      (measurableSet_lt measurable_const (hg.max measurable_const)).nullMeasurableSet
  rw [hmeasure]
  have hcompare : (μ.prod μ) {q | t * (C / (((3 ^ m : ℕ) : ℝ) ^ 2)) < max (g q.1) 0} ≤
      (μ.prod μ) {q | t * (C / (((3 ^ m : ℕ) : ℝ) ^ 2)) <
        max |MeasureTheory.condExp 𝓜 (μ.prod μ) X q| 0} := by
    apply measure_mono_ae
    filter_upwards [heq] with q hq hqmem
    change t * (C / (((3 ^ m : ℕ) : ℝ) ^ 2)) < max (g q.1) 0 at hqmem
    change t * (C / (((3 ^ m : ℕ) : ℝ) ^ 2)) <
      max |MeasureTheory.condExp 𝓜 (μ.prod μ) X q| 0
    rw [hq] at hqmem
    exact hqmem.trans_le (max_le_max (le_abs_self _) le_rfl)
  exact hcompare.trans (htail m k 𝓜 t ht)

end Rigidity.Proofs.S2
