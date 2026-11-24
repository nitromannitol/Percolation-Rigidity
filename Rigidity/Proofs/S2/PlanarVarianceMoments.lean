import PercolationClusterHomogenization.Proofs.Density.ConditionalInfluenceMoments
import Rigidity.Proofs.S2.PlanarConditionalVarianceMoment

/-!
# Moment bounds for planar conditional variance

The conditional variance sum inherits the quantitative inverse-volume moment bounds of the
averaged resampling energy.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- The planar conditional variance has `Lʳ` norm at most `C r¹² 3⁻²ᵐ`. -/
theorem planar_density_conditional_variance_moments (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (m : ℕ) (k : Vertex 2),
      let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
      MemLp (planarDensityConditionalVariance p m k) r P ∧
      lpNorm (planarDensityConditionalVariance p m k) r P ≤
        C * (r : ℝ) ^ 12 / (((3 ^ m : ℕ) : ℝ) ^ 2) := by
  obtain ⟨C, hC, hmom⟩ := planar_conditional_influence_energy_moments p hp
  refine ⟨C, hC, fun r hr m k => ?_⟩
  let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
  let μ := latticeBondLaw 2 p
  let T := bernoulliRealConfiguration (d := 2)
  let X := planarDensityRealObservable p m k
  let V := planarDensityConditionalVariance p m k
  let W := planarConditionalInfluenceEnergy p m k
  have hT : MeasurePreserving T P μ := measurePreserving_bernoulliRealConfiguration 2 p
  have hXm : Measurable X := (planar_density_real_observable_properties p m k).1
  have hVm : Measurable V := by
    dsimp only [V, planarDensityConditionalVariance]
    apply Measurable.tsum
    intro e
    have hc : Measurable (MeasureTheory.condExp (coordAlg ({e}ᶜ : Set (Bond 2))) P X) :=
      (stronglyMeasurable_condExp.mono (coordAlg_le _)).measurable
    exact (hXm.sub hc).pow_const 2
  have hWm : Measurable W := measurable_planarConditionalInfluenceEnergy p m k
  obtain ⟨hWmem, hWnorm⟩ := hmom r hr m k
  have hWTmem : MemLp (W ∘ T) r P := by
    have h : MemLp W r (Measure.map T P) := by rw [hT.map_eq]; exact hWmem
    exact h.comp_of_map hT.measurable.aemeasurable
  have hV0 (ω : Bond 2 → ℝ) : 0 ≤ V ω := tsum_nonneg fun _ => sq_nonneg _
  have hdom : ∀ᵐ ω ∂P, ‖V ω‖ ≤ (W ∘ T) ω := by
    filter_upwards [planar_density_conditional_variance_le_energy p hp m k] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hV0 ω)]
    exact hω.2
  have hVmem : MemLp V r P := hWTmem.mono' hVm.aestronglyMeasurable hdom
  have hnorm : lpNorm V r P ≤ lpNorm W r μ := by
    rw [← toReal_eLpNorm hVm.aestronglyMeasurable,
      ← toReal_eLpNorm hWm.aestronglyMeasurable,
      ← eLpNorm_comp_measurePreserving hWm.aestronglyMeasurable hT]
    exact ENNReal.toReal_mono hWTmem.2.ne (eLpNorm_mono_ae_real hdom)
  exact ⟨hVmem, hnorm.trans hWnorm⟩

end Rigidity.Proofs.S2
