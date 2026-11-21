import Rigidity.Proofs.S2.IntegratedEnergyTail
import Rigidity.Proofs.S2.NonnegativeIntegralSeries
import Rigidity.Proofs.S2.NormalizedInfluenceEnergy

/-!
# Summing conditional planar resampling influences

The average energy is the convergent sum of its single-bond averages almost surely.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- Individual bond influences are integrable in the independent copy, and their integrals
sum to the averaged resampling energy almost surely. -/
theorem planar_integrated_density_energy_series (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) (m : ℕ) (k : Vertex 2) :
    ∀ᵐ ω ∂(latticeBondLaw 2 p),
      (∀ e : Bond 2, Integrable (fun η : Configuration 2 =>
        |(infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
              ((triadicCube 2 m k).ncard : ℝ) -
            (infiniteClusterCount (triadicCube 2 m k) (resampleBond ω η e) : ℝ) /
              ((triadicCube 2 m k).ncard : ℝ)| ^ 2) (latticeBondLaw 2 p)) ∧
      Summable (fun e : Bond 2 => ∫ η : Configuration 2,
        |(infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
              ((triadicCube 2 m k).ncard : ℝ) -
            (infiniteClusterCount (triadicCube 2 m k) (resampleBond ω η e) : ℝ) /
              ((triadicCube 2 m k).ncard : ℝ)| ^ 2 ∂(latticeBondLaw 2 p)) ∧
      (∫ η, planarDensityResamplingEnergy m k (ω, η) ∂(latticeBondLaw 2 p)) =
        ∑' e : Bond 2, ∫ η : Configuration 2,
          |(infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ) -
              (infiniteClusterCount (triadicCube 2 m k) (resampleBond ω η e) : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ)| ^ 2 ∂(latticeBondLaw 2 p) := by
  let μ := latticeBondLaw 2 p
  let F (e : Bond 2) (q : Configuration 2 × Configuration 2) : ℝ :=
    |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ) -
      (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ)| ^ 2
  let G (q : Configuration 2 × Configuration 2) : ℝ≥0∞ := ∑' e, ENNReal.ofReal (F e q)
  have hFm (e : Bond 2) : Measurable (F e) := by
    dsimp only [F]
    have hF := measurable_infiniteClusterCount_triadicCube m k
    have hRes := (measurePreserving_resampleBond 2 p e).measurable
    exact (((hF.comp measurable_fst).div_const _).sub
      ((hF.comp hRes).div_const _)).abs.pow_const 2
  have hGm : Measurable G := Measurable.tsum fun e => (hFm e).ennreal_ofReal
  obtain ⟨C, hC, hmean⟩ := planar_normalized_density_resampling_energy_mean p hp
  have hfinite : (∫⁻ q, G q ∂(μ.prod μ)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((hmean m k).1)
  have hslice : (∫⁻ ω, ∫⁻ η, G (ω, η) ∂μ ∂μ) ≠ ∞ := by
    rw [← lintegral_prod G hGm.aemeasurable]
    exact hfinite
  filter_upwards [ae_lt_top (hGm.lintegral_prod_right') hslice] with ω hω
  have hseries := integral_tsum_nonnegative μ (fun e η => F e (ω, η))
    (fun e => (hFm e).comp (measurable_const.prodMk measurable_id))
    (fun e η => sq_nonneg _) hω
  simpa only [F, G, planarDensityResamplingEnergy] using hseries

end Rigidity.Proofs.S2

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External

/-- The sum of the individual conditional resampling influences has an inverse-volume tail. -/
theorem planar_conditional_influence_sum_osBound (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex 2),
      (∀ᵐ ω ∂(latticeBondLaw 2 p), Summable (fun e : Bond 2 =>
        ∫ η : Configuration 2,
          |(infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ) -
              (infiniteClusterCount (triadicCube 2 m k) (resampleBond ω η e) : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ)| ^ 2 ∂(latticeBondLaw 2 p))) ∧
      LatticeProb.OsBound (latticeBondLaw 2 p) (1 / 14 : ℝ)
        (C / (((3 ^ m : ℕ) : ℝ) ^ 2))
        (fun ω => ∑' e : Bond 2, ∫ η : Configuration 2,
          |(infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ) -
              (infiniteClusterCount (triadicCube 2 m k) (resampleBond ω η e) : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ)| ^ 2 ∂(latticeBondLaw 2 p)) := by
  obtain ⟨C, hC, htail⟩ := planar_integrated_density_energy_osBound p hp
  refine ⟨C, hC, fun m k => ?_⟩
  have hseries := planar_integrated_density_energy_series p hp m k
  refine ⟨hseries.mono (fun _ h => h.2.1), ?_⟩
  have htail' := (htail m k).of_exponent_le (show (1 / 14 : ℝ) ≤ 1 / 12 by norm_num)
  intro t ht
  have hEq : {ω : Configuration 2 | t * (C / (((3 ^ m : ℕ) : ℝ) ^ 2)) <
      max (∑' e : Bond 2, ∫ η : Configuration 2,
        |(infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
              ((triadicCube 2 m k).ncard : ℝ) -
            (infiniteClusterCount (triadicCube 2 m k) (resampleBond ω η e) : ℝ) /
              ((triadicCube 2 m k).ncard : ℝ)| ^ 2 ∂(latticeBondLaw 2 p)) 0} =ᵐ[latticeBondLaw 2 p]
      {ω : Configuration 2 | t * (C / (((3 ^ m : ℕ) : ℝ) ^ 2)) <
        max (∫ η, planarDensityResamplingEnergy m k (ω, η) ∂(latticeBondLaw 2 p)) 0} := by
    filter_upwards [hseries] with ω hω
    apply propext
    change (t * (C / (((3 ^ m : ℕ) : ℝ) ^ 2)) <
      max (∑' e : Bond 2, ∫ η : Configuration 2,
        |(infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
              ((triadicCube 2 m k).ncard : ℝ) -
            (infiniteClusterCount (triadicCube 2 m k) (resampleBond ω η e) : ℝ) /
              ((triadicCube 2 m k).ncard : ℝ)| ^ 2 ∂(latticeBondLaw 2 p)) 0) ↔
      (t * (C / (((3 ^ m : ℕ) : ℝ) ^ 2)) <
        max (∫ η, planarDensityResamplingEnergy m k (ω, η) ∂(latticeBondLaw 2 p)) 0)
    rw [hω.2.2]
  rw [measure_congr hEq]
  exact htail' t ht

end Rigidity.Proofs.S2
